#!/usr/bin/env python3
"""Sports Live Analyzer — Backend v5 | Leon.ru + Sofascore | TT·Football·Hockey·Tennis"""

import json, os, re as _re, ssl, time, threading, webbrowser
import urllib.request, urllib.parse, urllib.error
from http.server import HTTPServer, SimpleHTTPRequestHandler
from concurrent.futures import ThreadPoolExecutor, as_completed

PORT      = int(os.environ.get('PORT', 8080))
CACHE_TTL = 20

SPORTS  = ['tt', 'football', 'hockey', 'tennis']
_caches = {s: {'events': [], 'ts': 0, 'source': ''} for s in SPORTS}
_lock   = threading.Lock()

_PLAYER_CACHE = {}
_PLAYER_LOCK  = threading.Lock()
PLAYER_TTL    = 3600 * 6  # 6 hours

SSL_CTX = ssl.create_default_context()
SSL_CTX.check_hostname = False
SSL_CTX.verify_mode    = ssl.CERT_NONE

LEON_HEADERS = {
    'User-Agent': ('Mozilla/5.0 (Windows NT 10.0; Win64; x64) '
                   'AppleWebKit/537.36 (KHTML, like Gecko) '
                   'Chrome/124.0.0.0 Safari/537.36'),
    'Accept':          'application/json, text/plain, */*',
    'Accept-Language': 'ru-RU,ru;q=0.9,en;q=0.8',
    'Referer':         'https://leon.ru/',
}

SOFA_HEADERS = {
    'User-Agent': ('Mozilla/5.0 (Windows NT 10.0; Win64; x64) '
                   'AppleWebKit/537.36 (KHTML, like Gecko) '
                   'Chrome/124.0.0.0 Safari/537.36'),
    'Accept':          'application/json',
    'Accept-Language': 'ru-RU,ru;q=0.9,en;q=0.8',
    'Referer':         'https://www.sofascore.com/',
    'Origin':          'https://www.sofascore.com',
}

# ТТ — охватываем ВСЕ лиги Леона
TT_QUERIES = [
    'Setka', 'Table+Tennis', 'Настольный', 'TTL', 'Ping+Pong', 'WTT',
    'TT+Cup', 'Pro+TT', 'TT+Star', 'Liga+Pro', 'InPlay+TT',
    'Butterfly', 'UTT', 'ITTF', 'pingpong',
    'TT+League', 'TT+Series', 'TT+Tour', 'Virtual+TT',
]

SPORT_QUERIES = {
    'tt':       TT_QUERIES,
    'football': ['Футбол', 'Champions+League', 'Europa+League', 'Conference+League',
                 'Premier+League', 'La+Liga', 'Bundesliga', 'Serie+A', 'Ligue+1',
                 'Eredivisie', 'РПЛ', 'MLS', 'Liga+MX', 'Brasileirao'],
    'hockey':   ['Хоккей', 'КХЛ', 'NHL', 'SHL', 'Liiga', 'DEL', 'AHL'],
    'tennis':   ['Теннис', 'ATP', 'WTA', 'ITF', 'Roland+Garros', 'Wimbledon'],
}

_HOCKEY_KW = ['хоккей', 'hockey', 'кхл', 'nhl', 'shl', 'liiga', 'del ', 'ahl', 'нхл']
_BIGTEN_KW = ['atp', 'wta', 'itf', 'roland garros', 'wimbledon', 'us open',
              'australian open', 'challenger', 'davis cup', 'fed cup']


def get_json(url, timeout=12):
    req = urllib.request.Request(url, headers=LEON_HEADERS)
    with urllib.request.urlopen(req, context=SSL_CTX, timeout=timeout) as r:
        return json.loads(r.read().decode('utf-8'))


def sofa_json(url, timeout=8):
    req = urllib.request.Request(url, headers=SOFA_HEADERS)
    with urllib.request.urlopen(req, context=SSL_CTX, timeout=timeout) as r:
        return json.loads(r.read().decode('utf-8'))


# ── Sofascore Player History ─────────────────────────────────────────────────

def _search_player_sofa(name):
    """Search sofascore for player by name, return player id or None."""
    q = urllib.parse.quote(name.strip())
    data = sofa_json(f'https://api.sofascore.com/api/v1/search/all/?q={q}&page=0')
    players = data.get('players', [])
    # Prefer table tennis players
    for item in players:
        p = item.get('player', {})
        sport_slug = (p.get('sport') or {}).get('slug', '')
        sport_name = (p.get('sport') or {}).get('name', '').lower()
        if 'table' in sport_name or 'настольный' in sport_name or sport_slug == 'table-tennis':
            return p['id']
    # Fallback: first player result
    if players:
        return players[0].get('player', {}).get('id')
    return None


def _get_player_events_sofa(player_id):
    """Fetch last ~40 matches for a player from sofascore (2 pages)."""
    all_events = []
    for page in range(2):
        try:
            data = sofa_json(f'https://api.sofascore.com/api/v1/player/{player_id}/events/last/{page}')
            events = data.get('events', [])
            if not events:
                break
            all_events.extend(events)
        except Exception:
            break
    return all_events


def _compute_player_stats(events, player_id):
    """Compute winRate, form (last 5), avgSetMargin from events."""
    wins = 0
    total = 0
    form = []
    margins = []
    for ev in events[:25]:
        home_id = (ev.get('homeTeam') or {}).get('id')
        away_id = (ev.get('awayTeam') or {}).get('id')
        wc = ev.get('winnerCode')
        if wc not in (1, 2):
            continue
        is_home = (home_id == player_id)
        is_away = (away_id == player_id)
        if not is_home and not is_away:
            continue
        player_won = (is_home and wc == 1) or (is_away and wc == 2)
        h_sets = (ev.get('homeScore') or {}).get('current', 0) or 0
        a_sets = (ev.get('awayScore') or {}).get('current', 0) or 0
        if h_sets + a_sets > 0:
            margins.append(abs(h_sets - a_sets))
        total += 1
        wins += 1 if player_won else 0
        form.append('W' if player_won else 'L')
    return {
        'winRate':      round(wins / total, 3) if total else 0.5,
        'matches':      total,
        'wins':         wins,
        'form':         form[:5],
        'avgSetMargin': round(sum(margins) / len(margins), 2) if margins else 0.0,
    }


# ── Self-built player database (accumulates from Leon match results) ──────────
# Stored in memory; grows as matches complete. Survives server restarts via PLAYER_DB.

PLAYER_DB   = {}   # {norm_name: {wins, losses, sets_won, sets_lost, recent:[W/L], opp:{name:[w,l]}}}
_DB_LOCK    = threading.Lock()

# Groq AI (free, https://console.groq.com → free API key → Render env var GROQ_API_KEY)
GROQ_API_KEY = os.environ.get('GROQ_API_KEY', '')
_AI_CACHE    = {}   # {key: {data, ts}}
AI_CACHE_TTL = 90   # seconds


def _norm(name):
    return _re.sub(r'\s+', ' ', name.strip().lower())


def record_tt_result(home_name, away_name, home_sets, away_sets):
    """Record a finished TT match result into PLAYER_DB."""
    hn, an = _norm(home_name), _norm(away_name)
    if not hn or not an or home_sets + away_sets < 2:
        return
    home_won = home_sets > away_sets
    with _DB_LOCK:
        for nm, won, sw, sl, opp in [
            (hn, home_won,  home_sets, away_sets, an),
            (an, not home_won, away_sets, home_sets, hn),
        ]:
            if nm not in PLAYER_DB:
                PLAYER_DB[nm] = {'wins': 0, 'losses': 0, 'sets_won': 0, 'sets_lost': 0, 'recent': [], 'opp': {}}
            d = PLAYER_DB[nm]
            d['wins']     += 1 if won else 0
            d['losses']   += 0 if won else 1
            d['sets_won']  += sw
            d['sets_lost'] += sl
            d['recent']    = (['W' if won else 'L'] + d['recent'])[:20]
            if opp not in d['opp']: d['opp'][opp] = [0, 0]
            d['opp'][opp][0 if won else 1] += 1


def _db_stats(name):
    d = PLAYER_DB.get(_norm(name))
    if not d:
        return None
    total = d['wins'] + d['losses']
    if total == 0:
        return None
    return {
        'winRate':      round(d['wins'] / total, 3),
        'matches':      total,
        'wins':         d['wins'],
        'form':         d['recent'][:5],
        'avgSetMargin': round((d['sets_won'] - d['sets_lost']) / total, 2),
        'source':       'leon',
    }


def get_local_player_stats(p1_name, p2_name):
    """Stats from our self-built database (Leon results)."""
    p1 = _db_stats(p1_name)
    p2 = _db_stats(p2_name)
    h2h = None
    hn, an = _norm(p1_name), _norm(p2_name)
    d = PLAYER_DB.get(hn, {})
    opp = d.get('opp', {}).get(an)
    if opp and sum(opp) > 0:
        h2h = {'p1Wins': opp[0], 'p2Wins': opp[1], 'total': sum(opp)}
    return {'p1': p1, 'p2': p2, 'h2h': h2h, 'source': 'leon-local', 'dbSize': len(PLAYER_DB)}


# ── Groq AI + rule-based analysis ─────────────────────────────────────────────

def _groq_chat(prompt, max_tokens=200):
    payload = json.dumps({
        'model': 'llama-3.3-70b-versatile',
        'messages': [{'role': 'user', 'content': prompt}],
        'max_tokens': max_tokens, 'temperature': 0.35,
    }).encode('utf-8')
    req = urllib.request.Request(
        'https://api.groq.com/openai/v1/chat/completions',
        data=payload,
        headers={'Authorization': f'Bearer {GROQ_API_KEY}', 'Content-Type': 'application/json'},
        method='POST',
    )
    with urllib.request.urlopen(req, context=SSL_CTX, timeout=12) as r:
        return json.loads(r.read())['choices'][0]['message']['content'].strip()


def _rule_based_ai(match, stats):
    """Generate natural language analysis without AI."""
    p1, p2, h2h = stats.get('p1'), stats.get('p2'), stats.get('h2h')
    ht, at = match.get('homeTeam', '?'), match.get('awayTeam', '?')
    hs, aws = match.get('homeSets', 0), match.get('awaySets', 0)
    parts = []

    if p1 and p2 and p1.get('matches', 0) >= 3 and p2.get('matches', 0) >= 3:
        wr1, wr2 = int(p1['winRate'] * 100), int(p2['winRate'] * 100)
        diff = wr1 - wr2
        stronger = ht if diff > 0 else at
        if abs(diff) >= 15:
            parts.append(f"{stronger} значительно сильнее ({wr1}% vs {wr2}% побед)")
        elif abs(diff) >= 7:
            parts.append(f"{stronger} чуть сильнее по статистике ({wr1}% vs {wr2}%)")
        else:
            parts.append(f"Игроки примерно равны по статистике ({wr1}% vs {wr2}%)")
        f1 = ''.join(p1.get('form', []))
        f2 = ''.join(p2.get('form', []))
        if f1 or f2:
            parts.append(f"Форма: {ht}: {f1 or '?'} / {at}: {f2 or '?'}")

    if h2h and h2h.get('total', 0) >= 2:
        leader = ht if h2h['p1Wins'] > h2h['p2Wins'] else at
        parts.append(f"Личные встречи: {ht} {h2h['p1Wins']}–{h2h['p2Wins']} {at} (лидирует {leader})")

    if hs > aws:
        parts.append(f"{ht} ведёт по партиям {hs}:{aws}")
    elif aws > hs:
        parts.append(f"{at} ведёт по партиям {hs}:{aws}")

    return ' · '.join(parts) if parts else 'Недостаточно матчей для анализа (база накапливается)'


def get_ai_analysis(event_id, home, away, match_data, stats):
    now = time.time()
    key = f'{event_id}_{home}'
    with _DB_LOCK:
        cached = _AI_CACHE.get(key)
        if cached and now - cached['ts'] < AI_CACHE_TTL:
            return cached['data']

    if GROQ_API_KEY:
        p1 = stats.get('p1') or {}
        p2 = stats.get('p2') or {}
        h2h = stats.get('h2h') or {}
        hs  = match_data.get('homeSets', 0)
        aws = match_data.get('awaySets', 0)
        chp = match_data.get('currentHomePts', 0)
        cap = match_data.get('currentAwayPts', 0)
        prompt = (
            f"Настольный теннис, лайв матч: {home} vs {away}\n"
            f"Счёт по партиям: {hs}:{aws}. Текущая партия: {chp}:{cap}.\n"
            f"Котировки: {home} @ {match_data.get('w1Odds','?')}, {away} @ {match_data.get('w2Odds','?')}.\n"
        )
        if p1.get('matches', 0) >= 3:
            prompt += f"Статистика {home}: {int(p1.get('winRate', 0.5)*100)}% побед за {p1['matches']} матчей, форма: {''.join(p1.get('form',[]))}\n"
        if p2.get('matches', 0) >= 3:
            prompt += f"Статистика {away}: {int(p2.get('winRate', 0.5)*100)}% побед за {p2['matches']} матчей, форма: {''.join(p2.get('form',[]))}\n"
        if h2h.get('total', 0) >= 2:
            prompt += f"Личные встречи: {home} {h2h.get('p1Wins',0)}–{h2h.get('p2Wins',0)} {away}.\n"
        prompt += (
            "\nДай краткий беттинг-анализ (2 предложения, по-русски).\n"
            "Последняя строка СТРОГО в формате:\n"
            "ПРОГНОЗ: [имя игрока], УВЕРЕННОСТЬ: [ВЫСОКАЯ/СРЕДНЯЯ/НИЗКАЯ]"
        )
        try:
            text = _groq_chat(prompt)
            result = {'text': text, 'source': 'Groq · Llama 3.3 70B', 'hasGroq': True}
        except Exception as ex:
            print(f'[groq] {ex}')
            result = {'text': _rule_based_ai(match_data, stats), 'source': 'Правила', 'hasGroq': False}
    else:
        result = {'text': _rule_based_ai(match_data, stats), 'source': 'Правила', 'hasGroq': False}

    with _DB_LOCK:
        _AI_CACHE[key] = {'data': result, 'ts': now}
    return result


def get_player_stats(p1_name, p2_name):
    """Return H2H + recent form for two players. Cached 6h."""
    now = time.time()
    cache_key = (p1_name.lower().strip(), p2_name.lower().strip())
    with _PLAYER_LOCK:
        cached = _PLAYER_CACHE.get(cache_key)
        if cached and now - cached['ts'] < PLAYER_TTL:
            return cached['data']

    result = {'p1': None, 'p2': None, 'h2h': None}
    try:
        p1_id = _search_player_sofa(p1_name)
        p2_id = _search_player_sofa(p2_name)

        if p1_id:
            evs1 = _get_player_events_sofa(p1_id)
            result['p1'] = {'id': p1_id, 'name': p1_name, **_compute_player_stats(evs1, p1_id)}
            # H2H: scan p1 events for matches against p2
            if p2_id:
                h1 = h2 = 0
                for ev in evs1:
                    ht = (ev.get('homeTeam') or {}).get('id')
                    at = (ev.get('awayTeam') or {}).get('id')
                    wc = ev.get('winnerCode')
                    if {ht, at} == {p1_id, p2_id} and wc in (1, 2):
                        p1_home = ht == p1_id
                        if (p1_home and wc == 1) or (not p1_home and wc == 2):
                            h1 += 1
                        else:
                            h2 += 1
                if h1 + h2 > 0:
                    result['h2h'] = {'p1Wins': h1, 'p2Wins': h2, 'total': h1 + h2}

        if p2_id:
            evs2 = _get_player_events_sofa(p2_id)
            result['p2'] = {'id': p2_id, 'name': p2_name, **_compute_player_stats(evs2, p2_id)}

    except Exception as ex:
        print(f'[player-stats] {ex}')
        result['error'] = str(ex)

    with _PLAYER_LOCK:
        _PLAYER_CACHE[cache_key] = {'data': result, 'ts': now}
    return result


def _league_name(ev):
    league = ev.get('league') or {}
    if isinstance(league, dict):
        return (league.get('nameDefault') or league.get('name') or '').lower()
    return ''


def _is_not_tt(ev):
    """True if event is clearly NOT table tennis (hockey/big tennis/football)."""
    ln = _league_name(ev)
    if any(kw in ln for kw in _HOCKEY_KW): return True
    if any(kw in ln for kw in _BIGTEN_KW): return True
    if 'теннис' in ln and 'настольный' not in ln: return True
    if 'tennis' in ln and 'table' not in ln and 'настольный' not in ln: return True
    return False


def fetch_sport_event_list(sport):
    all_events = {}
    for q in SPORT_QUERIES[sport]:
        try:
            url = f'https://leon.ru/api-2/betline/search?ctag=ru-RU&q={q}'
            items = get_json(url)
            if not isinstance(items, list):
                continue
            for e in items:
                eid = e.get('id')
                if not eid or eid in all_events:
                    continue

                if sport == 'tt':
                    # TT: accept everything from TT queries EXCEPT clearly other sports
                    if not _is_not_tt(e):
                        all_events[eid] = e
                elif sport == 'hockey':
                    ln = _league_name(e)
                    if any(kw in ln for kw in _HOCKEY_KW):
                        all_events[eid] = e
                elif sport == 'tennis':
                    ln = _league_name(e)
                    has_tennis = any(kw in ln for kw in _BIGTEN_KW) or \
                                 ('теннис' in ln and 'настольный' not in ln) or \
                                 ('tennis' in ln and 'table' not in ln)
                    if has_tennis:
                        all_events[eid] = e
                elif sport == 'football':
                    ln = _league_name(e)
                    is_other = any(kw in ln for kw in _HOCKEY_KW) or \
                               any(kw in ln for kw in _BIGTEN_KW) or \
                               ('настольный' in ln) or ('table tennis' in ln)
                    if not is_other:
                        all_events[eid] = e
        except Exception as ex:
            print(f'[{sport} q={q}] {ex}')

    live = sum(1 for e in all_events.values() if e.get('matchPhase') == 'IN_PLAY')
    pre  = sum(1 for e in all_events.values() if e.get('matchPhase') == 'PRE_GAME')
    print(f'[{sport}] total={len(all_events)} live={live} pre={pre}')
    return list(all_events.values())


def fetch_leon_event_detail(event_id):
    url = (f'https://leon.ru/api-2/betline/event/inplay'
           f'?ctag=ru-RU&eventId={event_id}&flags=urlv2,reg,mainmarkets')
    return get_json(url, timeout=10)


# ── Parsing helpers ──────────────────────────────────────────────────────────

def _parse_sets(s):
    sets = []
    for part in s.split(';'):
        part = part.strip()
        if ':' in part:
            h, a = part.split(':')
            try:
                sets.append({'home': int(h.strip()), 'away': int(a.strip())})
            except ValueError:
                pass
    return sets


def _base_names(ev, base):
    competitors = ev.get('competitors', base.get('competitors', []))
    hc = next((c for c in competitors if c.get('homeAway') == 'HOME'), {})
    ac = next((c for c in competitors if c.get('homeAway') == 'AWAY'), {})
    nd = ev.get('nameDefault', base.get('nameDefault', ''))
    if ' - ' in nd:
        hn, an = nd.split(' - ', 1)
    else:
        hn = hc.get('nameDefault') or hc.get('name') or 'Команда 1'
        an = ac.get('nameDefault') or ac.get('name') or 'Команда 2'
    league = ev.get('league', base.get('league')) or {}
    lg = (league.get('nameDefault') or league.get('name') or '') if isinstance(league, dict) else ''
    url_path = base.get('url') or (ev.get('url') if ev else '') or ''
    if url_path and not url_path.startswith('/'):
        url_path = ''
    leon_url = f'https://leon.ru{url_path}' if url_path else 'https://leon.ru/'
    is_live = (ev.get('matchPhase') or base.get('matchPhase')) == 'IN_PLAY'
    return hn.strip(), an.strip(), lg, leon_url, is_live


# ── TT ───────────────────────────────────────────────────────────────────────

def _odds_tt(markets):
    w1 = w2 = None
    tot_over = tot_under = tot_line = None
    hdp_h = hdp_a = hdp_l = None
    best_bal = 999.0
    for m in (markets or []):
        if not m.get('open', True): continue
        runners = m.get('runners', [])
        if len(runners) < 2: continue
        mn = m.get('name', '').lower()
        rnames = [r.get('name', '').strip() for r in runners]
        if not w1 and len(runners) == 2 and '1' in rnames and '2' in rnames:
            for r in runners:
                n, p = r.get('name', '').strip(), r.get('price')
                if p and p > 1.0:
                    if n == '1': w1 = p
                    elif n == '2': w2 = p
        if 'тотал очков' in mn and len(runners) == 2:
            ov = un = None
            for r in runners:
                n, p = r.get('name', ''), r.get('price')
                nl = n.lower()
                if 'больше' in nl and p: ov = (p, n)
                elif 'меньше' in nl and p: un = (p, n)
            if ov and un:
                ml = _re.search(r'[\d.]+', ov[1])
                if ml:
                    line = float(ml.group())
                    bal = abs(ov[0] - 2.0) + abs(un[0] - 2.0)
                    if bal < best_bal:
                        best_bal = bal; tot_line = line; tot_over = ov[0]; tot_under = un[0]
        if 'фора по сетам' in mn and len(runners) == 2 and not hdp_h:
            for r in runners:
                n, p = r.get('name', '').strip(), r.get('price')
                if not p or p <= 1.0: continue
                hm = _re.search(r'([+-][\d.]+)', n)
                lv = float(hm.group(1)) if hm else None
                if n.startswith('1'): hdp_h, hdp_l = p, lv
                elif n.startswith('2'): hdp_a = p
    return w1, w2, tot_over, tot_under, tot_line, hdp_h, hdp_a, hdp_l


def parse_tt(base, detail=None):
    ev = detail if detail else base
    hn, an, lg, url, is_live = _base_names(ev, base)
    ls = ev.get('liveStatus') or base.get('liveStatus') or {}
    hs = aws = 0; sets = []; clh = cla = 0; csn = 1
    if ls:
        sc = ls.get('score', '0:0').replace('*', '').strip()
        if ':' in sc:
            try: h, a = sc.split(':'); hs, aws = int(h), int(a)
            except ValueError: pass
        sets = _parse_sets(ls.get('setScores', ''))
        ph = ls.get('detailedPhase', 'SET_1')
        if 'SET_' in ph:
            try: csn = int(ph.replace('SET_', ''))
            except: csn = len(sets)
        if sets:
            last = sets[-1]
            done = (last['home'] >= 11 and last['home'] - last['away'] >= 2) or \
                   (last['away'] >= 11 and last['away'] - last['home'] >= 2) or \
                   (last['home'] >= 14 or last['away'] >= 14)
            if not done: clh, cla = last['home'], last['away']
    mkts = ev.get('markets', [])
    w1, w2, to, tu, tl, hh, ha, hl = _odds_tt(mkts)
    # Record finished matches into our player database
    if hs >= 3 or aws >= 3:
        record_tt_result(hn, an, hs, aws)
    return {
        'id': str(ev.get('id', base.get('id', ''))), 'source': 'leon', 'sport': 'tt',
        'homeTeam': hn, 'awayTeam': an, 'tournament': lg or 'Настольный теннис',
        'homeSets': hs, 'awaySets': aws, 'sets': sets,
        'currentSetNum': csn, 'currentHomePts': clh, 'currentAwayPts': cla,
        'homeScore': hs, 'awayScore': aws, 'period': csn, 'periodLabel': f'Партия {csn}',
        'w1Odds': w1, 'w2Odds': w2, 'wxOdds': None,
        'totalOverOdds': to, 'totalUnderOdds': tu, 'totalLine': tl,
        'hdpHomeOdds': hh, 'hdpAwayOdds': ha, 'hdpLine': hl,
        'leonUrl': url, 'isLive': is_live, 'status': 'inprogress' if is_live else 'notstarted',
    }


# ── Football / Hockey ────────────────────────────────────────────────────────

def _odds_football(markets):
    w1 = wx = w2 = None
    tot_over = tot_under = tot_line = None
    hdp_h = hdp_a = hdp_l = None
    best_bal = 999.0
    for m in (markets or []):
        if not m.get('open', True): continue
        runners = m.get('runners', [])
        if len(runners) < 2: continue
        mn = m.get('name', '').lower()
        rn_low = [r.get('name', '').strip().lower() for r in runners]
        rn_orig = [r.get('name', '').strip() for r in runners]

        # 3-way
        if not w1 and len(runners) == 3:
            has1 = '1' in rn_orig; has2 = '2' in rn_orig
            hasX = any(n in ('x', 'ничья', 'draw') for n in rn_low)
            if has1 and has2 and hasX:
                for r in runners:
                    n = r.get('name', '').strip(); nl = n.lower(); p = r.get('price')
                    if not p or p <= 1.0: continue
                    if n == '1': w1 = p
                    elif n == '2': w2 = p
                    elif nl in ('x', 'ничья', 'draw'): wx = p

        # 2-way
        if not w1 and len(runners) == 2 and '1' in rn_orig and '2' in rn_orig:
            for r in runners:
                n, p = r.get('name', '').strip(), r.get('price')
                if p and p > 1.0:
                    if n == '1': w1 = p
                    elif n == '2': w2 = p

        # Total
        if ('тотал' in mn or 'total' in mn) and len(runners) == 2:
            if any(x in mn for x in ('сет', 'партия', 'гейм', 'сет')): continue
            ov = un = None
            for r in runners:
                n, p = r.get('name', ''), r.get('price'); nl = n.lower()
                if ('больше' in nl or 'over' in nl) and p: ov = (p, n)
                elif ('меньше' in nl or 'under' in nl) and p: un = (p, n)
            if ov and un:
                ml = _re.search(r'[\d.]+', ov[1])
                if ml:
                    line = float(ml.group())
                    bal = abs(ov[0] - 2.0) + abs(un[0] - 2.0)
                    if bal < best_bal:
                        best_bal = bal; tot_line = line; tot_over = ov[0]; tot_under = un[0]

        # Handicap
        if ('фора' in mn or 'гандикап' in mn) and len(runners) == 2 and not hdp_h:
            if any(x in mn for x in ('сет', 'партия')): continue
            for r in runners:
                n, p = r.get('name', '').strip(), r.get('price')
                if not p or p <= 1.0: continue
                hm = _re.search(r'([+-][\d.]+)', n)
                lv = float(hm.group(1)) if hm else None
                if n.startswith('1'): hdp_h, hdp_l = p, lv
                elif n.startswith('2'): hdp_a = p
    return w1, wx, w2, tot_over, tot_under, tot_line, hdp_h, hdp_a, hdp_l


def _parse_phase(phase, sport):
    ph = (phase or '').upper()
    if sport == 'football':
        if any(x in ph for x in ('FIRST', '1ST', 'HALF_1')): return 1, '1-й тайм'
        if any(x in ph for x in ('SECOND', '2ND', 'HALF_2')): return 2, '2-й тайм'
        if 'EXTRA' in ph or 'OVER' in ph: return 3, 'Доп. время'
        if 'PENALTY' in ph: return 4, 'Пенальти'
        return 1, '1-й тайм'
    else:  # hockey
        if any(x in ph for x in ('FIRST', 'PERIOD_1', '1ST')): return 1, '1-й период'
        if any(x in ph for x in ('SECOND', 'PERIOD_2', '2ND')): return 2, '2-й период'
        if any(x in ph for x in ('THIRD', 'PERIOD_3', '3RD')): return 3, '3-й период'
        if 'OT' in ph or 'OVER' in ph: return 4, 'ОТ'
        if any(x in ph for x in ('SHOOT', 'PENALTY')): return 5, 'Буллиты'
        return 1, '1-й период'


def parse_football(base, detail=None, sport='football'):
    ev = detail if detail else base
    hn, an, lg, url, is_live = _base_names(ev, base)
    ls = ev.get('liveStatus') or base.get('liveStatus') or {}
    hs = aws = 0; period = 1; plabel = ''; minute = 0
    if ls:
        sc = ls.get('score', '0:0').replace('*', '').strip()
        if ':' in sc:
            try: h, a = sc.split(':'); hs, aws = int(h), int(a)
            except ValueError: pass
        period, plabel = _parse_phase(ls.get('detailedPhase', ''), sport)
        mt = ls.get('matchTime') or ls.get('minute') or ls.get('timer') or 0
        if isinstance(mt, str):
            try: minute = int(mt.strip("+' "))
            except: minute = 0
        else:
            minute = int(mt) if mt else 0
    mkts = ev.get('markets', [])
    w1, wx, w2, to, tu, tl, hh, ha, hl = _odds_football(mkts)
    lbl = {'football': 'Футбол', 'hockey': 'Хоккей'}.get(sport, sport)
    return {
        'id': str(ev.get('id', base.get('id', ''))), 'source': 'leon', 'sport': sport,
        'homeTeam': hn, 'awayTeam': an, 'tournament': lg or lbl,
        'homeScore': hs, 'awayScore': aws,
        'homeSets': hs, 'awaySets': aws,
        'sets': [], 'currentSetNum': period, 'currentHomePts': 0, 'currentAwayPts': 0,
        'period': period, 'periodLabel': plabel, 'minute': minute,
        'w1Odds': w1, 'wxOdds': wx, 'w2Odds': w2,
        'totalOverOdds': to, 'totalUnderOdds': tu, 'totalLine': tl,
        'hdpHomeOdds': hh, 'hdpAwayOdds': ha, 'hdpLine': hl,
        'leonUrl': url, 'isLive': is_live, 'status': 'inprogress' if is_live else 'notstarted',
    }


# ── Tennis ───────────────────────────────────────────────────────────────────

def _odds_tennis(markets):
    w1 = w2 = None
    tot_over = tot_under = tot_line = None
    hdp_h = hdp_a = hdp_l = None
    best_bal = 999.0
    for m in (markets or []):
        if not m.get('open', True): continue
        runners = m.get('runners', [])
        if len(runners) < 2: continue
        mn = m.get('name', '').lower()
        rn = [r.get('name', '').strip() for r in runners]
        if not w1 and len(runners) == 2 and '1' in rn and '2' in rn:
            for r in runners:
                n, p = r.get('name', '').strip(), r.get('price')
                if p and p > 1.0:
                    if n == '1': w1 = p
                    elif n == '2': w2 = p
        if ('тотал' in mn or 'гейм' in mn) and len(runners) == 2:
            if 'сет' in mn: continue
            ov = un = None
            for r in runners:
                n, p = r.get('name', ''), r.get('price'); nl = n.lower()
                if 'больше' in nl and p: ov = (p, n)
                elif 'меньше' in nl and p: un = (p, n)
            if ov and un:
                ml = _re.search(r'[\d.]+', ov[1])
                if ml:
                    line = float(ml.group())
                    bal = abs(ov[0] - 2.0) + abs(un[0] - 2.0)
                    if bal < best_bal:
                        best_bal = bal; tot_line = line; tot_over = ov[0]; tot_under = un[0]
        if 'фора по сетам' in mn and len(runners) == 2 and not hdp_h:
            for r in runners:
                n, p = r.get('name', '').strip(), r.get('price')
                if not p or p <= 1.0: continue
                hm = _re.search(r'([+-][\d.]+)', n)
                lv = float(hm.group(1)) if hm else None
                if n.startswith('1'): hdp_h, hdp_l = p, lv
                elif n.startswith('2'): hdp_a = p
    return w1, w2, tot_over, tot_under, tot_line, hdp_h, hdp_a, hdp_l


def parse_tennis(base, detail=None):
    ev = detail if detail else base
    hn, an, lg, url, is_live = _base_names(ev, base)
    ls = ev.get('liveStatus') or base.get('liveStatus') or {}
    hs = aws = 0; sets = []; clh = cla = 0; csn = 1
    if ls:
        sc = ls.get('score', '0:0').replace('*', '').strip()
        if ':' in sc:
            try: h, a = sc.split(':'); hs, aws = int(h), int(a)
            except ValueError: pass
        sets = _parse_sets(ls.get('setScores', ''))
        ph = ls.get('detailedPhase', 'SET_1')
        if 'SET_' in ph:
            try: csn = int(ph.replace('SET_', ''))
            except: csn = max(1, len(sets))
        if sets:
            last = sets[-1]
            done = (last['home'] >= 6 and last['home'] - last['away'] >= 2) or \
                   (last['away'] >= 6 and last['away'] - last['home'] >= 2) or \
                   (last['home'] >= 7 or last['away'] >= 7)
            if not done: clh, cla = last['home'], last['away']
    mkts = ev.get('markets', [])
    w1, w2, to, tu, tl, hh, ha, hl = _odds_tennis(mkts)
    return {
        'id': str(ev.get('id', base.get('id', ''))), 'source': 'leon', 'sport': 'tennis',
        'homeTeam': hn, 'awayTeam': an, 'tournament': lg or 'Теннис',
        'homeSets': hs, 'awaySets': aws, 'sets': sets,
        'currentSetNum': csn, 'currentHomePts': clh, 'currentAwayPts': cla,
        'homeScore': hs, 'awayScore': aws, 'period': csn, 'periodLabel': f'Сет {csn}',
        'setsToWin': 2,
        'w1Odds': w1, 'w2Odds': w2, 'wxOdds': None,
        'totalOverOdds': to, 'totalUnderOdds': tu, 'totalLine': tl,
        'hdpHomeOdds': hh, 'hdpAwayOdds': ha, 'hdpLine': hl,
        'leonUrl': url, 'isLive': is_live, 'status': 'inprogress' if is_live else 'notstarted',
    }


# ── Main fetch ───────────────────────────────────────────────────────────────

PARSERS = {
    'tt':       lambda e, d: parse_tt(e, d),
    'football': lambda e, d: parse_football(e, d, 'football'),
    'hockey':   lambda e, d: parse_football(e, d, 'hockey'),
    'tennis':   lambda e, d: parse_tennis(e, d),
}


def get_sport_data(sport):
    now = time.time()
    with _lock:
        c = _caches[sport]
        if c['events'] and now - c['ts'] < CACHE_TTL:
            return c

    evs = fetch_sport_event_list(sport)
    live_evs = [e for e in evs if e.get('matchPhase') == 'IN_PLAY']
    pre_evs  = [e for e in evs if e.get('matchPhase') == 'PRE_GAME']

    details = {}
    if live_evs:
        with ThreadPoolExecutor(max_workers=6) as exe:
            futs = {exe.submit(fetch_leon_event_detail, e['id']): e['id'] for e in live_evs}
            for f in as_completed(futs, timeout=20):
                eid = futs[f]
                try: details[eid] = f.result()
                except Exception as ex: print(f'[{sport} detail {eid}] {ex}')

    parse = PARSERS[sport]
    result = []
    for e in live_evs:
        result.append(parse(e, details.get(e['id'])))
    for e in pre_evs[:10]:
        result.append(parse(e, None))

    live_odds = sum(1 for r in result if r['isLive'] and r['w1Odds'])
    label = f"Leon ({len(live_evs)} лайв, {len(pre_evs)} upcoming)"
    if live_odds:
        label += f" · {live_odds} с котировками"

    new_cache = {'events': result, 'ts': now, 'source': label, 'errors': []}
    with _lock:
        _caches[sport] = new_cache
    return new_cache


# ── HTTP server ───────────────────────────────────────────────────────────────

BASE_DIR = os.path.dirname(os.path.abspath(__file__))


class Handler(SimpleHTTPRequestHandler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=BASE_DIR, **kwargs)

    def do_GET(self):
        if self.path.startswith('/api/live'):
            self._api()
        elif self.path.startswith('/api/player-stats'):
            self._player_stats_api()
        elif self.path.startswith('/api/ai-analysis'):
            self._ai_api()
        elif self.path == '/health':
            self.send_response(200)
            self.send_header('Content-Type', 'text/plain')
            self.end_headers()
            self.wfile.write(b'ok')
        else:
            super().do_GET()

    def _api(self):
        try:
            qs = urllib.parse.parse_qs(urllib.parse.urlparse(self.path).query)
            sport = qs.get('sport', ['tt'])[0]
            if sport not in SPORTS:
                sport = 'tt'
            res = get_sport_data(sport)
            self._json_resp(200, {
                'events': res['events'], 'source': res['source'],
                'count': len(res['events']), 'sport': sport, 'ts': int(time.time()),
            })
        except Exception as ex:
            self._json_resp(500, {'error': str(ex), 'events': []})

    def _json_resp(self, code, data):
        body = json.dumps(data, ensure_ascii=False).encode('utf-8')
        self.send_response(code)
        self.send_header('Content-Type', 'application/json; charset=utf-8')
        self.send_header('Content-Length', str(len(body)))
        self.send_header('Access-Control-Allow-Origin', '*')
        self.send_header('Cache-Control', 'no-cache')
        self.end_headers()
        self.wfile.write(body)

    def _player_stats_api(self):
        try:
            qs = urllib.parse.parse_qs(urllib.parse.urlparse(self.path).query)
            p1 = qs.get('p1', [''])[0].strip()
            p2 = qs.get('p2', [''])[0].strip()
            if not p1 or not p2:
                self._json_resp(400, {'error': 'p1 and p2 required'})
                return
            # Local DB first (always fast, no blocking)
            result = get_local_player_stats(p1, p2)
            # If local is empty, try sofascore (may fail on cloud IPs)
            if not result['p1'] and not result['p2']:
                try:
                    sofa = get_player_stats(p1, p2)
                    if sofa.get('p1') or sofa.get('p2'):
                        result = sofa
                except Exception as ex:
                    result['sofascoreError'] = str(ex)
            self._json_resp(200, result)
        except Exception as ex:
            self._json_resp(500, {'error': str(ex)})

    def _ai_api(self):
        try:
            qs = urllib.parse.parse_qs(urllib.parse.urlparse(self.path).query)
            eid  = qs.get('id',   [''])[0]
            home = qs.get('home', [''])[0].strip()
            away = qs.get('away', [''])[0].strip()
            if not home or not away:
                self._json_resp(400, {'error': 'home and away required'})
                return
            stats = get_local_player_stats(home, away)
            if not stats['p1'] and not stats['p2']:
                try:
                    sofa = get_player_stats(home, away)
                    if sofa.get('p1') or sofa.get('p2'):
                        stats = sofa
                except Exception:
                    pass
            # Build minimal match_data from query params
            match_data = {
                'homeTeam': home, 'awayTeam': away,
                'homeSets': int(qs.get('hs', ['0'])[0]),
                'awaySets': int(qs.get('as', ['0'])[0]),
                'currentHomePts': int(qs.get('chp', ['0'])[0]),
                'currentAwayPts': int(qs.get('cap', ['0'])[0]),
                'w1Odds': qs.get('w1', [None])[0],
                'w2Odds': qs.get('w2', [None])[0],
            }
            result = get_ai_analysis(eid, home, away, match_data, stats)
            self._json_resp(200, {**result, 'stats': stats, 'groqEnabled': bool(GROQ_API_KEY)})
        except Exception as ex:
            self._json_resp(500, {'error': str(ex)})

    def log_message(self, fmt, *args):
        if args and '/api/' in str(args[0]):
            print(f'  [{time.strftime("%H:%M:%S")}] {args[0]} {args[1]}')

    def log_error(self, *args):
        pass


def main():
    host = '0.0.0.0'
    print('=' * 52)
    print('  Sports Live Analyzer v4')
    print(f'  Port: {PORT}')
    print('  Спорт: TT · Футбол · Хоккей · Теннис')
    print('=' * 52)
    server = HTTPServer((host, PORT), Handler)
    if PORT == 8080 and os.environ.get('RENDER') is None:
        def _open():
            time.sleep(1.2)
            webbrowser.open(f'http://localhost:{PORT}')
        threading.Thread(target=_open, daemon=True).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print('\nСервер остановлен.')


if __name__ == '__main__':
    main()