#!/usr/bin/env python3
"""
TT Live Analyzer — Backend Server v3
Источник: Leon.ru (котировки + счёт через betline API)
Запуск: python server.py  или двойной клик start.bat
"""

import json, os, re as _re, ssl, time, threading, webbrowser
import urllib.request, urllib.parse, urllib.error
from http.server import HTTPServer, SimpleHTTPRequestHandler
from concurrent.futures import ThreadPoolExecutor, as_completed

PORT      = int(os.environ.get('PORT', 8080))
CACHE_TTL = 20  # секунд

_cache = {'events': [], 'ts': 0, 'source': ''}
_lock  = threading.Lock()

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


def get_json(url, timeout=12):
    req = urllib.request.Request(url, headers=LEON_HEADERS)
    with urllib.request.urlopen(req, context=SSL_CTX, timeout=timeout) as r:
        return json.loads(r.read().decode('utf-8'))


# ================================================================
# Leon: поиск событий НТ
# ================================================================
SEARCH_QUERIES = ['Setka', 'Table+Tennis', 'TTL', 'Ping+Pong', 'WTT']

def fetch_leon_event_list():
    """Собираем все НТ события через поиск (по нескольким запросам)"""
    all_events = {}
    for q in SEARCH_QUERIES:
        try:
            url = f'https://leon.ru/api-2/betline/search?ctag=ru-RU&q={q}'
            items = get_json(url)
            if isinstance(items, list):
                for e in items:
                    if e.get('id'):
                        all_events[e['id']] = e
        except Exception as ex:
            print(f'[Leon search q={q}] {ex}')
    live = sum(1 for e in all_events.values() if e.get('matchPhase') == 'IN_PLAY')
    pre  = sum(1 for e in all_events.values() if e.get('matchPhase') == 'PRE_GAME')
    print(f'[Leon] Всего событий: {len(all_events)}, лайв: {live}, предстоящих: {pre}')
    return list(all_events.values())


def fetch_leon_event_detail(event_id):
    """Получаем полные данные события: рынки + котировки + счёт"""
    url = (f'https://leon.ru/api-2/betline/event/inplay'
           f'?ctag=ru-RU&eventId={event_id}&flags=urlv2,reg,mainmarkets')
    return get_json(url, timeout=10)


# ================================================================
# Парсинг
# ================================================================
def _parse_sets(set_scores_str):
    """"11:8; 8:11; 6:7" → [{'home':11,'away':8}, ...]"""
    sets = []
    for part in set_scores_str.split(';'):
        part = part.strip()
        if ':' in part:
            h, a = part.split(':')
            try:
                sets.append({'home': int(h.strip()), 'away': int(a.strip())})
            except ValueError:
                pass
    return sets


def _extract_odds(markets):
    """Парсим котировки W1/W2, Тотал очков, Фора по сетам"""
    w1 = w2 = None
    total_over = total_under = total_line = None
    hdp_home = hdp_away = hdp_line = None
    best_bal = 999.0  # для выбора самой сбалансированной линии тотала

    for m in (markets or []):
        if not m.get('open', True):
            continue
        runners = m.get('runners', [])
        if len(runners) < 2:
            continue
        mname = m.get('name', '').lower()

        # ── Победитель матча (W1/W2) ──────────────────────
        rnames = [r.get('name', '').strip() for r in runners]
        if not w1 and len(runners) == 2 and '1' in rnames and '2' in rnames:
            for r in runners:
                n, p = r.get('name', '').strip(), r.get('price')
                if p and p > 1.0:
                    if n == '1': w1 = p
                    elif n == '2': w2 = p

        # ── Тотал очков (total points over/under) ─────────
        if 'тотал очков' in mname and len(runners) == 2:
            over_r = under_r = None
            for r in runners:
                n, p = r.get('name', ''), r.get('price')
                nl = n.lower()
                if 'больше' in nl and p: over_r = (p, n)
                elif 'меньше' in nl and p: under_r = (p, n)
            if over_r and under_r:
                m_line = _re.search(r'[\d.]+', over_r[1])
                if m_line:
                    line = float(m_line.group())
                    bal = abs(over_r[0] - 2.0) + abs(under_r[0] - 2.0)
                    if bal < best_bal:  # выбираем линию с самыми ровными коэффициентами
                        best_bal   = bal
                        total_line = line
                        total_over  = over_r[0]
                        total_under = under_r[0]

        # ── Фора по сетам (sets handicap) ─────────────────
        if 'фора по сетам' in mname and len(runners) == 2 and not hdp_home:
            for r in runners:
                n, p = r.get('name', '').strip(), r.get('price')
                if not p or p <= 1.0: continue
                hm = _re.search(r'([+-][\d.]+)', n)
                line_val = float(hm.group(1)) if hm else None
                if n.startswith('1'):
                    hdp_home, hdp_line = p, line_val
                elif n.startswith('2'):
                    hdp_away = p

    return w1, w2, total_over, total_under, total_line, hdp_home, hdp_away, hdp_line


def parse_leon_event(base_event, detail=None):
    """Нормализуем событие Леона → внутренний формат"""
    ev = detail if detail else base_event

    competitors = ev.get('competitors', base_event.get('competitors', []))
    home_comp = next((c for c in competitors if c.get('homeAway') == 'HOME'), {})
    away_comp = next((c for c in competitors if c.get('homeAway') == 'AWAY'), {})

    # Имена из nameDefault (латиница, чистая)
    name_default = ev.get('nameDefault', base_event.get('nameDefault', ''))
    if ' - ' in name_default:
        home_name, away_name = name_default.split(' - ', 1)
    else:
        home_name = home_comp.get('nameDefault') or home_comp.get('name') or 'Игрок 1'
        away_name = away_comp.get('nameDefault') or away_comp.get('name') or 'Игрок 2'

    # Лига
    league = ev.get('league', base_event.get('league')) or {}
    if isinstance(league, dict):
        league_name = league.get('nameDefault') or league.get('name') or 'Настольный теннис'
    else:
        league_name = 'Настольный теннис'

    # Счёт из liveStatus
    ls = ev.get('liveStatus') or base_event.get('liveStatus') or {}
    home_sets = away_sets = 0
    sets = []
    clh = cla = 0
    cur_set_num = 1

    if ls:
        score_str = ls.get('score', '0:0').replace('*', '').strip()
        if ':' in score_str:
            try:
                h, a = score_str.split(':')
                home_sets, away_sets = int(h), int(a)
            except ValueError:
                pass

        set_scores_str = ls.get('setScores', '')
        sets = _parse_sets(set_scores_str)

        # Номер текущей партии
        phase = ls.get('detailedPhase', 'SET_1')
        if 'SET_' in phase:
            try:
                cur_set_num = int(phase.replace('SET_', ''))
            except ValueError:
                cur_set_num = len(sets)

        # Счёт в текущей партии = последняя запись в setScores
        if sets:
            last = sets[-1]
            is_done = (last['home'] >= 11 and last['home'] - last['away'] >= 2) or \
                      (last['away'] >= 11 and last['away'] - last['home'] >= 2) or \
                      (last['home'] >= 14 or last['away'] >= 14)
            if not is_done:
                clh, cla = last['home'], last['away']

    # Котировки
    markets = ev.get('markets', [])
    w1, w2, total_over, total_under, total_line, hdp_home, hdp_away, hdp_line = _extract_odds(markets)

    # URL на Леон — берём из base_event (поиск), там полный путь
    url_path = base_event.get('url') or (ev.get('url') if ev else '') or ''
    if url_path and not url_path.startswith('/'):
        url_path = ''
    leon_url = f'https://leon.ru{url_path}' if url_path else 'https://leon.ru/bets/table-tennis'

    is_live = (ev.get('matchPhase') or base_event.get('matchPhase')) == 'IN_PLAY'

    return {
        'id':              str(ev.get('id', base_event.get('id', ''))),
        'source':          'leon',
        'homeTeam':        home_name.strip(),
        'awayTeam':        away_name.strip(),
        'homeRanking':     0,
        'awayRanking':     0,
        'tournament':      league_name,
        'homeSets':        home_sets,
        'awaySets':        away_sets,
        'sets':            sets,
        'currentSetNum':   cur_set_num,
        'currentHomePts':  clh,
        'currentAwayPts':  cla,
        'w1Odds':          w1,
        'w2Odds':          w2,
        'totalOverOdds':   total_over,
        'totalUnderOdds':  total_under,
        'totalLine':       total_line,
        'hdpHomeOdds':     hdp_home,
        'hdpAwayOdds':     hdp_away,
        'hdpLine':         hdp_line,
        'leonUrl':         leon_url,
        'isLive':          is_live,
        'status':          'inprogress' if is_live else 'notstarted',
    }


# ================================================================
# Главная функция
# ================================================================
def get_all_live():
    global _cache
    now = time.time()
    with _lock:
        if _cache['events'] and now - _cache['ts'] < CACHE_TTL:
            return _cache

    events_list = fetch_leon_event_list()

    live_events = [e for e in events_list if e.get('matchPhase') == 'IN_PLAY']
    pre_events  = [e for e in events_list if e.get('matchPhase') == 'PRE_GAME']

    # Параллельно забираем детали (рынки + котировки) для лайв событий
    details = {}
    if live_events:
        with ThreadPoolExecutor(max_workers=6) as exe:
            futures = {exe.submit(fetch_leon_event_detail, e['id']): e['id']
                       for e in live_events}
            for f in as_completed(futures, timeout=20):
                eid = futures[f]
                try:
                    details[eid] = f.result()
                except Exception as ex:
                    print(f'[Leon detail {eid}] {ex}')

    result = []
    # Лайв первыми
    for e in live_events:
        detail = details.get(e['id'])
        result.append(parse_leon_event(e, detail))
    # Затем предстоящие
    for e in pre_events[:10]:
        result.append(parse_leon_event(e))

    live_with_odds = sum(1 for r in result if r['isLive'] and r['w1Odds'])
    source_label = f"Leon ({len(live_events)} лайв, {len(pre_events)} upcoming)"
    if live_with_odds:
        source_label += f" · {live_with_odds} с котировками"

    with _lock:
        _cache = {
            'events': result,
            'ts':     now,
            'source': source_label,
            'errors': [],
        }
    return _cache


# ================================================================
# HTTP-сервер
# ================================================================
BASE_DIR = os.path.dirname(os.path.abspath(__file__))


class Handler(SimpleHTTPRequestHandler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=BASE_DIR, **kwargs)

    def do_GET(self):
        if self.path.startswith('/api/live'):
            self._api()
        elif self.path == '/health':
            self.send_response(200)
            self.send_header('Content-Type', 'text/plain')
            self.end_headers()
            self.wfile.write(b'ok')
        else:
            super().do_GET()

    def _api(self):
        try:
            res  = get_all_live()
            body = json.dumps({
                'events': res['events'],
                'source': res['source'],
                'count':  len(res['events']),
                'ts':     int(time.time()),
            }, ensure_ascii=False).encode('utf-8')

            self.send_response(200)
            self.send_header('Content-Type',  'application/json; charset=utf-8')
            self.send_header('Content-Length', str(len(body)))
            self.send_header('Access-Control-Allow-Origin', '*')
            self.send_header('Cache-Control',  'no-cache')
            self.end_headers()
            self.wfile.write(body)

        except Exception as ex:
            body = json.dumps({'error': str(ex), 'events': []},
                              ensure_ascii=False).encode()
            self.send_response(500)
            self.send_header('Content-Type',  'application/json')
            self.send_header('Content-Length', str(len(body)))
            self.send_header('Access-Control-Allow-Origin', '*')
            self.end_headers()
            self.wfile.write(body)

    def log_message(self, fmt, *args):
        if args and '/api/' in str(args[0]):
            print(f'  [{time.strftime("%H:%M:%S")}] {args[0]} {args[1]}')

    def log_error(self, *args):
        pass


def main():
    host = '0.0.0.0'  # слушаем все интерфейсы (обязательно для облака)
    print('=' * 50)
    print('  TT Live Analyzer v3')
    print(f'  Port: {PORT}')
    print('  Источник: Leon.ru')
    print('=' * 50)

    server = HTTPServer((host, PORT), Handler)

    # Открываем браузер только при локальном запуске
    if PORT == 8080 and os.environ.get('RENDER') is None:
        def open_browser():
            time.sleep(1.2)
            webbrowser.open(f'http://localhost:{PORT}')
        threading.Thread(target=open_browser, daemon=True).start()

    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print('\nСервер остановлен.')


if __name__ == '__main__':
    main()