#!/usr/bin/env python3
"""Sports Live Analyzer — Backend v5 | Leon.ru + Sofascore | TT·Football·Hockey·Tennis"""

import json, math, os, re as _re, ssl, time, threading, webbrowser

try:
    import numpy as _np
    _HAS_NP = True
except ImportError:
    _HAS_NP = False

try:
    from bs4 import BeautifulSoup
    _HAS_BS4 = True
except ImportError:
    _HAS_BS4 = False
import urllib.request, urllib.parse, urllib.error
from http.server import HTTPServer, SimpleHTTPRequestHandler
from concurrent.futures import ThreadPoolExecutor, as_completed

PORT          = int(os.environ.get('PORT', 8080))
CACHE_TTL     = 20
GROQ_API_KEY  = os.environ.get('GROQ_API_KEY', '')

SPORTS  = ['tt', 'football', 'hockey', 'tennis']
_caches = {s: {'events': [], 'ts': 0, 'source': ''} for s in SPORTS}
_lock   = threading.Lock()

_PLAYER_CACHE = {}
_PLAYER_LOCK  = threading.Lock()
PLAYER_TTL    = 3600 * 6  # 6 hours

# ── Neural Network globals ────────────────────────────────────────────────────
_NN_DATA        = []   # [(feature_vector, label_0_or_1)]  training samples
_NN_MODEL       = None # trained TinyNN instance
_NN_LOCK        = threading.Lock()
_MATCH_SEEN     = {}   # {match_id: feature_vector}  live snapshots awaiting outcome
_NN_LAST_TRAIN  = 0
NN_MIN_SAMPLES  = 30   # start training after this many labelled samples
NN_RETRAIN_INT  = 900  # retrain every 15 min max
NN_N_IN         = 12   # number of input features (8 base + elo diff + elo strength + 2x win-rate)
_NN_WEIGHTS_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'nn_weights.json')
_ELO_FILE        = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'elo_db.json')
_PAT_FILE        = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'pat_db.json')
_PLYR_FILE       = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'player_db.json')

_ELO_DB   = {}   # {norm_name: elo_rating}
_PAT_DB   = {}   # {sit_key: [home_wins, away_wins]}
_ELO_LOCK = threading.Lock()
ELO_K     = 24
ELO_DEF   = 1500

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

# One broad query catches all football on Leon; virtual is filtered out by keyword below
FOOTBALL_QUERIES = ['Футбол', 'Football', 'Soccer']

SPORT_QUERIES = {
    'tt':       TT_QUERIES,
    'football': FOOTBALL_QUERIES,
    'hockey':   ['Хоккей', 'КХЛ', 'NHL', 'SHL', 'Liiga', 'DEL', 'AHL'],
    'tennis':   ['Теннис', 'ATP', 'WTA', 'ITF', 'Roland+Garros', 'Wimbledon'],
}

_HOCKEY_KW  = ['хоккей', 'hockey', 'кхл', 'nhl', 'shl', 'liiga', 'del ', 'ahl', 'нхл']
_BIGTEN_KW  = ['atp', 'wta', 'itf', 'roland garros', 'wimbledon', 'us open',
               'australian open', 'challenger', 'davis cup', 'fed cup']
_VIRTUAL_KW = ['виртуальн', 'virtual', 'кибер', 'cyber', 'robot', 'liga pro',
               'setka cup', 'inplay tt', 'настольный', 'table tennis', 'ping pong']


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
    """Compute winRate, setWinRate, avgMargin, tightSetRate, form."""
    wins = 0; total = 0; form = []
    set_wins = 0; set_total = 0
    pt_margins = []  # очки в каждом сете
    tight_wins = 0; tight_total = 0

    for ev in events[:30]:
        home_id = (ev.get('homeTeam') or {}).get('id')
        away_id = (ev.get('awayTeam') or {}).get('id')
        wc = ev.get('winnerCode')
        if wc not in (1, 2): continue
        is_home = (home_id == player_id)
        is_away = (away_id == player_id)
        if not is_home and not is_away: continue

        player_won = (is_home and wc == 1) or (is_away and wc == 2)
        total += 1
        wins += 1 if player_won else 0
        form.append('W' if player_won else 'L')

        # Per-set analysis (period1..period5)
        hs = ev.get('homeScore') or {}
        as_ = ev.get('awayScore') or {}
        for period in ('period1', 'period2', 'period3', 'period4', 'period5'):
            hp = hs.get(period); ap = as_.get(period)
            if hp is None or ap is None: break
            if hp + ap == 0: break
            set_total += 1
            p_won = (is_home and hp > ap) or (is_away and ap > hp)
            if p_won: set_wins += 1
            margin = abs(hp - ap)
            pt_margins.append(margin)
            if margin <= 2:
                tight_total += 1
                if p_won: tight_wins += 1

    return {
        'winRate':      round(wins / total, 3) if total else 0.5,
        'setWinRate':   round(set_wins / set_total, 3) if set_total >= 3 else None,
        'avgMargin':    round(sum(pt_margins) / len(pt_margins), 1) if pt_margins else None,
        'tightSetRate': round(tight_wins / tight_total, 3) if tight_total >= 3 else None,
        'matches':      total,
        'wins':         wins,
        'form':         form[:5],
    }


# ── Self-built player database (accumulates from Leon match results) ──────────
# Stored in memory; grows as matches complete. Survives server restarts via PLAYER_DB.

PLAYER_DB   = {}   # {norm_name: {wins, losses, sets_won, sets_lost, recent:[W/L], opp:{name:[w,l]}}}
_DB_LOCK    = threading.Lock()


def _norm(name):
    return _re.sub(r'\s+', ' ', name.strip().lower())


def _elo_get(name):
    nm = _norm(name)
    if nm not in _ELO_DB:
        # Seed from external ratings if available (better than default 1500)
        ext = _EXT_RATING_DB.get(nm)
        if ext:
            seeded = ELO_DEF + max(-300, min(300, (ext - 1500)))
            with _ELO_LOCK:
                _ELO_DB[nm] = seeded
    return _ELO_DB.get(nm, ELO_DEF)

def _elo_expected(r1, r2):
    return 1.0 / (1 + 10 ** ((r2 - r1) / 400))

def _elo_update(winner, loser):
    rw, rl = _elo_get(winner), _elo_get(loser)
    e = _elo_expected(rw, rl)
    with _ELO_LOCK:
        _ELO_DB[_norm(winner)] = round(rw + ELO_K * (1 - e), 1)
        _ELO_DB[_norm(loser)]  = round(rl + ELO_K * (0 - (1 - e)), 1)

def _pat_key(h_sets, a_sets, pt_diff):
    diff_b = max(-4, min(4, round(pt_diff / 2) * 2))
    return f'{h_sets}:{a_sets}|{diff_b}'

def _pat_record(h_sets, a_sets, pt_diff, home_won):
    key = _pat_key(h_sets, a_sets, pt_diff)
    with _ELO_LOCK:
        if key not in _PAT_DB: _PAT_DB[key] = [0, 0]
        _PAT_DB[key][0 if home_won else 1] += 1

def _pat_prob(h_sets, a_sets, pt_diff):
    key = _pat_key(h_sets, a_sets, pt_diff)
    c = _PAT_DB.get(key)
    if not c or sum(c) < 5: return None
    t = sum(c)
    return {'homeProb': round(c[0] / t, 3), 'total': t, 'key': key}


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
    winner = home_name if home_won else away_name
    loser  = away_name if home_won else home_name
    _elo_update(winner, loser)
    ph = home_sets - (1 if home_won else 0)
    pa = away_sets - (0 if home_won else 1)
    if ph >= 0 and pa >= 0:
        _pat_record(ph, pa, 0, home_won)


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
    """Stats from our self-built database (Leon results) + cached external H2H."""
    p1 = _db_stats(p1_name)
    p2 = _db_stats(p2_name)
    h2h = None
    hn, an = _norm(p1_name), _norm(p2_name)
    d = PLAYER_DB.get(hn, {})
    opp = d.get('opp', {}).get(an)
    if opp and sum(opp) > 0:
        h2h = {'p1Wins': opp[0], 'p2Wins': opp[1], 'total': sum(opp), 'source': 'leon'}
    # Merge in external H2H if local has <3 meetings
    if (not h2h or h2h['total'] < 3) and _HAS_BS4:
        ext_key = _h2h_ext_key(p1_name, p2_name)
        with _H2H_EXT_LOCK:
            ext = _H2H_EXT_CACHE.get(ext_key)
        if ext and ext.get('total', 0) > 0:
            if not h2h:
                h2h = ext
            elif ext['total'] > h2h['total']:
                h2h = ext  # prefer richer external record
    r1 = round(_elo_get(p1_name))
    r2 = round(_elo_get(p2_name))
    ext_r1 = _EXT_RATING_DB.get(hn)
    ext_r2 = _EXT_RATING_DB.get(an)
    return {
        'p1': p1, 'p2': p2, 'h2h': h2h,
        'source': 'leon-local', 'dbSize': len(PLAYER_DB),
        'elo': {'p1': r1, 'p2': r2, 'homeProb': round(_elo_expected(r1, r2), 3),
                'p1Name': p1_name, 'p2Name': p2_name},
        'extRating': {'p1': ext_r1, 'p2': ext_r2} if (ext_r1 or ext_r2) else None,
    }


# ── Neural Network ────────────────────────────────────────────────────────────

def _extract_features(ev):
    """12-feature normalised vector from a parsed TT event dict.
    Base 8 features + Elo diff + Elo strength + home/away win-rate delta."""
    hs  = float(ev.get('homeSets', 0))
    aws = float(ev.get('awaySets', 0))
    clh = float(ev.get('currentHomePts', 0))
    cla = float(ev.get('currentAwayPts', 0))
    w1  = float(ev.get('w1Odds') or 0)
    w2  = float(ev.get('w2Odds') or 0)
    # Elo features (GIL-safe dict reads)
    hn     = _norm(ev.get('homeTeam', ''))
    an     = _norm(ev.get('awayTeam', ''))
    elo_h  = _ELO_DB.get(hn, ELO_DEF)
    elo_a  = _ELO_DB.get(an, ELO_DEF)
    elo_d  = max(-1.5, min(1.5, (elo_h - elo_a) / 200.0))
    elo_s  = max(-1.5, min(1.5, (elo_h - ELO_DEF) / 150.0))
    # Player win-rate features
    ph     = PLAYER_DB.get(hn, {})
    pa     = PLAYER_DB.get(an, {})
    tot_h  = max(1, ph.get('wins', 0) + ph.get('losses', 0))
    tot_a  = max(1, pa.get('wins', 0) + pa.get('losses', 0))
    wr_h   = max(-0.5, min(0.5, ph.get('wins', 0) / tot_h - 0.5))
    wr_a   = max(-0.5, min(0.5, pa.get('wins', 0) / tot_a - 0.5))
    return [
        math.log(w2 / w1) if w1 > 1.01 and w2 > 1.01 else 0.0,   # log-odds (market)
        (hs  - aws) / 3.0,                                          # set lead
        (clh - cla) / 10.0,                                         # point lead
        (hs  + aws) / 5.0,                                          # match progress
        (clh + cla) / 20.0,                                         # set progress
        (1.0/w1 - 1.0/w2) if w1 > 1 and w2 > 1 else 0.0,          # implied prob diff
        1.0 if hs > aws else (-1.0 if aws > hs else 0.0),           # set leader sign
        1.0 if w1 < w2 else (-1.0 if w2 < w1 else 0.0),            # odds leader sign
        elo_d,                                                        # elo difference
        elo_s,                                                        # home elo strength
        wr_h,                                                         # home win-rate delta
        wr_a,                                                         # away win-rate delta
    ]


class TinyNN:
    """Compact 2-hidden-layer MLP for TT match outcome prediction."""

    def __init__(self, n_in=NN_N_IN, n_h1=20, n_h2=12):
        if not _HAS_NP:
            raise RuntimeError('numpy not available')
        s = 0.3
        self.W1 = (_np.random.randn(n_h1, n_in) * s).astype(float)
        self.b1 = _np.zeros(n_h1)
        self.W2 = (_np.random.randn(n_h2, n_h1) * s).astype(float)
        self.b2 = _np.zeros(n_h2)
        self.W3 = (_np.random.randn(1, n_h2) * s).astype(float)
        self.b3 = _np.zeros(1)

    @staticmethod
    def _relu(x): return _np.maximum(0.0, x)
    @staticmethod
    def _sig(x):  return 1.0 / (1.0 + _np.exp(-_np.clip(x, -20, 20)))

    def _fwd(self, X):
        h1  = self._relu(X @ self.W1.T + self.b1)
        h2  = self._relu(h1 @ self.W2.T + self.b2)
        out = self._sig(h2 @ self.W3.T + self.b3).ravel()
        return out, h1, h2

    def predict(self, x):
        return float(self._fwd(_np.array(x, float).reshape(1, -1))[0][0])

    def train(self, X, y, epochs=600, lr=0.012, lam=1e-4):
        X = _np.array(X, float); y = _np.array(y, float)
        n, bs = len(X), max(16, len(X) // 8)
        for _ in range(epochs):
            idx = _np.random.permutation(n)
            for i in range(0, n, bs):
                xb = X[idx[i:i+bs]]; yb = y[idx[i:i+bs]]
                p, h1, h2 = self._fwd(xb)
                d3 = ((p - yb) / len(xb)).reshape(-1, 1)
                dW3 = d3.T @ h2 + lam * self.W3; db3 = d3.sum(0)
                d2  = (d3 @ self.W3) * (h2 > 0)
                dW2 = d2.T @ h1   + lam * self.W2; db2 = d2.sum(0)
                d1  = (d2 @ self.W2) * (h1 > 0)
                dW1 = d1.T @ xb   + lam * self.W1; db1 = d1.sum(0)
                self.W3 -= lr * dW3; self.b3 -= lr * db3
                self.W2 -= lr * dW2; self.b2 -= lr * db2
                self.W1 -= lr * dW1; self.b1 -= lr * db1
            lr *= 0.997
        p_all = self._fwd(X)[0]
        acc  = float(_np.mean((p_all > 0.5) == (y > 0.5)))
        loss = float(-_np.mean(y * _np.log(p_all + 1e-9) + (1-y) * _np.log(1-p_all + 1e-9)))
        return {'acc': round(acc, 3), 'loss': round(loss, 4), 'n': n}

    def save(self):
        return {k: getattr(self, k).tolist() for k in ('W1', 'b1', 'W2', 'b2', 'W3', 'b3')}

    @classmethod
    def from_dict(cls, d):
        obj = object.__new__(cls)
        for k, v in d.items():
            setattr(obj, k, _np.array(v, float))
        return obj


def _nn_load():
    global _NN_MODEL
    if not _HAS_NP:
        return
    try:
        if os.path.exists(_NN_WEIGHTS_FILE):
            with open(_NN_WEIGHTS_FILE) as f:
                _NN_MODEL = TinyNN.from_dict(json.load(f))
            print(f'[nn] Weights loaded from disk ({_NN_WEIGHTS_FILE})')
    except Exception as ex:
        print(f'[nn-load] {ex}')


def _elo_save():
    try:
        with open(_ELO_FILE, 'w') as f:
            json.dump(_ELO_DB, f, ensure_ascii=False)
    except Exception as ex:
        print(f'[elo-save] {ex}')

def _elo_load():
    global _ELO_DB
    try:
        if os.path.exists(_ELO_FILE):
            with open(_ELO_FILE) as f:
                data = json.load(f)
            with _ELO_LOCK:
                _ELO_DB.update(data)
            print(f'[elo] Loaded {len(_ELO_DB)} ratings from disk')
    except Exception as ex:
        print(f'[elo-load] {ex}')

def _pat_save():
    try:
        with open(_PAT_FILE, 'w') as f:
            json.dump(_PAT_DB, f, ensure_ascii=False)
    except Exception as ex:
        print(f'[pat-save] {ex}')

def _pat_load():
    global _PAT_DB
    try:
        if os.path.exists(_PAT_FILE):
            with open(_PAT_FILE) as f:
                data = json.load(f)
            with _ELO_LOCK:
                _PAT_DB.update({k: v for k, v in data.items() if isinstance(v, list) and len(v) == 2})
            print(f'[pat] Loaded {len(_PAT_DB)} patterns from disk')
    except Exception as ex:
        print(f'[pat-load] {ex}')

def _player_db_save():
    try:
        with open(_PLYR_FILE, 'w') as f:
            json.dump(PLAYER_DB, f, ensure_ascii=False)
    except Exception as ex:
        print(f'[plyr-save] {ex}')

def _player_db_load():
    global PLAYER_DB
    try:
        if os.path.exists(_PLYR_FILE):
            with open(_PLYR_FILE) as f:
                data = json.load(f)
            with _DB_LOCK:
                PLAYER_DB.update(data)
            print(f'[plyr] Loaded {len(PLAYER_DB)} players from disk')
    except Exception as ex:
        print(f'[plyr-load] {ex}')

def _periodic_save():
    """Background thread: saves all DBs every 5 minutes."""
    while True:
        time.sleep(300)
        _elo_save()
        _pat_save()
        _player_db_save()

def _nn_maybe_train():
    global _NN_LAST_TRAIN
    if not _HAS_NP:
        return
    now = time.time()
    with _NN_LOCK:
        if now - _NN_LAST_TRAIN < NN_RETRAIN_INT:
            return
        data = list(_NN_DATA)
    if len(data) < NN_MIN_SAMPLES:
        return

    def _train():
        global _NN_MODEL, _NN_LAST_TRAIN
        print(f'[nn] Training on {len(data)} samples...')
        try:
            X = [d[0] for d in data]
            y = [d[1] for d in data]
            model = TinyNN()
            m = model.train(X, y)
            try:
                with open(_NN_WEIGHTS_FILE, 'w') as f:
                    json.dump(model.save(), f)
            except Exception as ex:
                print(f'[nn-save] {ex}')
            with _NN_LOCK:
                _NN_MODEL      = model
                _NN_LAST_TRAIN = time.time()
            print(f'[nn] Done — acc={m["acc"]:.1%}  loss={m["loss"]:.4f}  n={m["n"]}')
        except Exception as ex:
            print(f'[nn-train] {ex}')

    threading.Thread(target=_train, daemon=True).start()


def nn_predict(features):
    """Return home-win probability from NN, or None if model not ready."""
    with _NN_LOCK:
        model = _NN_MODEL
    if model is None:
        return None
    try:
        return max(0.05, min(0.95, model.predict(features)))
    except Exception:
        return None


def record_nn_sample(match_id, home_won):
    """Pair live features captured earlier with the final match outcome."""
    with _NN_LOCK:
        feats = _MATCH_SEEN.pop(str(match_id), None)
    if feats is None:
        return
    with _NN_LOCK:
        _NN_DATA.append((feats, 1.0 if home_won else 0.0))
        if len(_NN_DATA) > 3000:
            _NN_DATA[:] = _NN_DATA[-3000:]
    _nn_maybe_train()


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


# ── External Scraping (BeautifulSoup4) ───────────────────────────────────────

_H2H_EXT_CACHE = {}   # {norm_key: {p1Wins, p2Wins, total, source, ts}}
_H2H_EXT_LOCK  = threading.Lock()
_EXT_RATING_DB = {}   # {norm_name: int_rating}  from external sources
_EXT_RATING_TS = 0
H2H_EXT_TTL    = 3600 * 6   # 6 h
RATING_TTL     = 3600 * 12  # 12 h


def _bs4_get(url, timeout=10, extra_headers=None):
    """Fetch URL, parse with BS4. Returns soup or None."""
    if not _HAS_BS4:
        return None
    try:
        hdrs = {
            'User-Agent': ('Mozilla/5.0 (Windows NT 10.0; Win64; x64) '
                           'AppleWebKit/537.36 (KHTML, like Gecko) '
                           'Chrome/124.0.0.0 Safari/537.36'),
            'Accept': 'text/html,application/xhtml+xml,*/*;q=0.8',
            'Accept-Language': 'ru-RU,ru;q=0.9,en;q=0.8',
        }
        if extra_headers:
            hdrs.update(extra_headers)
        req = urllib.request.Request(url, headers=hdrs)
        with urllib.request.urlopen(req, context=SSL_CTX, timeout=timeout) as r:
            html = r.read().decode('utf-8', errors='replace')
        return BeautifulSoup(html, 'lxml')
    except Exception as ex:
        print(f'[bs4] {url[:60]}: {ex}')
        return None


def _h2h_ext_key(p1, p2):
    a, b = sorted([_norm(p1), _norm(p2)])
    return f'{a}|{b}'


def _scrape_betexplorer_h2h(p1_name, p2_name):
    """H2H from betexplorer.com/table-tennis — static server-rendered HTML."""
    try:
        q1 = urllib.parse.quote(p1_name)
        q2 = urllib.parse.quote(p2_name)
        # Search for match H2H on betexplorer
        url = f'https://www.betexplorer.com/table-tennis/search/?q={q1}+{q2}'
        soup = _bs4_get(url, timeout=8)
        if not soup:
            return None
        text = soup.get_text(' ', strip=True)
        # Try to extract win counts from any pattern like "5-3" or "5 : 3"
        m = _re.search(r'\b(\d{1,2})\s*[-:]\s*(\d{1,2})\b', text[:2000])
        if m:
            w1, w2 = int(m.group(1)), int(m.group(2))
            if 1 <= w1 + w2 <= 50:
                return {'p1Wins': w1, 'p2Wins': w2, 'total': w1 + w2, 'source': 'betexplorer'}
    except Exception as ex:
        print(f'[h2h-bex] {ex}')
    return None


def _scrape_mytabletennis_h2h(p1_name, p2_name):
    """H2H from mytabletennis.net player search + H2H page."""
    try:
        def _find_id(name):
            q = urllib.parse.quote(name.strip())
            soup = _bs4_get(f'https://www.mytabletennis.net/search/players/?q={q}', timeout=8)
            if not soup:
                return None
            for a in soup.find_all('a', href=True):
                m = _re.search(r'/events/player/(\d+)', a['href'])
                if m:
                    return m.group(1)
            return None

        id1 = _find_id(p1_name)
        id2 = _find_id(p2_name)
        if not id1 or not id2:
            return None
        soup = _bs4_get(f'https://www.mytabletennis.net/events/h2h/{id1}/{id2}/', timeout=8)
        if not soup:
            return None
        text = soup.get_text(' ', strip=True)
        m = _re.search(r'(\d+)\s*[-:]\s*(\d+)', text[:1000])
        if m:
            w1, w2 = int(m.group(1)), int(m.group(2))
            if 1 <= w1 + w2 <= 100:
                return {'p1Wins': w1, 'p2Wins': w2, 'total': w1 + w2, 'source': 'mytabletennis'}
    except Exception as ex:
        print(f'[h2h-mtt] {ex}')
    return None


def get_h2h_external(p1_name, p2_name):
    """Get H2H from external scrapers. Cached 6h. Never raises."""
    key = _h2h_ext_key(p1_name, p2_name)
    now = time.time()
    with _H2H_EXT_LOCK:
        c = _H2H_EXT_CACHE.get(key)
        if c and now - c.get('ts', 0) < H2H_EXT_TTL:
            return c
    result = None
    for fn in (_scrape_mytabletennis_h2h, _scrape_betexplorer_h2h):
        try:
            r = fn(p1_name, p2_name)
            if r:
                result = r
                break
        except Exception:
            continue
    if result:
        result['ts'] = now
        with _H2H_EXT_LOCK:
            _H2H_EXT_CACHE[key] = result
    return result


def _scrape_tt_ratings_setka():
    """
    Scrape Setka Cup standings to seed _EXT_RATING_DB with real player ranks.
    Setka Cup HTML pages have static tables with player names + stats.
    """
    global _EXT_RATING_TS
    now = time.time()
    if now - _EXT_RATING_TS < RATING_TTL:
        return
    urls = [
        'https://setka-cup.com/en/standings',
        'https://setka-cup.com/standings',
        'https://setka-cup.com/players',
    ]
    found = 0
    for url in urls:
        soup = _bs4_get(url, timeout=12)
        if not soup:
            continue
        # Look for table rows with player name + numeric rank/rating
        for row in soup.find_all('tr'):
            cells = row.find_all(['td', 'th'])
            if len(cells) < 3:
                continue
            name_cell = cells[1] if len(cells) > 1 else cells[0]
            name = name_cell.get_text(strip=True)
            if not name or len(name) < 3:
                continue
            # Try to find a numeric rating/points in subsequent cells
            for cell in cells[2:]:
                t = cell.get_text(strip=True)
                if _re.match(r'^\d{3,5}$', t):
                    rating = int(t)
                    if 100 <= rating <= 9999:
                        _EXT_RATING_DB[_norm(name)] = rating
                        found += 1
                        break
        if found > 5:
            break
    if found:
        _EXT_RATING_TS = now
        print(f'[ratings] Loaded {found} external ratings from Setka')


def _scrape_tt_ratings_ttdaily():
    """Scrape tt-daily.ru for Russian TT player ratings."""
    global _EXT_RATING_TS
    now = time.time()
    if now - _EXT_RATING_TS < RATING_TTL:
        return
    soup = _bs4_get('https://tt-daily.ru/ratings/', timeout=12)
    if not soup:
        return
    found = 0
    for row in soup.find_all('tr'):
        cells = row.find_all(['td', 'th'])
        if len(cells) < 2:
            continue
        for i, cell in enumerate(cells):
            t = cell.get_text(strip=True)
            if _re.match(r'^\d{3,5}$', t) and i > 0:
                name = cells[i - 1].get_text(strip=True)
                if name and len(name) > 2:
                    _EXT_RATING_DB[_norm(name)] = int(t)
                    found += 1
    if found:
        _EXT_RATING_TS = now
        print(f'[ratings] Loaded {found} ratings from tt-daily.ru')


def get_ext_rating(player_name):
    """Return external rating for player, or None."""
    return _EXT_RATING_DB.get(_norm(player_name))


# ── Football Team Statistics (SofaScore) ─────────────────────────────────────

_FOOTBALL_TEAM_CACHE = {}
_FOOTBALL_TEAM_LOCK  = threading.Lock()
FOOTBALL_TEAM_TTL    = 3600 * 4  # 4 hours


def _search_football_team_sofa(name):
    """Search SofaScore for a football team by name."""
    q = urllib.parse.quote(name.strip())
    try:
        data = sofa_json(f'https://api.sofascore.com/api/v1/search/all/?q={q}&page=0')
        teams = data.get('teams', [])
        # Prefer football teams
        for item in teams:
            t = item.get('team', {})
            if (t.get('sport') or {}).get('slug') == 'football':
                return t.get('id')
        if teams:
            return (teams[0].get('team') or {}).get('id')
    except Exception as ex:
        print(f'[sofa-fbteam] {ex}')
    return None


def _get_team_events_sofa(team_id, pages=2):
    """Fetch last matches for a team from SofaScore."""
    all_events = []
    for page in range(pages):
        try:
            data = sofa_json(f'https://api.sofascore.com/api/v1/team/{team_id}/events/last/{page}')
            evs = data.get('events', [])
            if not evs:
                break
            all_events.extend(evs)
        except Exception:
            break
    return all_events


def _compute_football_team_stats(events, team_id):
    """Compute form + goal averages for a football team from SofaScore events."""
    wins = draws = losses = 0
    goals_for = goals_against = 0
    form = []
    total = 0
    for ev in events[:12]:
        ht = (ev.get('homeTeam') or {}).get('id')
        at = (ev.get('awayTeam') or {}).get('id')
        wc = ev.get('winnerCode')   # 1=home wins, 2=away wins, 3=draw
        hs_sc = ev.get('homeScore') or {}
        as_sc = ev.get('awayScore') or {}
        hg = hs_sc.get('current') or hs_sc.get('normaltime') or 0
        ag = as_sc.get('current') or as_sc.get('normaltime') or 0
        is_home = (ht == team_id)
        is_away = (at == team_id)
        if not is_home and not is_away:
            continue
        total += 1
        my_g   = hg if is_home else ag
        opp_g  = ag if is_home else hg
        goals_for     += my_g
        goals_against += opp_g
        if wc == 3:
            draws += 1; form.append('D')
        elif (wc == 1 and is_home) or (wc == 2 and is_away):
            wins += 1; form.append('W')
        elif wc in (1, 2):
            losses += 1; form.append('L')
    if total == 0:
        return None
    return {
        'wins': wins, 'draws': draws, 'losses': losses, 'matches': total,
        'avgFor':     round(goals_for     / total, 2),
        'avgAgainst': round(goals_against / total, 2),
        'winRate':    round(wins / total, 3),
        'form':       form[:5],
    }


def get_football_team_stats(home_name, away_name):
    """Return form + goal stats for both football teams. Cached 4h."""
    now = time.time()
    key = (home_name.lower().strip(), away_name.lower().strip())
    with _FOOTBALL_TEAM_LOCK:
        c = _FOOTBALL_TEAM_CACHE.get(key)
        if c and now - c['ts'] < FOOTBALL_TEAM_TTL:
            return c['data']

    result = {'home': None, 'away': None, 'h2h': None}
    try:
        h_id = _search_football_team_sofa(home_name)
        a_id = _search_football_team_sofa(away_name)
        if h_id:
            evs_h = _get_team_events_sofa(h_id)
            result['home'] = _compute_football_team_stats(evs_h, h_id)
            if a_id:
                h2h_h = h2h_a = 0
                for ev in evs_h:
                    ht2 = (ev.get('homeTeam') or {}).get('id')
                    at2 = (ev.get('awayTeam') or {}).get('id')
                    wc2 = ev.get('winnerCode')
                    if {ht2, at2} == {h_id, a_id} and wc2 in (1, 2, 3):
                        if (wc2 == 1 and ht2 == h_id) or (wc2 == 2 and at2 == h_id):
                            h2h_h += 1
                        elif wc2 in (1, 2):
                            h2h_a += 1
                if h2h_h + h2h_a > 0:
                    result['h2h'] = {
                        'homeWins': h2h_h, 'awayWins': h2h_a,
                        'total': h2h_h + h2h_a, 'source': 'sofascore',
                    }
        if a_id:
            evs_a = _get_team_events_sofa(a_id)
            result['away'] = _compute_football_team_stats(evs_a, a_id)
    except Exception as ex:
        print(f'[football-stats] {ex}')

    with _FOOTBALL_TEAM_LOCK:
        _FOOTBALL_TEAM_CACHE[key] = {'data': result, 'ts': now}
    return result


def _pre_fetch_ratings():
    """Background thread: pre-load external ratings on startup."""
    time.sleep(15)  # wait for server to stabilise
    for fn in (_scrape_tt_ratings_setka, _scrape_tt_ratings_ttdaily):
        try:
            fn()
            if _EXT_RATING_DB:
                break
        except Exception as ex:
            print(f'[pre-fetch] {ex}')


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
                               any(kw in ln for kw in _VIRTUAL_KW)
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
        if 'фора по сетам' in mn and len(runners) == 2:
            # Предпочитаем линию ±1.5 (самую ликвидную); отбрасываем экзотику >±3.5
            cand_h = cand_a = cand_l = None
            for r in runners:
                n, p = r.get('name', '').strip(), r.get('price')
                if not p or p <= 1.0: continue
                hm = _re.search(r'([+-][\d.]+)', n)
                lv = float(hm.group(1)) if hm else None
                if n.startswith('1'): cand_h, cand_l = p, lv
                elif n.startswith('2'): cand_a = p
            if cand_h and cand_l is not None and abs(cand_l) <= 3.5:
                if hdp_l is None or abs(abs(cand_l) - 1.5) < abs(abs(hdp_l) - 1.5):
                    hdp_h, hdp_a, hdp_l = cand_h, cand_a, cand_l
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
    mid = str(ev.get('id', base.get('id', '')))
    result = {
        'id': mid, 'source': 'leon', 'sport': 'tt',
        'homeTeam': hn, 'awayTeam': an, 'tournament': lg or 'Настольный теннис',
        'homeSets': hs, 'awaySets': aws, 'sets': sets,
        'currentSetNum': csn, 'currentHomePts': clh, 'currentAwayPts': cla,
        'homeScore': hs, 'awayScore': aws, 'period': csn, 'periodLabel': f'Партия {csn}',
        'w1Odds': w1, 'w2Odds': w2, 'wxOdds': None,
        'totalOverOdds': to, 'totalUnderOdds': tu, 'totalLine': tl,
        'hdpHomeOdds': hh, 'hdpAwayOdds': ha, 'hdpLine': hl,
        'leonUrl': url, 'isLive': is_live, 'status': 'inprogress' if is_live else 'notstarted',
        'nnProb': None,
    }
    # Neural network: capture live features, record outcome when done
    if is_live and hs < 3 and aws < 3:
        feats = _extract_features(result)
        with _NN_LOCK:
            _MATCH_SEEN[mid] = feats
        nn_p = nn_predict(feats)
        result['nnProb'] = round(nn_p * 100, 1) if nn_p is not None else None
    if hs >= 3 or aws >= 3:
        record_tt_result(hn, an, hs, aws)
        record_nn_sample(mid, hs > aws)
    return result


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
        if 'фора по сетам' in mn and len(runners) == 2:
            cand_h = cand_a = cand_l = None
            for r in runners:
                n, p = r.get('name', '').strip(), r.get('price')
                if not p or p <= 1.0: continue
                hm = _re.search(r'([+-][\d.]+)', n)
                lv = float(hm.group(1)) if hm else None
                if n.startswith('1'): cand_h, cand_l = p, lv
                elif n.startswith('2'): cand_a = p
            if cand_h and cand_l is not None and abs(cand_l) <= 2.5:
                if hdp_l is None or abs(abs(cand_l) - 1.5) < abs(abs(hdp_l) - 1.5):
                    hdp_h, hdp_a, hdp_l = cand_h, cand_a, cand_l
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


# ── Groq AI Analysis ─────────────────────────────────────────────────────────

_AI_CACHE = {}
AI_TTL    = 120  # 2 min — матч живой, ситуация меняется


def groq_chat(prompt, max_tokens=320):
    """Вызов Groq API (Llama-3.3-70b-versatile)."""
    url  = 'https://api.groq.com/openai/v1/chat/completions'
    body = json.dumps({
        'model':      'llama-3.3-70b-versatile',
        'messages':   [{'role': 'user', 'content': prompt}],
        'max_tokens': max_tokens,
        'temperature': 0.35,
    }).encode('utf-8')
    req = urllib.request.Request(url, data=body, headers={
        'Authorization': f'Bearer {GROQ_API_KEY}',
        'Content-Type':  'application/json',
    }, method='POST')
    with urllib.request.urlopen(req, context=SSL_CTX, timeout=20) as r:
        return json.loads(r.read())['choices'][0]['message']['content'].strip()


def build_tt_prompt(p1, p2, score, homeProb, ev, w1, w2, stats):
    p1s = stats.get('p1') or {}
    p2s = stats.get('p2') or {}
    h2h = stats.get('h2h') or {}

    def fmt_player(name, st):
        if not st or st.get('matches', 0) < 3:
            return f'{name}: данных нет'
        wr  = f"{st['winRate']*100:.0f}%"
        frm = ''.join(st.get('form', []))
        swr = f" / сеты {st['setWinRate']*100:.0f}%" if st.get('setWinRate') else ''
        mgn = f" / ср.разрыв {st['avgMargin']:.1f}оч" if st.get('avgMargin') else ''
        return f'{name}: побед {wr}{swr}{mgn}, форма {frm}'

    h2h_str = (f"{h2h.get('p1Wins',0)}-{h2h.get('p2Wins',0)} из {h2h.get('total',0)}"
               f" [{h2h.get('source','local')}]"
               if h2h and h2h.get('total', 0) >= 2 else 'нет данных')
    ext = stats.get('extRating') or {}
    ext_str = ''
    if ext.get('p1') or ext.get('p2'):
        ext_str = f"\nВнешние рейтинги: {p1} = {ext.get('p1','?')}, {p2} = {ext.get('p2','?')}"

    elo_info = stats.get('elo') or {}
    elo_str = (f"\nElo рейтинги: {p1} = {elo_info.get('p1',1500)}, {p2} = {elo_info.get('p2',1500)}"
               f" (вер. по Elo: {elo_info.get('homeProb',0.5)*100:.0f}%)"
               if elo_info else '')

    return f"""Ты эксперт-аналитик ставок на настольный теннис. Проведи краткий анализ матча.

Матч: {p1} vs {p2}
Счёт по партиям: {score}
Котировки Леон: {p1} @ {w1 or '—'}, {p2} @ {w2 or '—'}

Статистика из архива:
- {fmt_player(p1, p1s)}
- {fmt_player(p2, p2s)}
- H2H ({p1} vs {p2}): {h2h_str}{ext_str}{elo_str}

Математическая модель: {p1} = {homeProb}%, EV ставки = {ev}%

Напиши КРАТКИЙ анализ (2–3 предложения) на русском. Выдели ключевой фактор.
Последняя строка ОБЯЗАТЕЛЬНО: ПРОГНОЗ: [имя победителя], УВЕРЕННОСТЬ: [ВЫСОКАЯ/СРЕДНЯЯ/НИЗКАЯ]"""


def _rule_analysis(p1, p2, homeProb, ev, stats):
    """Анализ без AI (запасной вариант)."""
    p1s = stats.get('p1') or {}
    p2s = stats.get('p2') or {}
    h2h = stats.get('h2h') or {}
    parts = []
    if p1s and p2s and p1s.get('matches', 0) >= 5 and p2s.get('matches', 0) >= 5:
        d = p1s['winRate'] - p2s['winRate']
        fav = p1 if d > 0 else p2
        if abs(d) >= 0.08:
            parts.append(f"По статистике побед фаворит — {fav} ({max(p1s['winRate'],p2s['winRate'])*100:.0f}% vs {min(p1s['winRate'],p2s['winRate'])*100:.0f}%).")
    if h2h and h2h.get('total', 0) >= 3:
        fav = p1 if h2h['p1Wins'] > h2h['p2Wins'] else p2
        parts.append(f"В личных встречах лидирует {fav} ({h2h['p1Wins']}:{h2h['p2Wins']}).")
    fav_name = p1 if homeProb > 50 else p2
    conf = 'ВЫСОКАЯ' if abs(homeProb-50) > 15 and ev > 4 else 'СРЕДНЯЯ' if abs(homeProb-50) > 8 else 'НИЗКАЯ'
    if not parts:
        parts.append(f"Математическая модель даёт {homeProb}% вероятности победы {fav_name} (EV {ev}%).")
    parts.append(f"ПРОГНОЗ: {fav_name}, УВЕРЕННОСТЬ: {conf}")
    return ' '.join(parts)


def build_football_prompt(p1, p2, score, period, minute, homeProb, ev, w1, wx, w2, stats=None):
    """AI prompt для футбольного матча со статистикой команд."""
    hs  = (stats or {}).get('home') or {}
    as_ = (stats or {}).get('away') or {}
    h2h = (stats or {}).get('h2h') or {}

    def fmt_team(name, st):
        if not st or st.get('matches', 0) < 3:
            return f'{name}: нет данных'
        frm = ''.join(st.get('form', []))
        return (f"{name}: {st['winRate']*100:.0f}% побед, форма {frm}, "
                f"голы {st['avgFor']:.1f} за/{st['avgAgainst']:.1f} против")

    h2h_str = (f"{h2h.get('homeWins',0)}–{h2h.get('awayWins',0)} из {h2h.get('total',0)} встреч"
               if h2h and h2h.get('total', 0) >= 1 else 'нет данных')
    min_str = f" {minute}'" if minute else ''
    return f"""Ты эксперт-аналитик ставок на футбол. Проведи краткий анализ матча в лайве.

Матч: {p1} vs {p2}
Счёт: {score} · {period}{min_str}
Котировки Леон: П1 @ {w1 or '—'}, Ничья @ {wx or '—'}, П2 @ {w2 or '—'}

Статистика команд (SofaScore):
- {fmt_team(p1, hs)}
- {fmt_team(p2, as_)}
- H2H ({p1} vs {p2}): {h2h_str}

Пуассон-модель (кросс-рынок): вероятность победы {p1} = {homeProb:.0f}%, EV = {ev:.1f}%

Напиши КРАТКИЙ анализ (2-3 предложения) на русском. Учти счёт, время, форму команд.
Последняя строка ОБЯЗАТЕЛЬНО: ПРОГНОЗ: [П1/П2/Ничья или Тотал/Фора], УВЕРЕННОСТЬ: [ВЫСОКАЯ/СРЕДНЯЯ/НИЗКАЯ]"""


def _rule_football_analysis(p1, p2, homeProb, ev, stats):
    """Правиловой анализ футбольного матча без AI."""
    hs  = (stats or {}).get('home') or {}
    as_ = (stats or {}).get('away') or {}
    h2h = (stats or {}).get('h2h') or {}
    parts = []
    if hs and as_ and hs.get('matches', 0) >= 3 and as_.get('matches', 0) >= 3:
        d = hs['winRate'] - as_['winRate']
        fav = p1 if d > 0 else p2
        if abs(d) >= 0.10:
            parts.append(f"По форме фаворит — {fav} ({max(hs['winRate'],as_['winRate'])*100:.0f}% vs {min(hs['winRate'],as_['winRate'])*100:.0f}% побед).")
    if h2h and h2h.get('total', 0) >= 2:
        fav = p1 if h2h['homeWins'] > h2h['awayWins'] else p2
        parts.append(f"H2H: лидирует {fav} ({h2h['homeWins']}:{h2h['awayWins']}).")
    fav_name = p1 if homeProb > 50 else p2
    conf = 'ВЫСОКАЯ' if abs(homeProb-50) > 12 and ev > 5 else 'СРЕДНЯЯ' if abs(homeProb-50) > 6 else 'НИЗКАЯ'
    if not parts:
        parts.append(f"Пуассон-модель: вероятность победы {fav_name} = {homeProb:.0f}% (EV {ev:.1f}%).")
    parts.append(f"ПРОГНОЗ: {fav_name}, УВЕРЕННОСТЬ: {conf}")
    return ' '.join(parts)


def get_ai_summary(signals):
    key = 'sum_' + '_'.join(s.get('match', '')[:12] for s in signals[:3])
    now = time.time()
    with _PLAYER_LOCK:
        c = _AI_CACHE.get(key)
        if c and now - c['ts'] < 60:
            return c['data']
    lines = []
    for i, s in enumerate(signals[:5], 1):
        ev_str = f"+{s['evPct']:.1f}" if s.get('evPct', 0) > 0 else f"{s.get('evPct', 0):.1f}"
        lines.append(f"{i}. {s.get('match','?')} → {s.get('label','?')} @{s.get('odds','?')} (EV {ev_str}%, {s.get('prob','?')}% вер.)")
    signals_text = '\n'.join(lines)
    if GROQ_API_KEY:
        try:
            prompt = (f"Ты аналитик ставок на спорт. Активные VALUE-сигналы прямо сейчас:\n\n"
                      f"{signals_text}\n\n"
                      f"Дай краткий обзор (3-4 предложения): какой сигнал самый перспективный, "
                      f"на что обратить внимание, есть ли риски. Будь конкретным.")
            text   = groq_chat(prompt)
            result = {'text': text, 'source': 'Llama-3.3-70b (Groq)', 'ok': True}
        except Exception as ex:
            print(f'[groq-summary] {ex}')
            best   = signals[0]
            result = {'text': f"Лучший сигнал: {best.get('label','?')} ({best.get('match','?')}), EV {best.get('evPct',0):.1f}%. Всего активных: {len(signals)}.",
                      'source': 'Правила', 'ok': True}
    else:
        best   = signals[0]
        result = {'text': f"Лучший сигнал: {best.get('label','?')} ({best.get('match','?')}), EV {best.get('evPct',0):.1f}%. Groq не настроен.",
                  'source': 'Правила', 'ok': True}
    with _PLAYER_LOCK:
        _AI_CACHE[key] = {'data': result, 'ts': now}
    return result


def get_ai_analysis(p1, p2, score, homeProb, ev, w1, w2, stats,
                    sport='tt', wx='', period='', minute=0):
    key = f'{p1}||{p2}||{score}||{sport}'
    now = time.time()
    with _PLAYER_LOCK:
        c = _AI_CACHE.get(key)
        if c and now - c['ts'] < AI_TTL:
            return c['data']

    if sport == 'football':
        # Fetch team stats if not already provided
        fb_stats = stats if (stats.get('home') or stats.get('away')) else {}
        if not fb_stats.get('home') and not fb_stats.get('away'):
            try:
                fb_stats = get_football_team_stats(p1, p2)
            except Exception:
                pass
        if GROQ_API_KEY:
            try:
                prompt = build_football_prompt(p1, p2, score, period, minute,
                                               homeProb, ev, w1, wx, w2, fb_stats)
                text   = groq_chat(prompt)
                result = {'text': text, 'source': 'Llama-3.3-70b (Groq)', 'ok': True}
            except Exception as ex:
                print(f'[groq-fb] {type(ex).__name__}: {ex}')
                result = {'text': _rule_football_analysis(p1, p2, homeProb, ev, fb_stats),
                          'source': 'Правила (Groq недоступен)', 'ok': True}
        else:
            result = {'text': _rule_football_analysis(p1, p2, homeProb, ev, fb_stats),
                      'source': 'Правила', 'ok': True}
    else:
        if GROQ_API_KEY:
            try:
                prompt = build_tt_prompt(p1, p2, score, homeProb, ev, w1, w2, stats)
                text   = groq_chat(prompt)
                result = {'text': text, 'source': 'Llama-3.3-70b (Groq)', 'ok': True}
            except Exception as ex:
                print(f'[groq-error] {type(ex).__name__}: {ex}')
                try:
                    rule_text = _rule_analysis(p1, p2, homeProb, ev, stats)
                except Exception as rex:
                    print(f'[rule-error] {rex}')
                    rule_text = f'Математическая модель: {p1} — {homeProb:.0f}% вероятность победы.'
                result = {'text': rule_text, 'source': 'Правила (Groq недоступен)', 'ok': True}
        else:
            try:
                rule_text = _rule_analysis(p1, p2, homeProb, ev, stats)
            except Exception as rex:
                print(f'[rule-error] {rex}')
                rule_text = f'Математическая модель: {p1} — {homeProb:.0f}% вероятность победы.'
            result = {'text': rule_text, 'source': 'Правила', 'ok': True}

    with _PLAYER_LOCK:
        _AI_CACHE[key] = {'data': result, 'ts': now}
    return result


# ── HTTP server ───────────────────────────────────────────────────────────────

BASE_DIR = os.path.dirname(os.path.abspath(__file__))


class Handler(SimpleHTTPRequestHandler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=BASE_DIR, **kwargs)

    def do_GET(self):
        if self.path.startswith('/api/live-stream'):
            self._sse_stream()
        elif self.path.startswith('/api/live'):
            self._api()
        elif self.path.startswith('/api/player-stats'):
            self._player_stats_api()
        elif self.path.startswith('/api/ai-summary'):
            self._ai_summary_api()
        elif self.path.startswith('/api/ai-analysis'):
            self._ai_api()
        elif self.path.startswith('/api/elo-stats'):
            self._elo_api()
        elif self.path.startswith('/api/nn-stats'):
            self._nn_stats_api()
        elif self.path.startswith('/api/h2h'):
            self._h2h_api()
        elif self.path.startswith('/api/football-stats'):
            self._football_stats_api()
        elif self.path == '/health':
            self.send_response(200)
            self.send_header('Content-Type', 'text/plain')
            self.end_headers()
            self.wfile.write(b'ok')
        else:
            super().do_GET()

    def _sse_stream(self):
        qs    = urllib.parse.parse_qs(urllib.parse.urlparse(self.path).query)
        sport = qs.get('sport', ['tt'])[0]
        if sport not in SPORTS:
            sport = 'tt'
        self.send_response(200)
        self.send_header('Content-Type',  'text/event-stream')
        self.send_header('Cache-Control', 'no-cache')
        self.send_header('Connection',    'keep-alive')
        self.send_header('Access-Control-Allow-Origin', '*')
        self.end_headers()
        def _push(res):
            payload = json.dumps({
                'events': res['events'], 'source': res['source'],
                'count':  len(res['events']), 'sport': sport,
                'ts':     int(time.time()),
            }, ensure_ascii=False)
            self.wfile.write(f'data: {payload}\n\n'.encode('utf-8'))
            self.wfile.flush()
        try:
            res     = get_sport_data(sport)
            _push(res)
            last_ts = res['ts']
            while True:
                time.sleep(4)
                self.wfile.write(b': ping\n\n')
                self.wfile.flush()
                res = get_sport_data(sport)
                if res['ts'] > last_ts:
                    _push(res)
                    last_ts = res['ts']
        except (BrokenPipeError, ConnectionResetError, OSError):
            pass
        except Exception as ex:
            print(f'[SSE] {ex}')

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

    def _ai_summary_api(self):
        try:
            qs       = urllib.parse.parse_qs(urllib.parse.urlparse(self.path).query)
            data_str = qs.get('data', ['[]'])[0]
            signals  = json.loads(urllib.parse.unquote(data_str))
            if not signals:
                self._json_resp(200, {'text': 'Нет сигналов для анализа', 'source': 'info'}); return
            result = get_ai_summary(signals)
            self._json_resp(200, result)
        except Exception as ex:
            print(f'[ai-summary] {ex}')
            self._json_resp(500, {'error': str(ex), 'text': 'Ошибка сервера', 'source': ''})

    def _ai_api(self):
        try:
            qs = urllib.parse.parse_qs(urllib.parse.urlparse(self.path).query)
            g  = lambda k, d='': qs.get(k, [d])[0].strip()
            p1 = g('p1'); p2 = g('p2')
            if not p1 or not p2:
                self._json_resp(400, {'error': 'p1 and p2 required'}); return
            score    = g('score', '0:0')
            homeProb = float(g('homeProb', '50'))
            ev_val   = float(g('ev', '0'))
            w1       = g('w1'); wx = g('wx'); w2 = g('w2')
            sport    = g('sport', 'tt')
            period   = g('period', '')
            minute   = int(g('minute', '0') or 0)
            if sport == 'football':
                stats = {}
            else:
                # TT: local stats first, fallback sofascore
                stats = get_local_player_stats(p1, p2)
                if not stats.get('p1') and not stats.get('p2'):
                    try:
                        sofa = get_player_stats(p1, p2)
                        if sofa.get('p1') or sofa.get('p2'):
                            stats = sofa
                    except Exception:
                        pass
            result = get_ai_analysis(p1, p2, score, homeProb, ev_val, w1, w2, stats,
                                     sport=sport, wx=wx, period=period, minute=minute)
            self._json_resp(200, {**result, 'groqEnabled': bool(GROQ_API_KEY)})
        except Exception as ex:
            print(f'[ai-api] {ex}')
            self._json_resp(500, {'error': str(ex), 'text': 'Ошибка AI-сервера', 'source': ''})

    def _football_stats_api(self):
        try:
            qs   = urllib.parse.parse_qs(urllib.parse.urlparse(self.path).query)
            home = qs.get('home', [''])[0].strip()
            away = qs.get('away', [''])[0].strip()
            if not home or not away:
                self._json_resp(400, {'error': 'home and away required'}); return
            result = get_football_team_stats(home, away)
            self._json_resp(200, result)
        except Exception as ex:
            self._json_resp(500, {'error': str(ex)})

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

    def _elo_api(self):
        try:
            qs  = urllib.parse.parse_qs(urllib.parse.urlparse(self.path).query)
            p1  = qs.get('p1', [''])[0].strip()
            p2  = qs.get('p2', [''])[0].strip()
            r1  = round(_elo_get(p1)) if p1 else ELO_DEF
            r2  = round(_elo_get(p2)) if p2 else ELO_DEF
            hs  = int(qs.get('hs', ['0'])[0])
            as_ = int(qs.get('as', ['0'])[0])
            hp  = int(qs.get('hp', ['0'])[0])
            ap  = int(qs.get('ap', ['0'])[0])
            pat = _pat_prob(hs, as_, hp - ap)
            self._json_resp(200, {
                'p1': {'name': p1, 'elo': r1},
                'p2': {'name': p2, 'elo': r2},
                'eloProb': round(_elo_expected(r1, r2), 3),
                'pattern': pat,
                'dbSize': len(_ELO_DB),
                'patternSize': len(_PAT_DB),
            })
        except Exception as ex:
            self._json_resp(500, {'error': str(ex)})

    def _nn_stats_api(self):
        try:
            with _NN_LOCK:
                samples = len(_NN_DATA)
                ready   = _NN_MODEL is not None
                last_t  = _NN_LAST_TRAIN
            self._json_resp(200, {
                'ready':      ready,
                'samples':    samples,
                'minSamples': NN_MIN_SAMPLES,
                'lastTrain':  int(last_t),
                'hasNumpy':   _HAS_NP,
            })
        except Exception as ex:
            self._json_resp(500, {'error': str(ex)})

    def _h2h_api(self):
        try:
            qs = urllib.parse.parse_qs(urllib.parse.urlparse(self.path).query)
            p1 = qs.get('p1', [''])[0].strip()
            p2 = qs.get('p2', [''])[0].strip()
            if not p1 or not p2:
                self._json_resp(400, {'error': 'p1 and p2 required'}); return
            # Local DB H2H first (instant)
            local = get_local_player_stats(p1, p2)
            h2h_local  = local.get('h2h')
            elo_data   = {'p1': local.get('elo', {}).get('p1', ELO_DEF),
                          'p2': local.get('elo', {}).get('p2', ELO_DEF)}
            ext_rating = {'p1': get_ext_rating(p1), 'p2': get_ext_rating(p2)}
            # External H2H in background thread — return cached if available
            h2h_ext = None
            with _H2H_EXT_LOCK:
                h2h_ext = _H2H_EXT_CACHE.get(_h2h_ext_key(p1, p2))
            if not h2h_ext:
                threading.Thread(target=get_h2h_external, args=(p1, p2), daemon=True).start()
            self._json_resp(200, {
                'p1': p1, 'p2': p2,
                'h2h_local':   h2h_local,
                'h2h_external': h2h_ext,
                'elo':         elo_data,
                'ext_rating':  ext_rating,
                'extRatingDB': len(_EXT_RATING_DB),
                'bs4':         _HAS_BS4,
            })
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
    _nn_load()
    _elo_load()
    _pat_load()
    _player_db_load()
    threading.Thread(target=_periodic_save, daemon=True).start()
    threading.Thread(target=_pre_fetch_ratings, daemon=True).start()
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