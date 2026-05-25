// ============================================================
// Sports Live Analyzer — App v11.0
// ============================================================

const SPORT_META = {
  tt:       { icon: '🏓', label: 'Н. Теннис', emptyIcon: '🏓', scoreLabel: 'партии' },
  football: { icon: '⚽', label: 'Футбол',    emptyIcon: '⚽', scoreLabel: 'голы'   },
  hockey:   { icon: '🏒', label: 'Хоккей',    emptyIcon: '🏒', scoreLabel: 'шайбы'  },
  tennis:   { icon: '🎾', label: 'Теннис',    emptyIcon: '🎾', scoreLabel: 'сеты'   },
};

// ── Stats (per-sport) ─────────────────────────────────────
const Stats = (() => {
  function _key(sport) { return `live_preds_v2_${sport}`; }

  function load(sport) {
    try { return JSON.parse(localStorage.getItem(_key(sport)) || '{"history":[],"pending":{}}'); }
    catch { return { history: [], pending: {} }; }
  }
  function save(sport, d) {
    try { localStorage.setItem(_key(sport), JSON.stringify(d)); } catch {}
  }

  function processRefresh(analyzed, sport) {
    const d = load(sport);
    const now = Date.now();

    for (const [key, pred] of Object.entries(d.pending)) {
      const cur = analyzed.find(m => m.id === pred.eventId);
      if (!cur) {
        if (now - pred.ts > 90000) delete d.pending[key];
        continue;
      }
      if (pred.tag === 'match') {
        const s = sport === 'tt' || sport === 'tennis';
        const won = s ? (cur.homeSets >= 3 || cur.homeSets >= cur.setsToWin)
                      : (cur.homeScore > cur.awayScore && cur.isLive === false);
        const done = s ? (cur.homeSets >= 3 || cur.awaySets >= 3)
                       : !cur.isLive;
        if (done) {
          const homeWon = s ? cur.homeSets > cur.awaySets : cur.homeScore > cur.awayScore;
          _settle(d, key, pred, homeWon === pred.predictedHome);
        }
      }
    }

    for (const m of analyzed) {
      if (!m.isLive) continue;
      for (const p of m.predictions) {
        if (p.signal !== 'high' && p.signal !== 'medium') continue;
        const key = `${m.id}_${p.tag}_${m.currentSetNum || 0}_${m.homeSets}_${m.awaySets}`;
        if (d.pending[key] || d.history.find(h => h.key === key)) continue;
        d.pending[key] = {
          key, eventId: m.id, homeTeam: m.homeTeam, awayTeam: m.awayTeam,
          tag: p.tag, signal: p.signal, label: p.label, market: p.market,
          odds: p.odds, stake: p.kelly.stake, evPct: p.evPct, prob: p.prob,
          predictedHome: p.predictedHome,
          homeSets: m.homeSets || 0, awaySets: m.awaySets || 0,
          setNum: m.currentSetNum || 0, ts: now,
        };
      }
    }

    for (const [key, pred] of Object.entries(d.pending)) {
      if (now - pred.ts > 600000) delete d.pending[key];
    }
    save(sport, d);
    return summary(d);
  }

  function _settle(d, key, pred, correct) {
    const profit = correct ? +(pred.stake * (pred.odds - 1)).toFixed(0) : -pred.stake;
    d.history.push({ ...pred, result: correct ? 'win' : 'loss', profit, resolvedTs: Date.now() });
    if (d.history.length > 200) d.history = d.history.slice(-200);
    delete d.pending[key];
  }

  function summary(d) {
    if (!d) return { wins: 0, losses: 0, profit: 0, roi: '0.0', pending: 0, total: 0, high: null, medium: null };
    const h   = d.history || [];
    const wins = h.filter(x => x.result === 'win').length;
    const loss = h.filter(x => x.result === 'loss').length;
    const prof = h.reduce((s, x) => s + (x.profit || 0), 0);
    const stk  = h.reduce((s, x) => s + (x.stake  || 0), 0);
    const roi  = stk > 0 ? (prof / stk * 100) : 0;
    const pend = Object.keys(d.pending || {}).length;
    const tier = sig => {
      const arr = h.filter(x => x.signal === sig);
      if (!arr.length) return null;
      const w = arr.filter(x => x.result === 'win').length;
      const l = arr.filter(x => x.result === 'loss').length;
      const p = arr.reduce((s, x) => s + (x.profit || 0), 0);
      const s = arr.reduce((s, x) => s + (x.stake  || 0), 0);
      return { wins: w, losses: l, profit: Math.round(p), roi: (s > 0 ? p/s*100 : 0).toFixed(1) };
    };
    return { wins, losses: loss, profit: Math.round(prof), roi: roi.toFixed(1),
             pending: pend, total: wins + loss, high: tier('high'), medium: tier('medium') };
  }

  function get(sport)   { return summary(load(sport)); }
  function reset(sport) { save(sport, { history: [], pending: {} }); }
  return { processRefresh, get, reset, load };
})();


// ── App ───────────────────────────────────────────────────
const App = (() => {
  const REFRESH_SEC = 25;
  let currentSport   = 'tt';
  let analyzed       = [];
  let countdownVal   = REFRESH_SEC;
  let countdownTimer = null;
  let isLoading      = false;
  let highlightedId  = null;
  const _historyCache  = {};   // { matchId: history_data }
  const _aiCache       = {};   // { matchId: ai_result }
  const _oddsHistory   = {};   // { matchId: { initial, current } }
  const _scoreTracker  = {};   // { matchId: { prevHomePts, prevAwayPts, prevTs, homeVel, awayVel, recentRun } }
  let _histFetchPending = false;
  const _notifiedKeys = new Set();
  let _prevStatProfit = null;
  let _notifsEnabled  = false;
  let _sse            = null;
  let _sseActive      = false;
  const _session      = { active: false, startTs: null, startProfit: null, startTotal: null };

  // ── Score velocity & runs tracking ───────────────────
  function updateScoreTracker(rawEvents) {
    const now = Date.now();
    for (const e of (rawEvents || [])) {
      if (!e.id || !e.isLive) continue;
      const hp = e.currentHomePts || 0;
      const ap = e.currentAwayPts || 0;
      const t  = _scoreTracker[e.id];
      if (!t) {
        _scoreTracker[e.id] = { prevHomePts: hp, prevAwayPts: ap, prevTs: now, homeVel: 0, awayVel: 0, recentRun: 0 };
        continue;
      }
      const dt = (now - t.prevTs) / 60000; // minutes
      if (dt >= 0.15) {
        const dh = Math.max(0, hp - t.prevHomePts);
        const da = Math.max(0, ap - t.prevAwayPts);
        if (dh + da > 0) {
          t.homeVel  = +(dh / dt).toFixed(1);
          t.awayVel  = +(da / dt).toFixed(1);
          t.recentRun = dh > da * 1.5 ? 1 : da > dh * 1.5 ? -1 : 0;
        }
        t.prevHomePts = hp;
        t.prevAwayPts = ap;
        t.prevTs      = now;
      }
    }
  }

  function getScoreData(matchId) { return _scoreTracker[matchId] || null; }

  // ── Уведомления браузера для HIGH сигналов ───────────
  function toggleNotifications() {
    const btn = document.getElementById('notif-btn');
    if (!('Notification' in window)) { alert('Уведомления не поддерживаются браузером'); return; }
    if (_notifsEnabled) {
      _notifsEnabled = false;
      if (btn) { btn.classList.remove('notif-on'); btn.title = 'Включить уведомления о HIGH сигналах'; }
      return;
    }
    if (Notification.permission === 'granted') {
      _notifsEnabled = true;
      if (btn) { btn.classList.add('notif-on'); btn.title = 'Уведомления включены — нажми чтобы выключить'; }
      return;
    }
    Notification.requestPermission().then(perm => {
      if (perm === 'granted') {
        _notifsEnabled = true;
        if (btn) { btn.classList.add('notif-on'); btn.title = 'Уведомления включены'; }
      }
    });
  }

  function _checkNotifications(list) {
    if (!_notifsEnabled || Notification.permission !== 'granted') return;
    for (const m of list) {
      if (!m.isLive) continue;
      for (const p of m.predictions) {
        if (p.signal !== 'high') continue;
        const key = `${m.id}_${p.tag}_${m.homeSets}_${m.awaySets}`;
        if (_notifiedKeys.has(key)) continue;
        _notifiedKeys.add(key);
        try {
          const evSign = p.evPct > 0 ? '+' : '';
          new Notification('🎯 HIGH VALUE — Sports Live', {
            body: `${m.homeTeam} vs ${m.awayTeam}\n${p.label} @ ${p.odds.toFixed(2)}\nEV ${evSign}${p.evPct.toFixed(1)}% · ${(p.prob*100).toFixed(0)}% вероятность`,
            tag: key,
          });
        } catch {}
      }
    }
  }

  // ── Odds movement tracking ────────────────────────────
  function updateOddsHistory(rawEvents) {
    for (const e of (rawEvents || [])) {
      if (!e.id || !e.w1Odds || !e.w2Odds) continue;
      const h = _oddsHistory[e.id];
      const entry = { w1: e.w1Odds, w2: e.w2Odds };
      if (!h) {
        _oddsHistory[e.id] = { initial: entry, current: entry, series: [entry] };
      } else {
        const last = h.series[h.series.length - 1];
        if (!last || last.w1 !== e.w1Odds || last.w2 !== e.w2Odds) {
          h.series.push(entry);
          if (h.series.length > 24) h.series = h.series.slice(-24);
        }
        h.current = entry;
      }
    }
  }

  function getOddsMovement(matchId) {
    const h = _oddsHistory[matchId];
    if (!h || !h.initial || h.initial.w1 === h.current.w1) return null;
    const w1Drift = +((h.initial.w1 - h.current.w1) / h.initial.w1 * 100).toFixed(1);
    const w2Drift = +((h.initial.w2 - h.current.w2) / h.initial.w2 * 100).toFixed(1);
    return {
      w1Drift, w2Drift,
      w1Initial: h.initial.w1, w2Initial: h.initial.w2,
      w1Steam: w1Drift >= 5,   // >=5% падение = умные деньги
      w2Steam: w2Drift >= 5,
    };
  }

  function _sparklineHtml(matchId) {
    const h = _oddsHistory[matchId];
    if (!h || !h.series || h.series.length < 3) return '';
    const vals = h.series.map(p => p.w1);
    const min = Math.min(...vals), max = Math.max(...vals);
    if (max - min < 0.02) return '';
    const W = 60, H = 18;
    const pts = vals.map((v, i) => {
      const x = ((i / (vals.length - 1)) * (W - 2) + 1).toFixed(1);
      const y = (H - 2 - ((v - min) / (max - min)) * (H - 4)).toFixed(1);
      return `${x},${y}`;
    }).join(' ');
    const clr = vals[vals.length-1] < vals[0] - 0.01 ? '#e74c3c'
              : vals[vals.length-1] > vals[0] + 0.01 ? '#2ecc71' : '#888';
    return `<svg class="spark-svg" width="${W}" height="${H}" viewBox="0 0 ${W} ${H}"><polyline points="${pts}" fill="none" stroke="${clr}" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round"/></svg>`;
  }

  // ── AI анализ по клику ────────────────────────────────
  async function loadAI(matchId, btn) {
    if (_aiCache[matchId]) { _showAI(matchId); return; }
    btn.textContent = '⏳ Анализирую...'; btn.disabled = true;
    const m = analyzed.find(x => x.id === matchId);
    if (!m) return;
    try {
      const p = new URLSearchParams({
        p1: m.homeTeam, p2: m.awayTeam,
        score: `${m.homeSets}:${m.awaySets}`,
        homeProb: m.matchWinHomeProb,
        ev: (m.topEV || 0).toFixed(1),
        w1: m.w1Odds || '', w2: m.w2Odds || '',
      });
      const res = await fetch(`/api/ai-analysis?${p}`, { cache: 'no-store' });
      _aiCache[matchId] = await res.json();
    } catch { /* ignore */ }
    btn.textContent = '🤖 AI анализ'; btn.disabled = false;
    _showAI(matchId);
  }

  function _showAI(matchId) {
    const el = document.getElementById(`ai-${matchId}`);
    const btn = document.getElementById(`aibtn-${matchId}`);
    const d = _aiCache[matchId];
    if (!el || !d) return;
    el.style.display = 'block';
    el.innerHTML = `<div class="ai-text">${esc(d.text || '—')}</div>
      <div class="ai-src">🤖 ${d.source || 'AI'}</div>`;
    if (btn) btn.style.display = 'none';
  }

  function getBankroll() {
    const v = parseInt(document.getElementById('bankroll-input')?.value || '1000');
    return Math.max(100, isNaN(v) ? 1000 : v);
  }

  // ── History background fetch ──────────────────────────
  async function fetchHistoryForMatches(matches) {
    if (_histFetchPending) return;
    _histFetchPending = true;
    const live     = matches.filter(m => m.isLive && m.sport === 'tt');
    const upcoming = matches.filter(m => !m.isLive && m.sport === 'tt' && m.w1Odds).slice(0, 8);
    let changed = false;
    await Promise.allSettled([...live, ...upcoming].map(async m => {
      if (_historyCache[m.id]) return; // already loaded
      try {
        const url = `/api/player-stats?p1=${encodeURIComponent(m.homeTeam)}&p2=${encodeURIComponent(m.awayTeam)}`;
        const res = await fetch(url, { cache: 'no-store' });
        if (!res.ok) return;
        const data = await res.json();
        if (!data.error) { _historyCache[m.id] = data; changed = true; }
      } catch { /* network error — ignore */ }
    }));
    _histFetchPending = false;
    if (changed) render();
  }

  // ── Сессионный трекер ─────────────────────────────────
  function toggleSession() {
    if (_session.active) {
      _session.active = false;
      try { localStorage.removeItem('session_state'); } catch {}
      _renderSessionBar(null);
    } else {
      const st = Stats.get(currentSport);
      _session.active      = true;
      _session.startTs     = Date.now();
      _session.startProfit = st.profit;
      _session.startTotal  = st.total;
      _saveSession();
      _renderSessionBar(st);
    }
    const btn = document.getElementById('session-btn');
    if (btn) btn.classList.toggle('session-on', _session.active);
  }

  function _renderSessionBar(stats) {
    const bar = document.getElementById('session-bar');
    if (!bar) return;
    if (!_session.active) { bar.style.display = 'none'; bar.innerHTML = ''; return; }
    const elapsed = Date.now() - _session.startTs;
    const mins    = Math.floor(elapsed / 60000);
    const dur     = mins >= 60 ? `${Math.floor(mins/60)}ч ${mins%60}м` : `${mins}м`;
    const pnl     = stats ? stats.profit - (_session.startProfit || 0) : 0;
    const bets    = stats ? stats.total  - (_session.startTotal  || 0) : 0;
    const pnlCls  = pnl >= 0 ? 'pnl-pos' : 'pnl-neg';
    bar.style.display = 'flex';
    bar.innerHTML = `
      <span class="sess-label">⏱ ${dur}</span>
      <span class="sess-sep">·</span>
      <span class="sess-bets">${bets} ставок</span>
      <span class="sess-sep">·</span>
      <span class="sess-pnl ${pnlCls}">${pnl >= 0 ? '+' : ''}${pnl}₽</span>
      <button class="sess-stop" onclick="App.toggleSession()">■ Стоп</button>
    `;
  }

  function _updateSession(stats) { if (_session.active) _renderSessionBar(stats); }

  function _saveSession() {
    try { localStorage.setItem('session_state', JSON.stringify({
      active: true, startTs: _session.startTs,
      startProfit: _session.startProfit, startTotal: _session.startTotal,
    })); } catch {}
  }

  function _loadSession() {
    try {
      const s = JSON.parse(localStorage.getItem('session_state') || 'null');
      if (!s || !s.active) return;
      Object.assign(_session, s);
      const btn = document.getElementById('session-btn');
      if (btn) btn.classList.add('session-on');
      _renderSessionBar(Stats.get(currentSport));
    } catch {}
  }

  // ── Sport tab switch ──────────────────────────────────
  function setSport(sport) {
    if (sport === currentSport) return;
    currentSport = sport;
    analyzed = [];
    highlightedId = null;
    // Clear history cache on sport switch
    Object.keys(_historyCache).forEach(k => delete _historyCache[k]);

    // Update tab UI
    document.querySelectorAll('.tab-btn').forEach(b => {
      b.classList.toggle('active', b.dataset.sport === sport);
    });

    // Update empty icon
    const meta = SPORT_META[sport] || SPORT_META.tt;
    document.getElementById('sport-empty-icon').textContent = meta.emptyIcon;

    // Reset stats bar for new sport
    updateStatsBar(Stats.get(sport));
    if (_sse) { _sse.close(); _sse = null; _sseActive = false; }
    refresh();
    _connectSSE();
  }

  // ── Shared data processing ────────────────────────────
  function _processData(data) {
    const bankroll = getBankroll();
    if (currentSport === 'tt') {
      updateOddsHistory(data.events);
      updateScoreTracker(data.events);
    }
    analyzed = (data.events || []).map(e => {
      if (e.sport === 'football' || e.sport === 'hockey' || e.sport === 'tennis')
        return SportsEngine.analyze(e, bankroll);
      return Engine.analyze(e, bankroll, _historyCache[e.id] || null, getOddsMovement(e.id), getScoreData(e.id));
    }).filter(Boolean);
    if (currentSport === 'tt') fetchHistoryForMatches(analyzed);
    const stats = Stats.processRefresh(analyzed, currentSport);
    updateStatsBar(stats);
    _updateSession(stats);
    if (_prevStatProfit !== null && stats.profit !== _prevStatProfit) {
      const delta = stats.profit - _prevStatProfit;
      const inp = document.getElementById('bankroll-input');
      if (inp) inp.value = Math.max(100, (parseInt(inp.value) || 1000) + delta);
    }
    _prevStatProfit = stats.profit;
    _updatePnlDelta(stats.profit);
    _checkNotifications(analyzed);
    const liveCount  = analyzed.filter(m => m.isLive).length;
    const valueCount = analyzed.filter(m =>
      m.predictions.some(p => p.signal === 'high' || p.signal === 'medium')
    ).length;
    document.getElementById('count-live').textContent  = liveCount;
    document.getElementById('count-value').textContent = valueCount;
    document.getElementById('last-update').textContent = new Date().toLocaleTimeString('ru');
    const srcEl = document.getElementById('data-source');
    if (srcEl) srcEl.textContent = data.source ? `Источник: ${data.source}` : '';
    setStatus(liveCount > 0 ? `${liveCount} лайв матчей` : `Нет лайв матчей`);
    render();
    if (_ladder.active && !_ladder.currentPick) _renderLadder();
  }

  // ── SSE real-time connection ──────────────────────────
  function _connectSSE() {
    if (typeof EventSource === 'undefined') return;
    if (_sse) { _sse.close(); _sse = null; }
    _sse = new EventSource(`/api/live-stream?sport=${currentSport}`);
    _sse.onopen = () => {
      _sseActive = true;
      clearInterval(countdownTimer);
      const tw = document.getElementById('timer-wrap');
      if (tw) tw.innerHTML = '<span class="sse-live-badge">🟢 Live</span>';
    };
    _sse.onmessage = ev => {
      try { _processData(JSON.parse(ev.data)); } catch {}
    };
    _sse.onerror = () => {
      if (!_sseActive) return;
      _sseActive = false;
      if (_sse) { _sse.close(); _sse = null; }
      const tw = document.getElementById('timer-wrap');
      if (tw) tw.innerHTML = `Обновление через <span id="countdown">${REFRESH_SEC}</span>с`;
      resetCountdown();
    };
  }

  // ── Refresh ───────────────────────────────────────────
  async function refresh() {
    if (isLoading) return;
    isLoading = true;
    const btn = document.getElementById('refresh-btn');
    if (btn) btn.classList.add('loading');
    setStatus('Получаю данные...');
    try {
      const data = await API.getLive(currentSport);
      _processData(data);
    } catch (e) {
      console.error(e);
      const isConn = e.message.includes('fetch') || e.message.includes('Failed');
      setStatus(isConn ? 'Сервер не запущен' : 'Ошибка', true);
      showError(isConn
        ? 'Сервер не запущен.<br>Запусти <strong>start.bat</strong>.'
        : e.message);
    } finally {
      isLoading = false;
      if (btn) btn.classList.remove('loading');
      if (!_sseActive) resetCountdown();
    }
  }

  // ── Best prediction ───────────────────────────────────
  function findBestPrediction() {
    let best = null, bestScore = -Infinity, bestMatch = null;
    for (const m of analyzed) {
      if (!m.isLive) continue;
      for (const p of m.predictions) {
        const sigBonus = p.signal === 'high' ? 1000 : p.signal === 'medium' ? 500 : 0;
        const score = sigBonus + p.evPct * 0.55 + (p.prob * 100) * 0.45;
        if (score > bestScore) { bestScore = score; best = p; bestMatch = m; }
      }
    }
    return best ? { pred: best, match: bestMatch } : null;
  }

  function showBestPrediction() {
    const result = findBestPrediction();
    const banner = document.getElementById('best-banner');
    if (!result) {
      if (banner) { banner.innerHTML = ''; banner.style.display = 'none'; }
      alert('Нет активных VALUE-прогнозов прямо сейчас');
      return;
    }
    const { pred, match } = result;
    const evSign   = pred.evPct > 0 ? '+' : '';
    const sigCls   = pred.signal === 'high' ? 'banner-high' : 'banner-med';
    const sigIcon  = pred.signal === 'high' ? '🎯' : pred.signal === 'medium' ? '📊' : '🔹';
    const sigTitle = pred.signal === 'high' ? 'ЛУЧШИЙ ПРОГНОЗ — HIGH VALUE'
                   : pred.signal === 'medium' ? 'ЛУЧШИЙ ПРОГНОЗ — VALUE'
                   : 'ЛУЧШИЙ ПРОГНОЗ СЕЙЧАС';
    banner.style.display = 'block';
    banner.innerHTML = `
      <div class="best-banner-inner ${sigCls}">
        <span class="best-icon">${sigIcon}</span>
        <div class="best-info">
          <span class="best-title">${sigTitle}</span>
          <span class="best-match">${esc(match.homeTeam)} vs ${esc(match.awayTeam)}</span>
          <span class="best-pred">${esc(pred.market)} — <strong>${esc(pred.label)}</strong></span>
          <span class="best-meta">
            ${(pred.prob*100).toFixed(0)}% вероятность · кф ${pred.odds.toFixed(2)} · EV ${evSign}${pred.evPct.toFixed(1)}%
            ${pred.kelly.stake > 0 ? `· Kelly: <strong>${pred.kelly.stake}₽</strong>` : ''}
          </span>
        </div>
        <button class="best-close" onclick="App.closeBestBanner()">✕</button>
      </div>`;
    highlightedId = match.id;
    render();
    setTimeout(() => {
      const card = document.querySelector(`[data-id="${match.id}"]`);
      if (card) card.scrollIntoView({ behavior: 'smooth', block: 'center' });
    }, 100);
  }

  function closeBestBanner() {
    const banner = document.getElementById('best-banner');
    if (banner) { banner.innerHTML = ''; banner.style.display = 'none'; }
    highlightedId = null;
    render();
  }

  // ── Stats bar ─────────────────────────────────────────
  function updateStatsBar(s) {
    const el = document.getElementById('stats-bar');
    if (!el) return;
    if (s.total === 0 && s.pending === 0) {
      el.innerHTML = '<span class="stats-hint">Статистика появится после первых прогнозов</span>';
      return;
    }
    const profCls = s.profit >= 0 ? 'sh-green' : 'sh-red';
    const roiCls  = parseFloat(s.roi) >= 0 ? 'sh-green' : 'sh-red';
    const tierHtml = (t, icon, cls) => !t ? '' :
      `<span class="stats-tier ${cls}">${icon} ${t.wins}✓/${t.losses}✗ <span class="${parseFloat(t.roi)>=0?'sh-green':'sh-red'}">ROI ${t.roi}%</span></span>`;
    el.innerHTML = `
      <span class="stats-label">Стат:</span>
      ${tierHtml(s.high, '🎯', 'tier-high')}
      ${tierHtml(s.medium, '📊', 'tier-med')}
      ${s.pending ? `<span class="stats-pill pend">${s.pending}⏳</span>` : ''}
      <span class="stats-sep">·</span>
      <span class="sh-val ${profCls}">${s.profit >= 0 ? '+' : ''}${s.profit}₽</span>
      <span class="stats-sep">·</span>
      <span class="sh-val ${roiCls}">ROI ${s.roi}%</span>
      <button class="stats-reset" onclick="App.resetStats()" title="Сбросить">↺</button>`;
  }

  function _updatePnlDelta(profit) {
    const el = document.getElementById('pnl-delta');
    if (!el) return;
    if (profit === 0) { el.textContent = ''; el.className = 'pnl-delta'; return; }
    const sign = profit > 0 ? '+' : '';
    el.textContent = `${sign}${profit}₽`;
    el.className = `pnl-delta ${profit > 0 ? 'pnl-pos' : 'pnl-neg'}`;
  }

  function resetStats() {
    if (!confirm('Сбросить статистику?')) return;
    Stats.reset(currentSport);
    _prevStatProfit = null;
    _updatePnlDelta(0);
    updateStatsBar(Stats.get(currentSport));
  }

  // ── Лесенка ───────────────────────────────────────────
  const _ladder = { active: false, balance: 0, target: 0, start: 0, history: [], currentPick: null, skipMatchId: null };

  function openLadder() {
    const panel = document.getElementById('ladder-panel');
    if (!panel) return;
    if (panel.style.display !== 'none') { panel.style.display = 'none'; return; }
    panel.style.display = 'block';
    if (_ladder.active) _renderLadder();
    else panel.innerHTML = _ladderSetupHtml();
  }

  function _ladderSetupHtml() {
    const cur = getBankroll();
    return `<div class="ladder-inner">
      <div class="ladder-header">
        <span class="ladder-title">🪜 Лесенка</span>
        <button class="ladder-close" onclick="App.closeLadder()">✕</button>
      </div>
      <div class="ladder-setup">
        <p class="lsetup-desc">Один прогноз за раз. Даю самый уверенный — ты сообщаешь результат — идём дальше.</p>
        <div class="lset-row">
          <label class="lset-lbl">Стартовый баланс</label>
          <div class="lset-inp-wrap">
            <input type="number" id="ld-balance" value="${cur}" min="100" step="50" class="lset-inp" />
            <span class="lset-cur">₽</span>
          </div>
        </div>
        <div class="lset-row">
          <label class="lset-lbl">Цель</label>
          <div class="lset-inp-wrap">
            <input type="number" id="ld-target" value="${cur * 3}" min="200" step="100" class="lset-inp" />
            <span class="lset-cur">₽</span>
          </div>
        </div>
        <button class="btn-ld-start" onclick="App.startLadder()">🚀 Запустить лесенку</button>
      </div>
    </div>`;
  }

  function startLadder() {
    const bal = parseInt(document.getElementById('ld-balance')?.value);
    const tgt = parseInt(document.getElementById('ld-target')?.value);
    if (!bal || !tgt || isNaN(bal) || isNaN(tgt)) return;
    if (tgt <= bal) { alert('Цель должна быть больше баланса'); return; }
    _ladder.active  = true;
    _ladder.balance = bal;
    _ladder.target  = tgt;
    _ladder.start   = bal;
    _ladder.history = [];
    _ladder.currentPick = null;
    _saveLadder();
    _renderLadder();
  }

  function _findBestForLadder() {
    // Keep current pick if the match is still live and signal holds
    if (_ladder.currentPick) {
      const cp = _ladder.currentPick;
      const m  = analyzed.find(x => x.id === cp.match.id && x.isLive);
      if (m) {
        const p = m.predictions.find(x => x.tag === cp.pred.tag && x.label === cp.pred.label);
        if (p && (p.signal === 'high' || p.signal === 'medium')) {
          return { pred: p, match: m, stake: cp.stake };
        }
      }
    }

    // Scan for best pick, excluding one match if requested
    function _scan(excludeId) {
      let best = null, bestScore = -Infinity, bestMatch = null;
      for (const sig of ['high', 'medium']) {
        for (const m of analyzed) {
          if (!m.isLive) continue;
          if (excludeId && m.id === excludeId) continue;
          for (const p of m.predictions) {
            if (p.signal !== sig) continue;
            const score = p.evPct * 0.45 + (p.prob * 100) * 0.35 + m.topConf * 0.20;
            if (score > bestScore) { bestScore = score; best = p; bestMatch = m; }
          }
        }
        if (best) break;
      }
      return best ? { pred: best, match: bestMatch } : null;
    }

    // Skip the last-settled/skipped match; fall back to including it if nothing else exists
    let found = _scan(_ladder.skipMatchId);
    if (!found && _ladder.skipMatchId) found = _scan(null);
    if (!found) return null;

    const b = found.pred.odds - 1;
    const q = 1 - found.pred.prob;
    const kellyRaw = Math.max(0, (b * found.pred.prob - q) / b);
    let stake = kellyRaw * 0.30 * _ladder.balance;
    stake = Math.min(stake, _ladder.balance * 0.25);
    stake = Math.max(50, Math.round(stake / 10) * 10);
    return { pred: found.pred, match: found.match, stake };
  }

  function changeLadderPick() {
    if (!_ladder.currentPick) return;
    _ladder.skipMatchId = _ladder.currentPick.match.id;
    _ladder.currentPick = null;
    _renderLadder();
  }

  function _renderLadder() {
    const panel = document.getElementById('ladder-panel');
    if (!panel || !_ladder.active) return;

    const wins    = _ladder.history.filter(h => h.won).length;
    const losses  = _ladder.history.filter(h => !h.won).length;
    const step    = _ladder.history.length + 1;
    const progPct = Math.min(100, Math.round(_ladder.balance / _ladder.target * 100));

    if (_ladder.balance <= 0) { panel.innerHTML = _ladderBustedHtml(wins, losses); return; }
    if (_ladder.balance >= _ladder.target) { panel.innerHTML = _ladderDoneHtml(wins, losses); return; }

    _ladder.currentPick = _findBestForLadder();
    const pick = _ladder.currentPick;

    panel.innerHTML = `<div class="ladder-inner">
      <div class="ladder-header">
        <span class="ladder-title">🪜 Лесенка — шаг ${step}</span>
        <button class="ladder-close" onclick="App.closeLadder()">✕</button>
      </div>
      <div class="ladder-progress">
        <div class="lp-amounts">
          <span class="lp-cur">${_ladder.balance.toLocaleString('ru')}₽</span>
          <span class="lp-of">из</span>
          <span class="lp-tgt">${_ladder.target.toLocaleString('ru')}₽</span>
          <span class="lp-left">осталось ${(_ladder.target - _ladder.balance).toLocaleString('ru')}₽</span>
        </div>
        <div class="lp-bar-wrap"><div class="lp-bar" style="width:${progPct}%"></div></div>
        <div class="lp-stats">✓ ${wins} побед · ✗ ${losses} поражений</div>
      </div>
      ${pick ? _ladderPickHtml(pick) : `<div class="ladder-wait">
        <div class="lw-icon">⏳</div>
        <div class="lw-msg">Нет уверенных прогнозов прямо сейчас.<br>Обновление через <span id="ld-cd">${countdownVal}</span>с</div>
      </div>`}
    </div>`;
  }

  function _ladderPickHtml(pick) {
    const p = pick.pred, m = pick.match;
    const sigCls  = p.signal === 'high' ? 'lsig-high' : 'lsig-med';
    const sigTxt  = p.signal === 'high' ? '🎯 HIGH VALUE' : '📊 VALUE';
    const evSign  = p.evPct > 0 ? '+' : '';
    const profit  = Math.round(pick.stake * (p.odds - 1));
    const newBal  = (_ladder.balance + profit).toLocaleString('ru');
    const conf    = m.topConf;
    return `<div class="ladder-pick">
      <div class="lpick-sig ${sigCls}">${sigTxt} · уверенность ${conf}%</div>
      <div class="lpick-match">${esc(m.homeTeam)} <span class="lpick-vs">vs</span> ${esc(m.awayTeam)}</div>
      <div class="lpick-tour">${esc(m.tournament)}</div>
      <div class="lpick-bet">
        <div>
          <span class="lpick-market">${esc(p.market)}</span>
          <span class="lpick-label">${esc(p.label)}</span>
        </div>
        <div class="lpick-nums">
          <span class="lpick-odds">@ ${p.odds.toFixed(2)}</span>
          <span class="lpick-prob">${(p.prob * 100).toFixed(0)}% вер.</span>
          <span class="lpick-ev">${evSign}${p.evPct.toFixed(1)}% EV</span>
        </div>
      </div>
      <div class="lpick-stake-row">
        <span class="lpick-slbl">Ставка:</span>
        <span class="lpick-sval">${pick.stake}₽</span>
        <span class="lpick-pot">→ при победе ${newBal}₽</span>
      </div>
      <div class="lpick-actions">
        <button class="btn-ld-win" onclick="App.ladderSettle(true)">✅ Зашло +${profit}₽</button>
        <button class="btn-ld-lose" onclick="App.ladderSettle(false)">❌ Не зашло −${pick.stake}₽</button>
      </div>
      <div class="lpick-change-wrap">
        <button class="btn-ld-change" onclick="App.changeLadderPick()">🔄 Поменять прогноз</button>
        <span class="lpick-change-hint">если матч недоступен или не хочешь ставить</span>
      </div>
    </div>`;
  }

  function _ladderDoneHtml(wins, losses) {
    const mult = (_ladder.balance / _ladder.start).toFixed(2);
    return `<div class="ladder-inner ladder-celebrate">
      <div class="ladder-header">
        <span class="ladder-title">🪜 Лесенка</span>
        <button class="ladder-close" onclick="App.closeLadder()">✕</button>
      </div>
      <div class="ld-result">
        <div class="ld-icon">🏆</div>
        <div class="ld-title ld-win-title">Цель достигнута!</div>
        <div class="ld-bal">${_ladder.balance.toLocaleString('ru')}₽</div>
        <div class="ld-meta">×${mult} от старта · ${_ladder.history.length} шагов · ${wins} побед · ${losses} поражений</div>
        <button class="btn-ld-reset" onclick="App.resetLadder()">Новая лесенка</button>
      </div>
    </div>`;
  }

  function _ladderBustedHtml(wins, losses) {
    return `<div class="ladder-inner">
      <div class="ladder-header">
        <span class="ladder-title">🪜 Лесенка</span>
        <button class="ladder-close" onclick="App.closeLadder()">✕</button>
      </div>
      <div class="ld-result">
        <div class="ld-icon">💔</div>
        <div class="ld-title ld-lose-title">Баланс исчерпан</div>
        <div class="ld-meta">${_ladder.history.length} шагов · ${wins} побед · ${losses} поражений</div>
        <button class="btn-ld-reset" onclick="App.resetLadder()">Начать заново</button>
      </div>
    </div>`;
  }

  function ladderSettle(won) {
    const pick = _ladder.currentPick;
    if (!pick) return;
    const profit = won ? Math.round(pick.stake * (pick.pred.odds - 1)) : -pick.stake;
    _ladder.history.push({
      label:         pick.pred.label,
      match:         `${pick.match.homeTeam} vs ${pick.match.awayTeam}`,
      stake:         pick.stake, odds: pick.pred.odds, won, profit,
      balanceBefore: _ladder.balance,
      balanceAfter:  Math.max(0, _ladder.balance + profit),
      ts:            Date.now(),
    });
    _ladder.skipMatchId = pick.match.id; // don't immediately re-pick same match
    _ladder.balance     = Math.max(0, _ladder.balance + profit);
    _ladder.currentPick = null;
    _saveLadder();
    _renderLadder();
  }

  function closeLadder() {
    const panel = document.getElementById('ladder-panel');
    if (panel) panel.style.display = 'none';
  }

  function resetLadder() {
    _ladder.active = false; _ladder.balance = 0; _ladder.target = 0;
    _ladder.start  = 0;    _ladder.history = []; _ladder.currentPick = null;
    try { localStorage.removeItem('ladder_state'); } catch {}
    closeLadder();
  }

  function _saveLadder() {
    try {
      localStorage.setItem('ladder_state', JSON.stringify({
        active: _ladder.active, balance: _ladder.balance,
        target: _ladder.target, start: _ladder.start, history: _ladder.history,
      }));
    } catch {}
  }

  function _loadLadder() {
    try {
      const s = localStorage.getItem('ladder_state');
      if (!s) return;
      Object.assign(_ladder, JSON.parse(s));
      if (_ladder.active) {
        const panel = document.getElementById('ladder-panel');
        if (panel) { panel.style.display = 'block'; _renderLadder(); }
      }
    } catch {}
  }

  // ── История ставок ────────────────────────────────────
  function openHistory() {
    const overlay = document.getElementById('history-overlay');
    const panel   = document.getElementById('history-panel');
    if (!overlay || !panel) return;
    panel.innerHTML = _historyHtml(currentSport);
    overlay.style.display = 'flex';
    document.body.style.overflow = 'hidden';
  }

  function closeHistory() {
    const overlay = document.getElementById('history-overlay');
    if (overlay) overlay.style.display = 'none';
    document.body.style.overflow = '';
  }

  function _exportHistoryCsv() {
    const d = Stats.load(currentSport);
    const rows = [['Дата','Матч','Прогноз','Сигнал','КФ','Ставка₽','EV%','Результат','P&L₽']];
    for (const h of (d.history || []).slice().reverse()) {
      rows.push([
        new Date(h.ts).toLocaleString('ru'),
        `${h.homeTeam} vs ${h.awayTeam}`,
        h.label,
        h.signal.toUpperCase(),
        h.odds.toFixed(2),
        h.stake,
        (h.evPct||0).toFixed(1),
        h.result === 'win' ? 'Зашло' : 'Не зашло',
        h.profit >= 0 ? `+${h.profit}` : h.profit,
      ]);
    }
    const csv = rows.map(r => r.map(v => `"${v}"`).join(',')).join('\n');
    const a = document.createElement('a');
    a.href = 'data:text/csv;charset=utf-8,﻿' + encodeURIComponent(csv);
    a.download = `bets_${new Date().toISOString().slice(0,10)}.csv`;
    a.click();
  }

  function _calibrationHtml(history) {
    const settled = history.filter(h => h.prob && h.result);
    if (settled.length < 8) return '';
    const buckets = [
      { lo: 0.55, hi: 0.60, label: '55–60%' },
      { lo: 0.60, hi: 0.65, label: '60–65%' },
      { lo: 0.65, hi: 0.70, label: '65–70%' },
      { lo: 0.70, hi: 1.01, label: '70%+' },
    ];
    const rows = buckets.map(b => {
      const items = settled.filter(h => h.prob >= b.lo && h.prob < b.hi);
      if (!items.length) return null;
      const wins = items.filter(h => h.result === 'win').length;
      const actual = wins / items.length;
      const expected = (b.lo + Math.min(b.hi, 0.75)) / 2;
      const diff = actual - expected;
      const barW = Math.round(actual * 100);
      const expW = Math.round(expected * 100);
      const cls = Math.abs(diff) < 0.05 ? 'cal-ok' : diff > 0 ? 'cal-hi' : 'cal-lo';
      return `<div class="cal-row">
        <span class="cal-lbl">${b.label}</span>
        <div class="cal-track">
          <div class="cal-bar ${cls}" style="width:${barW}%"></div>
          <div class="cal-exp-line" style="left:${expW}%"></div>
        </div>
        <span class="cal-val ${cls}">${(actual*100).toFixed(0)}%</span>
        <span class="cal-cnt">${items.length}шт</span>
      </div>`;
    }).filter(Boolean);
    if (!rows.length) return '';
    return `<div class="cal-block">
      <div class="cal-title">📐 Калибровка <span class="cal-hint">— вертикальная линия = ожидаемое</span></div>
      ${rows.join('')}
    </div>`;
  }

  function _historyHtml(sport) {
    const d = Stats.load(sport);
    const hist    = (d.history || []).slice().reverse();
    const pending = Object.values(d.pending || {}).sort((a,b) => b.ts - a.ts);
    const total   = hist.length + pending.length;

    const calHtml = _calibrationHtml(hist);

    const histRows = hist.map(h => {
      const isWin  = h.result === 'win';
      const cls    = isWin ? 'hr-win' : 'hr-loss';
      const sigCls = h.signal === 'high' ? 'tier-high' : 'tier-med';
      const sigLbl = h.signal === 'high' ? '🎯 HIGH' : '📊 MED';
      const dt     = new Date(h.ts).toLocaleDateString('ru', { day:'2-digit', month:'2-digit', hour:'2-digit', minute:'2-digit' });
      return `<div class="hist-row-item ${cls}">
        <div class="hri-top">
          <span class="hri-sig stats-tier ${sigCls}">${sigLbl}</span>
          <span class="hri-match">${esc(trunc(h.homeTeam,12))} vs ${esc(trunc(h.awayTeam,12))}</span>
          <span class="hri-dt">${dt}</span>
        </div>
        <div class="hri-mid">${esc(h.label)} · @ ${h.odds.toFixed(2)} · ${h.stake}₽</div>
        <div class="hri-res ${isWin?'hri-w':'hri-l'}">${isWin ? '✓ Зашло' : '✗ Не зашло'} <span class="hri-pnl">${h.profit >= 0 ? '+' : ''}${h.profit}₽</span></div>
      </div>`;
    }).join('');

    const pendRows = pending.map(p => {
      const sigCls = p.signal === 'high' ? 'tier-high' : 'tier-med';
      const sigLbl = p.signal === 'high' ? '🎯 HIGH' : '📊 MED';
      return `<div class="hist-row-item hr-pend">
        <div class="hri-top">
          <span class="hri-sig stats-tier ${sigCls}">${sigLbl}</span>
          <span class="hri-match">${esc(trunc(p.homeTeam,12))} vs ${esc(trunc(p.awayTeam,12))}</span>
          <span class="hri-dt">⏳ ожидает</span>
        </div>
        <div class="hri-mid">${esc(p.label)} · @ ${p.odds.toFixed(2)} · ${p.stake}₽</div>
      </div>`;
    }).join('');

    return `<div class="hist-inner">
      <div class="hist-head-row">
        <span class="hist-title">📜 История (${total})</span>
        <div class="hist-actions">
          ${hist.length ? `<button class="btn-hist-csv" onclick="App.exportHistoryCsv()">⬇ CSV</button>` : ''}
          <button class="dp-close-btn" onclick="App.closeHistory()">✕</button>
        </div>
      </div>
      ${calHtml}
      ${pending.length ? `<div class="hpend-section"><div class="hpend-title">⏳ В ожидании (${pending.length})</div>${pendRows}</div>` : ''}
      ${hist.length ? histRows : '<div class="hist-empty">История ставок появится здесь после первых завершённых прогнозов</div>'}
    </div>`;
  }

  // ── Detail view ───────────────────────────────────────
  function openDetailView(matchId) {
    const m = analyzed.find(x => x.id === matchId);
    const overlay = document.getElementById('detail-overlay');
    const panel   = document.getElementById('detail-panel');
    if (!m || !overlay || !panel) return;
    panel.innerHTML = _detailHtml(m);
    overlay.style.display = 'flex';
    document.body.style.overflow = 'hidden';
  }

  function closeDetailView() {
    const overlay = document.getElementById('detail-overlay');
    if (overlay) overlay.style.display = 'none';
    document.body.style.overflow = '';
  }

  function _detailHtml(m) {
    function sigRow(lbl, val) {
      return `<div class="dp-sig-row"><span class="dp-sig-lbl">${lbl}</span><span class="dp-sig-val">${val}</span></div>`;
    }
    function probBar(lbl, pct) {
      const cls = pct > 55 ? 'pb-hi' : pct < 45 ? 'pb-lo' : '';
      const valCls = pct > 55 ? 'sh-green' : pct < 45 ? 'sh-red' : '';
      return `<div class="dp-pbar-row">
        <span class="dp-pbar-lbl">${lbl}</span>
        <div class="dp-pbar-track"><div class="dp-pbar-fill ${cls}" style="width:${pct}%"></div></div>
        <span class="dp-pbar-val ${valCls}">${pct}%</span>
      </div>`;
    }

    const instab    = m._instab || 0;
    const instabTxt = instab > 0.48
      ? `⛔ ${(instab*100).toFixed(0)}% — блок сигналов`
      : `✅ ${(instab*100).toFixed(0)}% — стабильно`;
    const histTxt  = m.histAgree === true ? '✅ Архив подтверждает' : m.histAgree === false ? '⚠️ Архив противоречит' : '— Нет данных архива';
    const steamAg  = m.steamData?.agrees;
    const steamTxt = steamAg === true ? '✅ Движение в нашу сторону' : steamAg === false ? '⚠️ Умные деньги против' : '— Нет движения котировок';
    const dom      = m.domData;
    const domTxt   = dom && Math.abs(dom.score) >= 0.3
      ? `✅ ${dom.score > 0 ? esc(trunc(m.homeTeam,12))+' +'+dom.homeAvg : esc(trunc(m.awayTeam,12))+' +'+dom.awayAvg}оч/пар`
      : '— Нет явного доминирования';
    const nnP   = m.nnProb;
    const nnTxt = nnP != null
      ? (m.nnAgrees === true
          ? `✅ ${nnP > 50 ? esc(trunc(m.homeTeam,12)) : esc(trunc(m.awayTeam,12))} ${nnP > 50 ? nnP : 100-nnP}%`
          : m.nnAgrees === false
            ? `⚠️ Расходится с моделью`
            : `— ${nnP}% (слабый сигнал)`)
      : '— Накапливает данные';
    const elo    = m._eloData;
    const eloTxt = elo && (elo.p1 !== 1500 || elo.p2 !== 1500)
      ? `${esc(trunc(m.homeTeam,10))} ${elo.p1} vs ${esc(trunc(m.awayTeam,10))} ${elo.p2} → ${(elo.homeProb*100).toFixed(0)}%`
      : '— Рейтинг накапливается';

    const mktHome  = m.w1Odds && m.w2Odds
      ? Math.round(Math.pow(1/m.w1Odds, 1) / (Math.pow(1/m.w1Odds,1) + Math.pow(1/m.w2Odds,1)) * 100)
      : 50;
    const distrib  = m.scoreDistrib ? Object.entries(m.scoreDistrib).sort((a,b) => b[1]-a[1]) : [];
    const topProb  = distrib[0]?.[1] || 1;

    return `<div class="detail-inner">
      <div class="dp-close-row"><button class="dp-close-btn" onclick="App.closeDetailView()">✕ Закрыть</button></div>
      <div class="dp-head">
        <div class="dp-match">
          <span class="dp-team ${m.matchWinHomeProb >= 50 ? 'dp-fav' : ''}">${esc(m.homeTeam)}</span>
          <div class="dp-score-wrap">
            <span class="dp-score-main">${m.homeSets}:${m.awaySets}</span>
            ${m.currentPts > 0 ? `<span class="dp-score-cur">${m.currentHomePts}:${m.currentAwayPts}</span>` : ''}
          </div>
          <span class="dp-team ${m.matchWinAwayProb > 50 ? 'dp-fav' : ''}">${esc(m.awayTeam)}</span>
        </div>
        <div class="dp-meta-row">
          <span class="dp-tour">${esc(m.tournament)}</span>
          ${m.isLive ? '<span class="dp-live-dot"></span>' : ''}
        </div>
      </div>

      <div class="dp-section">
        <div class="dp-sh">🔍 Источники сигнала</div>
        <div class="dp-sigs">
          ${sigRow('Нестабильность', instabTxt)}
          ${sigRow('Архив игроков', histTxt)}
          ${sigRow('Умные деньги', steamTxt)}
          ${sigRow('Доминирование', domTxt)}
          ${sigRow('Нейросеть', nnTxt)}
          ${sigRow('Elo рейтинг', eloTxt)}
        </div>
      </div>

      <div class="dp-section">
        <div class="dp-sh">📊 Вероятность победы: ${esc(trunc(m.homeTeam, 18))}</div>
        ${probBar('Рынок (Power model)', mktHome)}
        ${probBar('Итоговая оценка', m.matchWinHomeProb)}
      </div>

      ${distrib.length ? `<div class="dp-section">
        <div class="dp-sh">🎯 Все сценарии счёта</div>
        ${distrib.map(([k,v], i) => {
          const isHome = parseInt(k[0]) > parseInt(k[2]);
          const barW   = Math.round(v / topProb * 100);
          return `<div class="dpd-row${i===0?' dpd-top':''}">
            <span class="dpd-score ${isHome?'dpd-h':'dpd-a'}">${k}</span>
            <div class="dpd-bar-t"><div class="dpd-bar-f ${isHome?'dpd-h':'dpd-a'}" style="width:${barW}%"></div></div>
            <span class="dpd-pct">${(v*100).toFixed(0)}%</span>
          </div>`;
        }).join('')}
      </div>` : ''}

      <div class="dp-section">
        <div class="dp-sh">💡 Прогнозы для ставки</div>
        ${m.predictions.length
          ? m.predictions.map(p => {
              const evSign = p.evPct > 0 ? '+' : '';
              return `<div class="dp-pred ${p.signal === 'high' ? 'dp-pred-high' : 'dp-pred-med'}">
                <div class="dpp-top">
                  <span class="dpp-sig">${p.signal === 'high' ? '🎯 HIGH' : '📊 VALUE'}</span>
                  <span class="dpp-label">${esc(p.label)}</span>
                  <span class="dpp-ev">${evSign}${p.evPct.toFixed(1)}%</span>
                </div>
                <div class="dpp-meta">${(p.prob*100).toFixed(0)}% вер. · @ ${p.odds.toFixed(2)} · Kelly ${p.kelly.stake}₽ (${p.kelly.pct}%)</div>
              </div>`;
            }).join('')
          : '<div class="dp-no-preds">⏳ Нет уверенных сигналов прямо сейчас</div>'}
      </div>
    </div>`;
  }

  // ── Render ────────────────────────────────────────────
  function render() {
    const filter   = document.getElementById('filter-select')?.value || 'all';
    const sort     = document.getElementById('sort-select')?.value   || 'confidence';
    const bankroll = getBankroll();

    let list = analyzed.map(m => {
      if (m.sport === 'football' || m.sport === 'hockey' || m.sport === 'tennis')
        return SportsEngine.analyze(m, bankroll);
      return Engine.analyze(m, bankroll, _historyCache[m.id] || null, getOddsMovement(m.id), getScoreData(m.id));
    }).filter(Boolean);

    if (filter === 'high')
      list = list.filter(m => m.predictions.some(p => p.signal === 'high'));
    else if (filter === 'value')
      list = list.filter(m => m.predictions.some(p => p.signal === 'high' || p.signal === 'medium'));
    else if (filter === 'inprogress')
      list = list.filter(m => m.isLive);

    list.sort((a, b) => {
      if (sort === 'confidence') return b.topConf - a.topConf;
      if (sort === 'ev')         return b.topEV   - a.topEV;
      if (sort === 'sets')       return (b.homeSets + b.awaySets) - (a.homeSets + a.awaySets);
      return 0;
    });

    const grid = document.getElementById('matches-grid');
    const meta = SPORT_META[currentSport] || SPORT_META.tt;

    if (list.length === 0) {
      grid.innerHTML = `<div class="empty-wrap">
        <div class="empty-icon" id="sport-empty-icon">${meta.emptyIcon}</div>
        <p>Нет матчей по выбранному фильтру</p>
        <small>Обновляется каждые ${REFRESH_SEC} секунд</small>
      </div>`;
      return;
    }
    grid.innerHTML = list.map(renderCard).join('');
  }

  // ── Player stats / history block ─────────────────────
  function historyRowHtml(m) {
    if (m.sport !== 'tt') return '';
    const h = _historyCache[m.id];

    if (!h) {
      return m.isLive
        ? `<div class="hist-row hist-loading">📁 Статистика игроков: загружается...</div>`
        : '';
    }

    const p1 = h.p1, p2 = h.p2, h2h = h.h2h;
    const hasData = (p1 && p1.matches >= 1) || (p2 && p2.matches >= 1);

    if (!hasData) {
      return `<div class="hist-row hist-neutral">📁 Игроки ещё не в базе (данные накапливаются)</div>`;
    }

    const cls = m.histAgree === true  ? 'hist-ok'
              : m.histAgree === false ? 'hist-warn' : 'hist-neutral';

    const pRow = (nm, st) => !st || st.matches < 1 ? '' : `
      <div class="pstat">
        <span class="pstat-name">${esc(trunc(nm, 15))}</span>
        <span class="pstat-wr ${st.winRate>=0.56?'wr-high':st.winRate<=0.44?'wr-low':''}">${(st.winRate*100).toFixed(0)}%</span>
        <span class="pstat-form">${(st.form||[]).join('')}</span>
        <span class="pstat-m">${st.matches}м</span>
      </div>`;

    const h2hHtml = h2h && h2h.total >= 1
      ? `<div class="h2h-row">H2H: ${h2h.p1Wins}–${h2h.p2Wins} (${h2h.total} матчей)</div>` : '';

    const verdict = m.histAgree === true  ? '✅ Архив подтверждает прогноз'
                  : m.histAgree === false ? '⚠️ Архив противоречит прогнозу'
                  : '📁 Статистика игроков';

    const elo = h.elo;
    const eloHtml = elo && (elo.p1 !== 1500 || elo.p2 !== 1500) ? `
      <div class="elo-row">
        <span class="elo-label">Elo:</span>
        <span class="elo-badge ${elo.p1 > elo.p2 ? 'elo-hi' : ''}">${esc(trunc(m.homeTeam,10))} ${elo.p1}</span>
        <span class="elo-sep">vs</span>
        <span class="elo-badge ${elo.p2 > elo.p1 ? 'elo-hi' : ''}">${esc(trunc(m.awayTeam,10))} ${elo.p2}</span>
        <span class="elo-prob">${(elo.homeProb*100).toFixed(0)}% → ${(( 1-elo.homeProb)*100).toFixed(0)}%</span>
      </div>` : '';

    const nnHtml = m.nnProb !== null && m.nnProb !== undefined
      ? (() => {
          const pct = m.nnProb > 50 ? m.nnProb : (100 - m.nnProb).toFixed(0);
          const who = m.nnProb > 50 ? trunc(m.homeTeam, 12) : trunc(m.awayTeam, 12);
          const cls2 = m.nnAgrees === true ? 'nn-agree' : m.nnAgrees === false ? 'nn-disagree' : '';
          return `<div class="nn-row ${cls2}">
            <span class="nn-lbl">🧠 Нейросеть:</span>
            <span class="nn-val">${esc(who)} ${pct}%</span>
            ${m.nnAgrees === true ? '<span class="nn-badge nn-ok">✓ совпадает</span>'
              : m.nnAgrees === false ? '<span class="nn-badge nn-warn">≠ расходится</span>' : ''}
          </div>`;
        })()
      : (m.isLive && m.sport === 'tt'
          ? `<div class="nn-row nn-building">🧠 Нейросеть: <span class="nn-hint">накапливает данные...</span></div>`
          : '');

    return `<div class="hist-block ${cls}">
      <div class="hist-header">${verdict}</div>
      ${pRow(m.homeTeam, p1)}${pRow(m.awayTeam, p2)}${h2hHtml}${eloHtml}${nnHtml}
    </div>`;
  }

  // ── Card ──────────────────────────────────────────────
  function renderCard(m) {
    const sport = m.sport || 'tt';
    const isGoalSport = sport === 'football' || sport === 'hockey';
    const isTT = sport === 'tt';

    const homeWin = (m.homeSets || m.homeScore || 0) > (m.awaySets || m.awayScore || 0);
    const awayWin = (m.awaySets || m.awayScore || 0) > (m.homeSets || m.homeScore || 0);

    const stripCls = m.bestSignal === 'high'  ? 'strip-green'
                   : m.bestSignal === 'medium' ? 'strip-yellow'
                   : m.bestSignal === 'low'    ? 'strip-blue'
                   : 'strip-grey';

    const cardCls = [
      m.bestSignal === 'high'   ? 'sig-strong' : m.bestSignal === 'medium' ? 'sig-medium' : '',
      m.id === highlightedId ? 'card-highlighted' : '',
    ].filter(Boolean).join(' ');

    // Score display
    const hs = m.homeSets ?? m.homeScore ?? 0;
    const as_ = m.awaySets ?? m.awayScore ?? 0;

    // Set chips (TT + Tennis)
    let setsHtml = '';
    if (!isGoalSport) {
      setsHtml = (m.sets || []).map(s => {
        const done = isTT ? Engine.isSetDone(s.home, s.away)
                          : SportsEngine.isSetDoneTennis(s.home, s.away);
        return `<span class="set-chip ${done ? 'set-done' : 'set-active'}">${s.home}:${s.away}</span>`;
      }).join('');
    }

    // Period/time label (football/hockey)
    const periodHtml = isGoalSport && m.periodLabel
      ? `<div class="period-label">${esc(m.periodLabel)}${m.minute ? ` ${m.minute}'` : ''}</div>`
      : '';

    // Current score in set/game
    const curPtsHtml = !isGoalSport && m.currentPts > 0
      ? `<div class="current-pts">${m.currentHomePts}:${m.currentAwayPts} в ${m.currentSetNum}-й ${isTT ? 'партии' : 'сете'}</div>`
      : '';

    // Set win probability display
    const swPct = m.setWinHomeProb || 50;
    const setWinHtml = isTT && m.isLive && m.currentPts > 0 && Math.abs(swPct - 50) >= 10 ? (() => {
      const favHome = swPct > 50;
      const pct     = favHome ? swPct : 100 - swPct;
      const favTeam = esc(trunc(favHome ? m.homeTeam : m.awayTeam, 14));
      const cls     = pct >= 75 ? 'sw-strong' : pct >= 65 ? 'sw-med' : 'sw-weak';
      return `<div class="set-win-row"><span class="sw-label">Пар.${m.currentSetNum}:</span><span class="${cls}">${favTeam} ${pct}%</span></div>`;
    })() : '';

    // Sparkline (odds movement history)
    const sparkSvg  = isTT ? _sparklineHtml(m.id) : '';
    const sparkHtml = sparkSvg ? `<div class="spark-row">${sparkSvg}<span class="spark-lbl">${esc(trunc(m.homeTeam,10))} ← кф</span></div>` : '';

    // Odds block с движением котировок
    const mov = m.steamData?.drift || null;
    const hasSteam = mov && (mov.w1Steam || mov.w2Steam);
    let oddsHtml = '';
    if (m.w1Odds || m.w2Odds) {
      const mkChip = (name, val, pct, fav, drift, initVal, steam) => {
        const driftHtml = drift != null && Math.abs(drift) >= 1.5
          ? `<span class="o-drift ${drift > 0 ? 'drift-dn' : 'drift-up'}">${drift > 0 ? '↓' : '↑'}${Math.abs(drift)}%</span>`
          : '';
        const initHtml = initVal && Math.abs(initVal - val) >= 0.02
          ? `<span class="o-init">было ${initVal.toFixed(2)}</span>` : '';
        return `<div class="odds-chip ${fav?'odds-fav':''} ${steam?'odds-steam':''}">
          <span class="o-name">${esc(name)}</span>
          <span class="o-val">${val.toFixed(2)}${driftHtml}</span>
          <span class="o-pct">${pct}%${initHtml}</span>
          ${steam ? '<span class="o-steam-lbl">⚡стим</span>' : ''}
        </div>`;
      };
      const chips = [];
      if (m.w1Odds) chips.push(mkChip(trunc(m.homeTeam,11), m.w1Odds, m.matchWinHomeProb,
        m.matchWinHomeProb>50, mov?.w1Drift, mov?.w1Initial, mov?.w1Steam));
      if (m.wxOdds && m.drawProb>0) chips.push(mkChip('X', m.wxOdds, m.drawProb, false, null, null, false));
      if (m.w2Odds) chips.push(mkChip(trunc(m.awayTeam,11), m.w2Odds, m.matchWinAwayProb,
        m.matchWinAwayProb>50, mov?.w2Drift, mov?.w2Initial, mov?.w2Steam));
      oddsHtml = `<div class="odds-strip">
        ${chips.join('')}
        ${m.leonMargin ? `<span class="odds-margin">Маржа ${m.leonMargin}%</span>` : ''}
      </div>
      ${hasSteam ? `<div class="steam-banner">⚡ УМНЫЕ ДЕНЬГИ — резкое движение котировок</div>` : ''}`;
    }

    // Доминирование по очкам
    const dom = m.domData;
    const domHtml = dom && (dom.homeAvg > 0 || dom.awayAvg > 0) && m.doneSets?.length >= 1 ? `
      <div class="dom-row">
        <span class="dom-label">Доминирование:</span>
        <span class="dom-val ${dom.homeAvg > dom.awayAvg + 1 ? 'dom-home' : dom.awayAvg > dom.homeAvg + 1 ? 'dom-away' : ''}">
          ${esc(trunc(m.homeTeam,10))} ${dom.homeAvg > 0 ? dom.homeAvg+'оч/пар' : '—'}
          <span class="dom-sep">vs</span>
          ${esc(trunc(m.awayTeam,10))} ${dom.awayAvg > 0 ? dom.awayAvg+'оч/пар' : '—'}
        </span>
      </div>` : '';

    // Распределение счёта матча (с визуальными барами)
    const distribHtml = (() => {
      if (!m.scoreDistrib || !m.isLive) return '';
      const sorted = Object.entries(m.scoreDistrib).sort((a, b) => b[1] - a[1]);
      const topProb = sorted[0]?.[1] || 1;
      const items = sorted.slice(0, 4).map(([k, v], i) => {
        const pct = (v * 100).toFixed(0);
        const barW = Math.round(v / topProb * 100);
        const isHome = parseInt(k[0]) > parseInt(k[2]);
        const cls = i === 0 ? 'sd-bar-top' : '';
        const teamCls = isHome ? 'sd-home' : 'sd-away';
        return `<div class="sd-row ${cls}">
          <span class="sd-score ${teamCls}">${k}</span>
          <div class="sd-bar-track"><div class="sd-bar-fill ${teamCls}" style="width:${barW}%"></div></div>
          <span class="sd-pct">${pct}%</span>
        </div>`;
      }).join('');
      return `<div class="score-distrib">
        <div class="sd-header">Прогноз счёта:</div>
        ${items}
      </div>`;
    })();

    // Скорость очков
    const vel = m._scoreVel;
    const velHtml = vel && (vel.home > 0 || vel.away > 0) ? `
      <div class="vel-row">
        <span class="vel-label">Темп:</span>
        <span class="vel-home">${esc(trunc(m.homeTeam, 9))} ${vel.home}оч/мин</span>
        <span class="vel-sep">↔</span>
        <span class="vel-away">${esc(trunc(m.awayTeam, 9))} ${vel.away}оч/мин</span>
        ${vel.run !== 0 ? `<span class="vel-run ${vel.run > 0 ? 'run-home' : 'run-away'}">${vel.run > 0 ? '🔥 серия ' + esc(trunc(m.homeTeam, 8)) : '🔥 серия ' + esc(trunc(m.awayTeam, 8))}</span>` : ''}
      </div>` : '';

    const smiDir = m.momentumAdj > 2 ? '▲' : m.momentumAdj < -2 ? '▼' : '–';
    const smiCls = m.momentumAdj > 2 ? 'smi-up' : m.momentumAdj < -2 ? 'smi-down' : 'smi-neu';

    const predsHtml = m.predictions.length > 0
      ? m.predictions.slice(0, 3).map(predRow).join('')
      : `<div class="pred-row type-nobet">
           <span class="pred-icon">⏳</span>
           <span class="pred-body"><div class="pred-label">Ждём данных для прогноза</div></span>
         </div>`;

    const topPred = m.predictions.find(p => p.kelly.stake > 0);
    const kellyHtml = topPred ? `
      <div class="kelly-box">
        <div class="k-left">
          <span class="k-label">Kelly 25% · ${esc(topPred.market)}</span>
          <span class="k-market">${esc(topPred.label)}</span>
        </div>
        <div class="k-right">
          <span class="k-stake">${topPred.kelly.stake}₽</span>
          <span class="k-odds">@ ${topPred.odds.toFixed(2)}</span>
        </div>
      </div>` : '';

    const leonBtn = m.leonUrl ? `
      <a class="btn-leon" href="${esc(m.leonUrl)}" target="_blank" rel="noopener">
        Открыть на Леоне →
      </a>` : '';

    const detailBtn = `<button class="btn-detail" onclick="App.openDetailView('${m.id}')">📋 Детали</button>`;

    const aiHtml = isTT && m.isLive ? `
      <button class="btn-ai" id="aibtn-${m.id}" onclick="App.loadAI('${m.id}', this)">🤖 AI анализ</button>
      <div class="ai-result" id="ai-${m.id}" style="display:none"></div>` : '';

    const statusBadge = m.isLive
      ? `<span class="card-status status-live"><span class="live-dot-small"></span>LIVE</span>`
      : `<span class="card-status status-pre">СКОРО</span>`;

    const sportIcon = SPORT_META[sport]?.icon || '';

    return `
    <div class="match-card ${cardCls}" data-id="${m.id}">
      <div class="card-strip ${stripCls}"></div>
      <div class="card-inner">
        <div class="card-meta">
          <span class="card-tournament">${sportIcon} ${esc(m.tournament)}</span>
          ${statusBadge}
        </div>
        <div class="scoreboard">
          <div class="sb-player home">
            <span class="sb-name ${homeWin ? 'winning' : ''}">${esc(m.homeTeam)}</span>
          </div>
          <div class="sb-center">
            <div class="sb-main-score">
              <span class="${homeWin ? 'score-win' : ''}">${hs}</span>
              <span class="score-sep">:</span>
              <span class="${awayWin ? 'score-win' : ''}">${as_}</span>
            </div>
            ${periodHtml}
            <div class="sb-set-scores">${setsHtml || (!isGoalSport ? '<span style="color:var(--text3);font-size:0.72rem">—</span>' : '')}</div>
            ${curPtsHtml}
          </div>
          <div class="sb-player away" style="align-items:flex-end">
            <span class="sb-name ${awayWin ? 'winning' : ''}">${esc(m.awayTeam)}</span>
          </div>
        </div>
        <div class="momentum-wrap">
          <div class="momentum-label">
            <span class="ml-left">${esc(trunc(m.homeTeam, 13))}</span>
            <span class="ml-mid">Моментум <span class="${smiCls}">${smiDir}</span></span>
            <span class="ml-right">${esc(trunc(m.awayTeam, 13))}</span>
          </div>
          <div class="momentum-bar">
            <div class="mfill home" style="width:${m.momentum}%"></div>
          </div>
        </div>
        ${setWinHtml}
        ${historyRowHtml(m)}
        ${domHtml}
        ${velHtml}
        ${distribHtml}
        ${oddsHtml}
        ${sparkHtml}
        <div class="preds-section">
          <div class="preds-title">📊 Прогнозы</div>
          ${predsHtml}
        </div>
        ${kellyHtml}
        ${aiHtml}
        <div class="card-bottom-row">${leonBtn}${detailBtn}</div>
      </div>
    </div>`;
  }


  function predRow(p) {
    const rowCls = p.signal === 'high'  ? 'type-value'
                 : p.signal === 'medium' ? 'type-medium'
                 : p.signal === 'low'    ? 'type-weak'
                 : 'type-nobet';
    const icon   = p.signal === 'high' ? '🎯' : p.signal === 'medium' ? '📊' : '🔹';
    const evSign = p.evPct > 0 ? '+' : '';
    const evCls  = p.evPct > 7 ? 'ev-high' : p.evPct > 3 ? 'ev-med' : p.evPct > 0 ? 'ev-low' : 'ev-neg';
    const sigLbl = p.signal === 'high' ? 'HIGH VALUE' : p.signal === 'medium' ? 'VALUE' : 'Слабый';
    return `<div class="pred-row ${rowCls}">
      <span class="pred-icon">${icon}</span>
      <div class="pred-body">
        <div class="pred-market">${esc(p.market)}</div>
        <div class="pred-label">${esc(p.label)}</div>
        <div class="pred-meta">${(p.prob*100).toFixed(0)}% вер. · кф ${p.odds.toFixed(2)} · ${sigLbl}</div>
      </div>
      <span class="pred-ev ${evCls}">${evSign}${p.evPct.toFixed(1)}%</span>
    </div>`;
  }

  // ── Countdown ─────────────────────────────────────────
  function resetCountdown() {
    if (_sseActive) return;
    countdownVal = REFRESH_SEC;
    clearInterval(countdownTimer);
    countdownTimer = setInterval(() => {
      countdownVal--;
      const el = document.getElementById('countdown');
      if (el) el.textContent = countdownVal;
      if (countdownVal <= 0) { clearInterval(countdownTimer); refresh(); }
    }, 1000);
  }

  function setStatus(txt, err = false) {
    const el = document.getElementById('status-text');
    if (el) { el.textContent = txt; el.style.color = err ? 'var(--red)' : ''; }
  }

  function showError(html) {
    document.getElementById('matches-grid').innerHTML = `
      <div class="empty-wrap">
        <div class="empty-icon">⚠️</div>
        <p style="color:var(--red)">${html}</p>
        <small>Обновление через ${REFRESH_SEC} секунд...</small>
      </div>`;
  }

  function esc(s) {
    return String(s || '').replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;');
  }
  function trunc(s, n) { return s && s.length > n ? s.slice(0, n) + '…' : (s || ''); }

  function init() {
    document.getElementById('bankroll-input')?.addEventListener('change', render);
    updateStatsBar(Stats.get(currentSport));
    _loadLadder();
    _loadSession();
    refresh();
    _connectSSE();
  }

  document.addEventListener('DOMContentLoaded', init);
  return { refresh, render, setSport, showBestPrediction, closeBestBanner, resetStats, loadAI,
           openLadder, startLadder, ladderSettle, changeLadderPick, closeLadder, resetLadder,
           toggleNotifications, openDetailView, closeDetailView,
           openHistory, closeHistory, exportHistoryCsv: _exportHistoryCsv,
           toggleSession };
})();