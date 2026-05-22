// ============================================================
// TT Live Analyzer — App v5.0
// ============================================================

// ── Статистика прогнозов (localStorage) ───────────────────
const Stats = (() => {
  const KEY = 'tt_preds_v2';

  function load() {
    try { return JSON.parse(localStorage.getItem(KEY) || '{"history":[],"pending":{}}'); }
    catch { return { history: [], pending: {} }; }
  }

  function save(d) {
    try { localStorage.setItem(KEY, JSON.stringify(d)); } catch (e) {}
  }

  // Запускается после каждого refresh
  function processRefresh(analyzed) {
    const d = load();
    const now = Date.now();

    // ── Разрешаем ожидающие прогнозы ──────────────────────
    for (const [key, pred] of Object.entries(d.pending)) {
      const cur = analyzed.find(m => m.id === pred.eventId);

      // Событие исчезло → матч завершён — проверяем по последнему счёту
      if (!cur) {
        if (now - pred.ts > 90000) { // ждём 1.5 мин
          delete d.pending[key];
        }
        continue;
      }

      // Прогноз на победителя партии
      if (pred.tag === 'set') {
        const prevTotal = pred.homeSets + pred.awaySets;
        const curTotal  = cur.homeSets  + cur.awaySets;
        if (curTotal > prevTotal) {
          const homeWonNewSet = cur.homeSets > pred.homeSets;
          const correct = (homeWonNewSet === pred.predictedHome);
          _settle(d, key, pred, correct);
        }
        // Партия ещё идёт, но уже слишком поздно — снять прогноз
        if (cur.currentSetNum > pred.setNum) {
          delete d.pending[key];
        }
        continue;
      }

      // Прогноз на победителя матча
      if (pred.tag === 'match') {
        if (cur.homeSets >= 3 || cur.awaySets >= 3) {
          const homeWon = cur.homeSets >= 3;
          _settle(d, key, pred, homeWon === pred.predictedHome);
        }
        continue;
      }

      // Прогноз на тотал партии
      if (pred.tag === 'total_set') {
        const prevSetTotal = pred.homeSets + pred.awaySets;
        const curSetTotal  = cur.homeSets  + cur.awaySets;
        if (curSetTotal > prevSetTotal) {
          // Найдём завершённую партию
          const finSets  = (cur.sets || []).filter(s => Engine.isSetDone(s.home, s.away));
          const lastDone = finSets[finSets.length - 1];
          if (lastDone) {
            const setTotal = lastDone.home + lastDone.away;
            const over     = setTotal > 21.5;
            const correct  = (pred.isOver === over);
            _settle(d, key, pred, correct);
          } else {
            delete d.pending[key];
          }
        }
        continue;
      }
    }

    // ── Добавляем новые HIGH/MEDIUM прогнозы ──────────────
    for (const m of analyzed) {
      if (!m.isLive) continue;
      for (const p of m.predictions) {
        if (p.signal !== 'high' && p.signal !== 'medium') continue;
        const key = `${m.id}_${p.tag}_${m.currentSetNum}_${m.homeSets}_${m.awaySets}`;
        if (d.pending[key] || d.history.find(h => h.key === key)) continue;

        d.pending[key] = {
          key,
          eventId:       m.id,
          homeTeam:      m.homeTeam,
          awayTeam:      m.awayTeam,
          tag:           p.tag,
          signal:        p.signal,
          label:         p.label,
          market:        p.market,
          odds:          p.odds,
          stake:         p.kelly.stake,
          evPct:         p.evPct,
          predictedHome: p.predictedHome,
          homeSets:      m.homeSets,
          awaySets:      m.awaySets,
          setNum:        m.currentSetNum,
          isOver:        p.label.includes('ТБ'),
          ts:            now,
        };
      }
    }

    // Чистим старые ожидающие (>10 мин)
    for (const [key, pred] of Object.entries(d.pending)) {
      if (now - pred.ts > 600000) delete d.pending[key];
    }

    save(d);
    return summary(d);
  }

  function _settle(d, key, pred, correct) {
    const profit = correct
      ? +(pred.stake * (pred.odds - 1)).toFixed(0)
      : -pred.stake;
    d.history.push({ ...pred, result: correct ? 'win' : 'loss', profit, resolvedTs: Date.now() });
    // Храним только последние 200 записей
    if (d.history.length > 200) d.history = d.history.slice(-200);
    delete d.pending[key];
  }

  function summary(d) {
    if (!d) d = load();
    const h    = d.history || [];
    const wins = h.filter(x => x.result === 'win').length;
    const loss = h.filter(x => x.result === 'loss').length;
    const prof = h.reduce((s, x) => s + (x.profit || 0), 0);
    const stk  = h.reduce((s, x) => s + (x.stake  || 0), 0);
    const roi  = stk > 0 ? (prof / stk * 100) : 0;
    const pend = Object.keys(d.pending || {}).length;
    return { wins, losses: loss, profit: Math.round(prof), roi: roi.toFixed(1), pending: pend, total: wins + loss };
  }

  function get()   { return summary(); }
  function reset() { save({ history: [], pending: {} }); }

  return { processRefresh, get, reset };
})();


// ── Основное приложение ───────────────────────────────────
const App = (() => {

  const REFRESH_SEC = 25;
  let analyzed        = [];
  let countdownVal    = REFRESH_SEC;
  let countdownTimer  = null;
  let isLoading       = false;
  let highlightedId   = null;

  function getBankroll() {
    const v = parseInt(document.getElementById('bankroll-input')?.value || '1000');
    return Math.max(100, isNaN(v) ? 1000 : v);
  }

  // ── Refresh ───────────────────────────────────────────
  async function refresh() {
    if (isLoading) return;
    isLoading = true;
    const btn = document.getElementById('refresh-btn');
    if (btn) btn.classList.add('loading');
    setStatus('Получаю данные...');

    try {
      const data = await API.getLiveTT();
      const bankroll = getBankroll();

      analyzed = (data.events || []).map(e => Engine.analyze(e, bankroll));

      // Обрабатываем статистику
      const stats = Stats.processRefresh(analyzed);
      updateStatsBar(stats);

      const liveCount  = analyzed.filter(m => m.isLive).length;
      const valueCount = analyzed.filter(m =>
        m.predictions.some(p => p.signal === 'high' || p.signal === 'medium')
      ).length;

      document.getElementById('count-live').textContent   = liveCount;
      document.getElementById('count-value').textContent  = valueCount;
      document.getElementById('last-update').textContent  = new Date().toLocaleTimeString('ru');

      const srcEl = document.getElementById('data-source');
      if (srcEl) srcEl.textContent = data.source ? `Источник: ${data.source}` : '';

      setStatus(liveCount > 0 ? `${liveCount} лайв матчей` : 'Нет лайв матчей');
      render();
    } catch (e) {
      console.error(e);
      const isConn = e.message.includes('fetch') || e.message.includes('Failed');
      setStatus(isConn ? 'Сервер не запущен' : 'Ошибка', true);
      showError(isConn
        ? 'Сервер не запущен.<br>Запусти <strong>start.bat</strong> (двойной клик).'
        : e.message);
    } finally {
      isLoading = false;
      if (btn) btn.classList.remove('loading');
      resetCountdown();
    }
  }

  // ── Лучший прогноз ────────────────────────────────────
  function findBestPrediction() {
    let best = null, bestScore = -Infinity, bestMatch = null;
    for (const m of analyzed) {
      if (!m.isLive) continue;
      for (const p of m.predictions) {
        // Приоритет: high > medium > low, внутри — по EV и вероятности
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

    // Баннер
    const evSign = pred.evPct > 0 ? '+' : '';
    const sigCls  = pred.signal === 'high' ? 'banner-high' : 'banner-med';
    const sigIcon = pred.signal === 'high' ? '🎯' : pred.signal === 'medium' ? '📊' : '🔹';
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
            ${(pred.prob * 100).toFixed(0)}% вероятность · кф ${pred.odds.toFixed(2)} · EV ${evSign}${pred.evPct.toFixed(1)}%
            ${pred.kelly.stake > 0 ? `· Kelly: <strong>${pred.kelly.stake}₽</strong>` : ''}
          </span>
        </div>
        <button class="best-close" onclick="App.closeBestBanner()">✕</button>
      </div>`;

    // Прокрутить к карточке и подсветить
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

  // ── Статистика ────────────────────────────────────────
  function updateStatsBar(s) {
    const el = document.getElementById('stats-bar');
    if (!el) return;
    if (s.total === 0 && s.pending === 0) {
      el.innerHTML = '<span class="stats-hint">Статистика появится после первых прогнозов</span>';
      return;
    }
    const profCls = s.profit >= 0 ? 'sh-green' : 'sh-red';
    const roiCls  = parseFloat(s.roi) >= 0 ? 'sh-green' : 'sh-red';
    el.innerHTML = `
      <span class="stats-label">Стат:</span>
      <span class="stats-pill win">${s.wins}✓</span>
      <span class="stats-pill loss">${s.losses}✗</span>
      ${s.pending ? `<span class="stats-pill pend">${s.pending}⏳</span>` : ''}
      <span class="stats-sep">·</span>
      <span class="sh-val ${profCls}">${s.profit >= 0 ? '+' : ''}${s.profit}₽</span>
      <span class="stats-sep">·</span>
      <span class="sh-val ${roiCls}">ROI ${s.roi}%</span>
      <button class="stats-reset" onclick="App.resetStats()" title="Сбросить статистику">↺</button>`;
  }

  function resetStats() {
    if (!confirm('Сбросить всю статистику?')) return;
    Stats.reset();
    updateStatsBar(Stats.get());
  }

  // ── Рендер карточек ───────────────────────────────────
  function render() {
    const filter   = document.getElementById('filter-select')?.value || 'all';
    const sort     = document.getElementById('sort-select')?.value   || 'confidence';
    const bankroll = getBankroll();

    let list = analyzed.map(m => Engine.analyze(m, bankroll));

    if (filter === 'value') {
      list = list.filter(m => m.predictions.some(p => p.signal === 'high' || p.signal === 'medium'));
    } else if (filter === 'inprogress') {
      list = list.filter(m => m.isLive);
    }

    list.sort((a, b) => {
      if (sort === 'confidence') return b.topConf - a.topConf;
      if (sort === 'ev')         return b.topEV   - a.topEV;
      if (sort === 'sets')       return (b.homeSets + b.awaySets) - (a.homeSets + a.awaySets);
      return 0;
    });

    const grid = document.getElementById('matches-grid');
    if (list.length === 0) {
      grid.innerHTML = `<div class="empty-wrap">
        <div class="empty-icon">🏓</div>
        <p>Нет матчей по выбранному фильтру</p>
        <small>Обновляется каждые ${REFRESH_SEC} секунд</small>
      </div>`;
      return;
    }
    grid.innerHTML = list.map(renderCard).join('');
  }

  // ── Карточка ──────────────────────────────────────────
  function renderCard(m) {
    const homeWin = m.homeSets > m.awaySets;
    const awayWin = m.awaySets > m.homeSets;

    const stripCls = m.bestSignal === 'high'   ? 'strip-green'
                   : m.bestSignal === 'medium'  ? 'strip-yellow'
                   : m.bestSignal === 'low'     ? 'strip-blue'
                   : 'strip-grey';

    const cardCls = [
      m.bestSignal === 'high'   ? 'sig-strong' : m.bestSignal === 'medium' ? 'sig-medium' : '',
      m.id === highlightedId ? 'card-highlighted' : '',
    ].filter(Boolean).join(' ');

    const setsHtml = (m.sets || []).map(s => {
      const done = Engine.isSetDone(s.home, s.away);
      return `<span class="set-chip ${done ? 'set-done' : 'set-active'}">${s.home}:${s.away}</span>`;
    }).join('');

    const oddsHtml = (m.w1Odds || m.w2Odds) ? `
      <div class="odds-strip">
        ${m.w1Odds ? `<div class="odds-chip ${m.matchWinHomeProb > 50 ? 'odds-fav' : ''}">
          <span class="o-name">${esc(trunc(m.homeTeam, 12))}</span>
          <span class="o-val">${m.w1Odds.toFixed(2)}</span>
          <span class="o-pct">${m.matchWinHomeProb}%</span>
        </div>` : ''}
        ${m.w2Odds ? `<div class="odds-chip ${m.matchWinAwayProb > 50 ? 'odds-fav' : ''}">
          <span class="o-name">${esc(trunc(m.awayTeam, 12))}</span>
          <span class="o-val">${m.w2Odds.toFixed(2)}</span>
          <span class="o-pct">${m.matchWinAwayProb}%</span>
        </div>` : ''}
        ${m.leonMargin ? `<span class="odds-margin">Маржа ${m.leonMargin}%</span>` : ''}
      </div>` : '';

    // Momentum SMI indicator
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

    const statusBadge = m.isLive
      ? `<span class="card-status status-live"><span class="live-dot-small"></span>LIVE</span>`
      : `<span class="card-status status-pre">СКОРО</span>`;

    return `
    <div class="match-card ${cardCls}" data-id="${m.id}">
      <div class="card-strip ${stripCls}"></div>
      <div class="card-inner">

        <div class="card-meta">
          <span class="card-tournament">${esc(m.tournament)}</span>
          ${statusBadge}
        </div>

        <div class="scoreboard">
          <div class="sb-player home">
            <span class="sb-name ${homeWin ? 'winning' : ''}">${esc(m.homeTeam)}</span>
          </div>
          <div class="sb-center">
            <div class="sb-main-score">
              <span class="${homeWin ? 'score-win' : ''}">${m.homeSets}</span>
              <span class="score-sep">:</span>
              <span class="${awayWin ? 'score-win' : ''}">${m.awaySets}</span>
            </div>
            <div class="sb-set-scores">${setsHtml || '<span style="color:var(--text3);font-size:0.72rem">—</span>'}</div>
            ${m.currentPts > 0
              ? `<div class="current-pts">${m.currentHomePts}:${m.currentAwayPts} в ${m.currentSetNum}-й партии</div>`
              : ''}
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

        ${oddsHtml}

        <div class="preds-section">
          <div class="preds-title">📊 Прогнозы</div>
          ${predsHtml}
        </div>

        ${kellyHtml}
        ${leonBtn}
      </div>
    </div>`;
  }

  function predRow(p) {
    const rowCls = p.signal === 'high'   ? 'type-value'
                 : p.signal === 'medium'  ? 'type-medium'
                 : p.signal === 'low'     ? 'type-weak'
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
        <div class="pred-meta">${(p.prob * 100).toFixed(0)}% вер. · кф ${p.odds.toFixed(2)} · ${sigLbl}</div>
      </div>
      <span class="pred-ev ${evCls}">${evSign}${p.evPct.toFixed(1)}%</span>
    </div>`;
  }

  // ── Таймер ───────────────────────────────────────────
  function resetCountdown() {
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
    updateStatsBar(Stats.get());
    refresh();
  }

  document.addEventListener('DOMContentLoaded', init);
  return { refresh, render, showBestPrediction, closeBestBanner, resetStats };
})();