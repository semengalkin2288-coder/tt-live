// ============================================================
// Sports Engine v2.0  —  Football · Hockey · Tennis
// Core: Full Poisson model for goal sports (λ extracted from live odds)
//       Markov DP for tennis (set + game level)
// ============================================================

const SportsEngine = (() => {

  // ── Kelly / EV ────────────────────────────────────────────
  function kelly(prob, odds, bank, frac = 0.25) {
    const b = odds - 1, q = 1 - prob;
    const k = (b * prob - q) / b;
    const f = Math.max(0, k * frac);
    const stake = Math.max(Math.round(f * bank / 10) * 10, f > 0.001 ? 50 : 0);
    return { stake, pct: (f * 100).toFixed(1), raw: k };
  }

  function ev(prob, odds) {
    return ((prob * (odds - 1)) - (1 - prob)) * 100;
  }

  function noVig3(w1, wx, w2) {
    const r1 = 1/w1, rx = 1/wx, r2 = 1/w2, t = r1+rx+r2;
    return { home: r1/t, draw: rx/t, away: r2/t };
  }
  function noVig2(w1, w2) {
    const r1 = 1/w1, r2 = 1/w2, t = r1+r2;
    return { home: r1/t, away: r2/t };
  }
  function noVigTotal(overOdds, underOdds) {
    const r1 = 1/overOdds, r2 = 1/underOdds, t = r1+r2;
    return { over: r1/t, under: r2/t };
  }

  // ── Poisson core ──────────────────────────────────────────
  function pPMF(k, lam) {
    if (lam <= 0) return k === 0 ? 1 : 0;
    let p = Math.exp(-lam);
    for (let i = 0; i < k; i++) p = p * lam / (i + 1);
    return Math.max(0, p);
  }

  // Compute [p1, px, p2] from Poisson(λh) vs Poisson(λa)
  function poissonMatchProbs(lh, la, maxG = 9) {
    // Pre-compute PMFs with tail correction
    const ph = Array.from({ length: maxG + 1 }, (_, i) => pPMF(i, lh));
    const pa = Array.from({ length: maxG + 1 }, (_, i) => pPMF(i, la));
    const sumH = ph.reduce((a, b) => a + b, 0) || 1;
    const sumA = pa.reduce((a, b) => a + b, 0) || 1;
    for (let i = 0; i <= maxG; i++) { ph[i] /= sumH; pa[i] /= sumA; }

    let p1 = 0, px = 0, p2 = 0;
    for (let i = 0; i <= maxG; i++) {
      for (let j = 0; j <= maxG; j++) {
        const p = ph[i] * pa[j];
        if (i > j) p1 += p;
        else if (i === j) px += p;
        else p2 += p;
      }
    }
    const t = p1 + px + p2 || 1;
    return [p1/t, px/t, p2/t];
  }

  // Lambda cache to avoid redundant grid searches
  const _lCache = new Map();

  // Two-level grid search: solve λh, λa from no-vig win probabilities
  function solveLambdas(p1, px, p2) {
    const key = `${p1.toFixed(3)}_${px.toFixed(3)}_${p2.toFixed(3)}`;
    if (_lCache.has(key)) return _lCache.get(key);

    let bLh = 1.2, bLa = 0.9, bErr = Infinity;

    // Coarse sweep
    for (let lh = 0.1; lh <= 4.0; lh += 0.2) {
      for (let la = 0.1; la <= 4.0; la += 0.2) {
        const [e1, ex, e2] = poissonMatchProbs(lh, la);
        const err = (e1-p1)**2 + (ex-px)**2 + (e2-p2)**2;
        if (err < bErr) { bErr = err; bLh = lh; bLa = la; }
      }
    }
    // Fine sweep around best
    for (let dlh = -0.18; dlh <= 0.18; dlh += 0.02) {
      for (let dla = -0.18; dla <= 0.18; dla += 0.02) {
        const lh = Math.max(0.05, bLh + dlh);
        const la = Math.max(0.05, bLa + dla);
        const [e1, ex, e2] = poissonMatchProbs(lh, la);
        const err = (e1-p1)**2 + (ex-px)**2 + (e2-p2)**2;
        if (err < bErr) { bErr = err; bLh = lh; bLa = la; }
      }
    }

    const result = [+bLh.toFixed(3), +bLa.toFixed(3)];
    if (_lCache.size > 300) _lCache.clear();
    _lCache.set(key, result);
    return result;
  }

  // Full score-state probabilities given remaining λh, λa and current score
  function scoreStateProbs(lh_rem, la_rem, hG, aG, totalLine, hdpLine, maxG = 9) {
    const ph = Array.from({ length: maxG + 1 }, (_, i) => pPMF(i, lh_rem));
    const pa = Array.from({ length: maxG + 1 }, (_, i) => pPMF(i, la_rem));
    const sumH = ph.reduce((a, b) => a + b, 0) || 1;
    const sumA = pa.reduce((a, b) => a + b, 0) || 1;
    for (let i = 0; i <= maxG; i++) { ph[i] /= sumH; pa[i] /= sumA; }

    let p1=0, px=0, p2=0, over=0, under=0, hdpH=0, hdpA=0;

    for (let ri = 0; ri <= maxG; ri++) {
      for (let rj = 0; rj <= maxG; rj++) {
        const p = ph[ri] * pa[rj];
        const fH = hG + ri, fA = aG + rj;

        // Match result
        if (fH > fA) p1 += p;
        else if (fH === fA) px += p;
        else p2 += p;

        // Total goals
        if (totalLine !== null && totalLine !== undefined) {
          if (fH + fA > totalLine) over += p;
          else under += p;
        }

        // Handicap (goal difference)
        if (hdpLine !== null && hdpLine !== undefined) {
          if ((fH - fA) + hdpLine > 0) hdpH += p;
          else hdpA += p;
        }
      }
    }

    const wt = p1+px+p2 || 1, tt = over+under || 1, ht = hdpH+hdpA || 1;
    return {
      p1: p1/wt, px: px/wt, p2: p2/wt,
      over: over/tt, under: under/tt,
      hdpH: hdpH/ht, hdpA: hdpA/ht,
    };
  }

  // ── Signal / confidence ───────────────────────────────────
  // edge = model_prob - market_implied_prob (how much we disagree with market)
  function signalLevel(evPct, prob, edge) {
    if (evPct >= 8  && prob >= 0.60 && edge >= 0.05) return 'high';
    if (evPct >= 4  && prob >= 0.54 && edge >= 0.03) return 'medium';
    if (evPct >= 1.5 && prob >= 0.51 && edge >= 0.015) return 'low';
    return 'none';
  }

  function confidence(prob, evPct) {
    let s = Math.round(prob * 100);
    if (evPct > 10) s = Math.min(s + 9, 95);
    else if (evPct > 6) s = Math.min(s + 5, 93);
    else if (evPct > 3) s = Math.min(s + 3, 91);
    else if (evPct < 0) s = Math.max(s - 8, 20);
    return Math.max(20, Math.min(95, s));
  }

  // ── FOOTBALL / HOCKEY ─────────────────────────────────────
  // Core idea:
  //   1. Extract no-vig probs from live 1X2 odds
  //   2. Solve Poisson λh, λa that match those probs
  //      (these λ represent REMAINING expected goals, since odds are live)
  //   3. Use λ to compute ALL market probabilities from first principles
  //   4. Compare model prob vs bookmaker's own market prices
  //   5. Signal where model finds genuine cross-market inconsistency

  function analyzeGoalSport(event, bankroll, sport) {
    const {
      homeTeam, awayTeam,
      homeScore = 0, awayScore = 0,
      period = 1,
      w1Odds, wxOdds, w2Odds,
      totalOverOdds, totalUnderOdds, totalLine,
      hdpHomeOdds, hdpAwayOdds, hdpLine,
    } = event;

    const isFootball = sport === 'football';

    // Need at least W1/W2 to run model
    if (!w1Odds || !w2Odds) {
      return { ...event, predictions: [], bestSignal: 'none', topEV: 0, topConf: 30,
               momentum: 50, leonMargin: null, matchWinHomeProb: 50, matchWinAwayProb: 50,
               drawProb: 0, momentumAdj: 0, setWinHomeProb: 50, doneSets: [], currentPts: 0 };
    }

    // ── Step 1: Market's no-vig probabilities ─────────────
    let mktP1, mktPx, mktP2;
    if (wxOdds) {
      const b = noVig3(w1Odds, wxOdds, w2Odds);
      mktP1 = b.home; mktPx = b.draw; mktP2 = b.away;
    } else {
      const b = noVig2(w1Odds, w2Odds);
      mktP1 = b.home; mktPx = 0; mktP2 = b.away;
    }

    // ── Step 2: Solve remaining λh, λa ───────────────────
    let lh, la;
    if (wxOdds && mktPx > 0.04) {
      [lh, la] = solveLambdas(mktP1, mktPx, mktP2);
    } else {
      // 2-way market: estimate total from period + sport defaults
      const periodRemFrac = isFootball
        ? [0, 0.55, 0.26, 0.08][Math.min(period, 3)]
        : [0, 0.70, 0.38, 0.13][Math.min(period, 3)];
      const fullAvg = isFootball ? 2.6 : 5.4;
      const remTotal = fullAvg * periodRemFrac;
      lh = remTotal * mktP1 / (mktP1 + mktP2);
      la = remTotal * mktP2 / (mktP1 + mktP2);
    }

    // ── Step 3: Model probabilities from Poisson ──────────
    const model = scoreStateProbs(lh, la, homeScore, awayScore,
      (totalLine !== undefined ? totalLine : null),
      (hdpLine   !== undefined ? hdpLine   : null));

    // ── Step 4: Build predictions ─────────────────────────
    const preds = [];

    function addPred(tag, market, label, modelProb, mktImplied, odds, evPct, ph) {
      if (!odds || odds <= 1.1 || modelProb < 0.01) return;
      const edge = modelProb - mktImplied;
      const sig = signalLevel(evPct, modelProb, edge);
      if (sig === 'none') return;
      preds.push({
        tag, market, label, prob: modelProb, odds, evPct,
        kelly: kelly(modelProb, odds, bankroll), signal: sig, predictedHome: ph,
      });
    }

    // Win / Draw
    const evH = ev(model.p1, w1Odds);
    const evA = ev(model.p2, w2Odds);
    addPred('match', 'Победитель', homeTeam, model.p1, mktP1, w1Odds, evH, true);
    addPred('match', 'Победитель', awayTeam, model.p2, mktP2, w2Odds, evA, false);
    if (wxOdds) {
      const evX = ev(model.px, wxOdds);
      addPred('draw', 'Ничья', 'Ничья', model.px, mktPx, wxOdds, evX, null);
    }

    // Total goals — key value: model uses consistent λ while bookie prices it separately
    if (totalLine !== null && totalLine !== undefined && totalOverOdds && totalUnderOdds) {
      const mktTot = noVigTotal(totalOverOdds, totalUnderOdds);
      const evO = ev(model.over, totalOverOdds);
      const evU = ev(model.under, totalUnderOdds);
      addPred('total', `Тотал (${totalLine})`, `Больше ${totalLine}`,
        model.over, mktTot.over, totalOverOdds, evO, null);
      addPred('total', `Тотал (${totalLine})`, `Меньше ${totalLine}`,
        model.under, mktTot.under, totalUnderOdds, evU, null);
    }

    // Handicap — model uses consistent λ vs bookie's separate handicap pricing
    if (hdpLine !== null && hdpLine !== undefined && hdpHomeOdds && hdpAwayOdds) {
      const mktHdp = noVigTotal(hdpHomeOdds, hdpAwayOdds);
      const evHH = ev(model.hdpH, hdpHomeOdds);
      const evHA = ev(model.hdpA, hdpAwayOdds);
      const awayLine = -hdpLine;
      addPred('handicap', `Гандикап (${hdpLine > 0 ? '+' : ''}${hdpLine})`,
        `${homeTeam} (${hdpLine > 0 ? '+' : ''}${hdpLine})`,
        model.hdpH, mktHdp.over, hdpHomeOdds, evHH, true);
      addPred('handicap', `Гандикап (${awayLine > 0 ? '+' : ''}${awayLine})`,
        `${awayTeam} (${awayLine > 0 ? '+' : ''}${awayLine})`,
        model.hdpA, mktHdp.under, hdpAwayOdds, evHA, false);
    }

    preds.sort((a, b) => b.evPct - a.evPct);

    const scoreDiff = homeScore - awayScore;
    const momentum  = Math.max(5, Math.min(95, 50 + scoreDiff * 10));
    const bestSig   = preds[0]?.signal || 'none';
    const topEV     = preds[0]?.evPct  || 0;
    const topProb   = preds[0]?.prob    || 0.5;
    const topConf   = confidence(topProb, topEV);

    const vigParts = [1/w1Odds, wxOdds ? 1/wxOdds : 0, 1/w2Odds];
    const margin = ((vigParts.reduce((a,b)=>a+b,0)-1)*100).toFixed(1);

    return {
      ...event,
      predictions: preds, bestSignal: bestSig, topEV, topConf,
      momentum, leonMargin: margin,
      matchWinHomeProb: Math.round(model.p1 * 100),
      matchWinAwayProb: Math.round(model.p2 * 100),
      drawProb:         Math.round(model.px  * 100),
      momentumAdj:      +(scoreDiff * 1.5).toFixed(1),
      setWinHomeProb:   Math.round(model.p1 * 100),
      doneSets: [], currentPts: 0,
      // Expose model lambdas for debugging
      _lh: +lh.toFixed(2), _la: +la.toFixed(2),
    };
  }

  // ── TENNIS ────────────────────────────────────────────────
  // Improvements vs v1:
  //   - Proper Markov at game level (who leads in games within set)
  //   - Blend: model DP + market implied prob with dynamic weight
  //   - Total games: full remaining-set DP with per-set game distribution
  //   - Strict edge requirement vs market

  function isSetDoneTennis(h, a) {
    if (h >= 6 && h - a >= 2) return true;
    if (a >= 6 && a - h >= 2) return true;
    if (h >= 7 || a >= 7)    return true;
    return false;
  }

  // P(win set from game score h:a) — Markov
  function setWinProbGames(hG, aG) {
    if (isSetDoneTennis(hG, aG)) return hG > aG ? 1.0 : 0.0;
    const diff = hG - aG, total = hG + aG;
    // At 6:6 tiebreak — treat as coin flip
    if (hG === 6 && aG === 6) return 0.5;
    const progress = Math.min(1, total / 12);
    const scale = 0.04 + progress * 0.09;
    return Math.max(0.05, Math.min(0.95, 0.5 + diff * scale));
  }

  // P(win match from set score h:a) — Markov DP
  function matchWinDP(hS, aS, setWinP, setsToWin) {
    if (hS >= setsToWin) return 1.0;
    if (aS >= setsToWin) return 0.0;
    const cache = {};
    function dp(h, a) {
      if (h >= setsToWin) return 1.0;
      if (a >= setsToWin) return 0.0;
      const k = `${h}_${a}`;
      if (cache[k] !== undefined) return cache[k];
      return (cache[k] = setWinP * dp(h+1,a) + (1-setWinP) * dp(h,a+1));
    }
    return dp(hS, aS);
  }

  // Expected remaining sets after current (DP)
  function expectedRemainingSets(hS, aS, setWinP, setsToWin) {
    const cache = {};
    function dpS(h, a) {
      if (h >= setsToWin || a >= setsToWin) return 0;
      const k = `${h}:${a}`;
      if (cache[k] !== undefined) return cache[k];
      return (cache[k] = 1 + setWinP * dpS(h+1,a) + (1-setWinP) * dpS(h,a+1));
    }
    return setWinP * dpS(hS+1,aS) + (1-setWinP) * dpS(hS,aS+1);
  }

  // P(home covers set handicap) — DP
  function setHdpDP(hS, aS, setWinP, hdpLine, setsToWin) {
    const cache = {};
    function dp(h, a) {
      if (h >= setsToWin) { return (h-a) + hdpLine > 0 ? [1,0] : [0,1]; }
      if (a >= setsToWin) { return (h-a) + hdpLine > 0 ? [1,0] : [0,1]; }
      const k = `${h}:${a}`;
      if (cache[k]) return cache[k];
      const hw = dp(h+1,a), aw = dp(h,a+1);
      return (cache[k] = [
        setWinP*hw[0]+(1-setWinP)*aw[0],
        setWinP*hw[1]+(1-setWinP)*aw[1],
      ]);
    }
    return dp(hS, aS);
  }

  function analyzeTennis(event, bankroll) {
    const {
      homeTeam, awayTeam,
      homeSets = 0, awaySets = 0, sets = [],
      currentSetNum = 1, currentHomePts = 0, currentAwayPts = 0,
      setsToWin = 2,
      w1Odds, w2Odds,
      totalOverOdds, totalUnderOdds, totalLine,
      hdpHomeOdds, hdpAwayOdds, hdpLine,
    } = event;

    const STW = setsToWin || 2;
    const doneSets = sets.filter(s => isSetDoneTennis(s.home, s.away));

    // ── Set win probability ───────────────────────────────
    // From current game score in this set
    const setWinGame = setWinProbGames(currentHomePts || 0, currentAwayPts || 0);

    // From historical set win rate (Laplace smoothed)
    let histSetWin = 0.5;
    if (doneSets.length >= 1) {
      const hw = doneSets.filter(s => s.home > s.away).length;
      histSetWin = (hw + 0.5) / (doneSets.length + 1);
    }

    // Weight: more sets played → trust history more
    const histWeight = Math.min(0.5, doneSets.length * 0.18);
    const setWinFinal = Math.max(0.05, Math.min(0.95,
      (1 - histWeight) * setWinGame + histWeight * histSetWin
    ));

    // ── Match win probability ─────────────────────────────
    const matchModel = matchWinDP(homeSets, awaySets, setWinFinal, STW);

    // Blend model with market odds
    const base = (w1Odds && w2Odds) ? noVig2(w1Odds, w2Odds) : { home: 0.5, away: 0.5 };
    // Dynamic blend: more sets played → trust model more
    const modelWeight = Math.min(0.70, 0.40 + doneSets.length * 0.10);
    const trueHome = Math.max(0.03, Math.min(0.97,
      modelWeight * matchModel + (1-modelWeight) * base.home
    ));
    const trueAway = 1 - trueHome;

    const effW1 = w1Odds || Math.max(1.05, 1/(matchModel * 0.93));
    const effW2 = w2Odds || Math.max(1.05, 1/((1-matchModel) * 0.93));

    const mktP1 = base.home, mktP2 = base.away;

    // ── Total games ───────────────────────────────────────
    let totalOverProb = null;
    if (totalLine && totalOverOdds && totalUnderOdds) {
      const doneGames = doneSets.reduce((s, x) => s + x.home + x.away, 0);
      const curGames  = (currentHomePts || 0) + (currentAwayPts || 0);
      // Average games per set (from done sets, or default)
      const avgSet = doneSets.length > 0 ? doneGames / doneSets.length : 9.2;
      // Remaining games in current set
      const estCurSetTotal = Math.max(curGames, avgSet * 0.8);
      const remCur = Math.max(0, estCurSetTotal - curGames);
      // Remaining future sets * avg games
      const remSets = expectedRemainingSets(homeSets, awaySets, setWinFinal, STW);
      const estTotal = doneGames + curGames + remCur + remSets * avgSet;
      const diff = estTotal - totalLine;
      totalOverProb = Math.max(0.08, Math.min(0.92, 0.5 + diff * 0.05));
    }

    // ── Set handicap ──────────────────────────────────────
    let hdpHomeProb = null, hdpAwayProb = null;
    if (hdpLine !== null && hdpLine !== undefined && hdpHomeOdds && hdpAwayOdds) {
      if (homeSets < STW && awaySets < STW) {
        [hdpHomeProb, hdpAwayProb] = setHdpDP(homeSets, awaySets, setWinFinal, hdpLine, STW);
      }
    }

    // ── Build predictions ─────────────────────────────────
    const preds = [];
    const matchDone = homeSets >= STW || awaySets >= STW;

    function addPred(tag, market, label, modelProb, mktImplied, odds, evPct, ph) {
      if (matchDone || !odds || odds <= 1.1) return;
      const edge = modelProb - mktImplied;
      const sig = signalLevel(evPct, modelProb, edge);
      if (sig === 'none') return;
      preds.push({
        tag, market, label, prob: modelProb, odds, evPct,
        kelly: kelly(modelProb, odds, bankroll), signal: sig, predictedHome: ph,
      });
    }

    addPred('match', 'Победитель', homeTeam, trueHome, mktP1, effW1,
      ev(trueHome, effW1), true);
    addPred('match', 'Победитель', awayTeam, trueAway, mktP2, effW2,
      ev(trueAway, effW2), false);

    if (totalOverProb !== null && totalLine) {
      const mktTot = (totalOverOdds && totalUnderOdds)
        ? noVigTotal(totalOverOdds, totalUnderOdds) : { over: 0.5, under: 0.5 };
      addPred('total', `Тотал геймов (${totalLine})`, `Больше ${totalLine}`,
        totalOverProb, mktTot.over, totalOverOdds,
        ev(totalOverProb, totalOverOdds), null);
      addPred('total', `Тотал геймов (${totalLine})`, `Меньше ${totalLine}`,
        1-totalOverProb, mktTot.under, totalUnderOdds,
        ev(1-totalOverProb, totalUnderOdds), null);
    }

    if (hdpHomeProb !== null) {
      const mktHdp = noVigTotal(hdpHomeOdds, hdpAwayOdds);
      const awayHdp = -(hdpLine || 0);
      addPred('handicap', 'Фора по сетам',
        `${homeTeam} (${(hdpLine||0) > 0 ? '+' : ''}${hdpLine})`,
        hdpHomeProb, mktHdp.over, hdpHomeOdds, ev(hdpHomeProb, hdpHomeOdds), true);
      addPred('handicap', 'Фора по сетам',
        `${awayTeam} (${awayHdp > 0 ? '+' : ''}${awayHdp})`,
        hdpAwayProb, mktHdp.under, hdpAwayOdds, ev(hdpAwayProb, hdpAwayOdds), false);
    }

    preds.sort((a, b) => b.evPct - a.evPct);

    const momentum = Math.max(5, Math.min(95, 50 + (setWinGame - 0.5) * 60));
    const bestSig  = preds[0]?.signal || 'none';
    const topEV    = preds[0]?.evPct  || 0;
    const topProb  = preds[0]?.prob    || 0.5;
    const topConf  = confidence(topProb, topEV);
    const margin   = (w1Odds && w2Odds)
      ? ((1/w1Odds + 1/w2Odds - 1) * 100).toFixed(1) : null;

    return {
      ...event,
      predictions: preds, bestSignal: bestSig, topEV, topConf,
      momentum, leonMargin: margin,
      matchWinHomeProb: Math.round(trueHome * 100),
      matchWinAwayProb: Math.round(trueAway * 100),
      drawProb: 0,
      momentumAdj: +((setWinGame - 0.5) * 10).toFixed(1),
      setWinHomeProb: Math.round(setWinGame * 100),
      doneSets, currentPts: (currentHomePts || 0) + (currentAwayPts || 0),
    };
  }

  // ── Public API ────────────────────────────────────────────
  function analyze(event, bankroll = 1000) {
    const s = event.sport || 'tt';
    try {
      if (s === 'football' || s === 'hockey') return analyzeGoalSport(event, bankroll, s);
      if (s === 'tennis')                     return analyzeTennis(event, bankroll);
    } catch (e) {
      console.error(`[SportsEngine.${s}]`, e);
    }
    return null;
  }

  return { analyze, isSetDoneTennis };
})();