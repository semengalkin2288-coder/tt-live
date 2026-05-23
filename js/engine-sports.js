// ============================================================
// Sports Engine v1.0  —  Football · Hockey · Tennis
// ============================================================

const SportsEngine = (() => {

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
    const r1 = 1/w1, rx = wx ? 1/wx : 0, r2 = 1/w2, t = r1 + rx + r2;
    return { home: r1/t, draw: rx/t, away: r2/t };
  }

  function noVig2(w1, w2) {
    if (!w1 || !w2) return { home: 0.5, away: 0.5 };
    const r1 = 1/w1, r2 = 1/w2, t = r1 + r2;
    return { home: r1/t, away: r2/t };
  }

  // ── Poisson ──────────────────────────────────────────────
  function poissonPMF(k, lam) {
    let p = Math.exp(-lam);
    for (let i = 0; i < k; i++) p = p * lam / (i + 1);
    return p;
  }
  function poissonCDF(k, lam) {
    let s = 0;
    for (let i = 0; i <= k; i++) s += poissonPMF(i, lam);
    return Math.min(1, s);
  }
  function poissonAtLeast(k, lam) {
    if (k <= 0) return 1;
    return 1 - poissonCDF(k - 1, lam);
  }

  // ── Signal / confidence ───────────────────────────────────
  function signalLevel(evPct, prob) {
    if (evPct >= 6  && prob >= 0.58) return 'high';
    if (evPct >= 3  && prob >= 0.53) return 'medium';
    if (evPct >= 1  && prob >= 0.50) return 'low';
    return 'none';
  }

  function confidence(prob, evPct) {
    let s = Math.round(prob * 100);
    if (evPct > 8)      s = Math.min(s + 8, 95);
    else if (evPct > 4) s = Math.min(s + 4, 93);
    else if (evPct < 0) s = Math.max(s - 8, 20);
    return Math.max(20, Math.min(95, s));
  }

  // ── FOOTBALL / HOCKEY ─────────────────────────────────────
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

    // Base probs from live odds (already reflect score/time)
    const base = (wxOdds && w1Odds && w2Odds)
      ? noVig3(w1Odds, wxOdds, w2Odds)
      : (() => { const p = noVig2(w1Odds, w2Odds); return { home: p.home, draw: 0, away: p.away }; })();

    // Small score-momentum adjustment
    const scoreDiff = homeScore - awayScore;
    const adj = Math.max(-0.06, Math.min(0.06, scoreDiff * 0.015));

    const homeWinProb = Math.max(0.03, Math.min(0.94, base.home + adj));
    const drawProb    = base.draw > 0
      ? Math.max(0.02, base.draw - Math.abs(adj) * 0.4) : 0;
    const awayWinProb = Math.max(0.03, Math.min(0.94, 1 - homeWinProb - drawProb));

    // Remaining goals estimate (Poisson)
    const avgGoals = isFootball ? 2.7 : 5.5;
    const remFracMap = isFootball
      ? [0, 0.55, 0.25, 0.10, 0.05]   // period index 0-4
      : [0, 0.72, 0.40, 0.15, 0.08, 0.04];
    const remFrac = remFracMap[Math.min(period, remFracMap.length - 1)] || 0.3;
    const remLambda = avgGoals * remFrac;
    const curGoals  = homeScore + awayScore;

    // Total
    let totalOverProb = null;
    if (totalLine && totalOverOdds && totalUnderOdds) {
      const needed = totalLine - curGoals;
      if (needed <= 0) {
        totalOverProb = 0.97;
      } else {
        totalOverProb = poissonAtLeast(Math.ceil(needed), remLambda);
      }
      totalOverProb = Math.max(0.05, Math.min(0.95, totalOverProb));
    }

    // Handicap (goal-based)
    let hdpHomeProb = null, hdpAwayProb = null;
    if (hdpLine !== null && hdpLine !== undefined && hdpHomeOdds && hdpAwayOdds) {
      const adjHome = Math.max(0.03, Math.min(0.94, homeWinProb + (hdpLine || 0) * 0.04));
      hdpHomeProb = adjHome;
      hdpAwayProb = 1 - adjHome;
    }

    const momentum = Math.max(5, Math.min(95, 50 + scoreDiff * 8));

    const effW1 = w1Odds;
    const effWx = wxOdds;
    const effW2 = w2Odds;

    const evHome = effW1 ? ev(homeWinProb, effW1) : -99;
    const evDraw = effWx && drawProb > 0 ? ev(drawProb, effWx) : -99;
    const evAway = effW2 ? ev(awayWinProb, effW2) : -99;

    const preds = [];

    function addPred(tag, market, label, prob, odds, evPct, ph) {
      if (!odds || odds <= 1.0) return;
      const sig = signalLevel(evPct, prob);
      if (sig === 'none') return;
      preds.push({ tag, market, label, prob, odds, evPct,
        kelly: kelly(prob, odds, bankroll), signal: sig, predictedHome: ph });
    }

    // Winner
    if (effW1 && homeWinProb >= 0.53)
      addPred('match', 'Победитель', homeTeam, homeWinProb, effW1, evHome, true);
    else if (effW2 && awayWinProb >= 0.53)
      addPred('match', 'Победитель', awayTeam, awayWinProb, effW2, evAway, false);

    // Draw (football only)
    if (isFootball && drawProb >= 0.28 && effWx)
      addPred('draw', 'Ничья', 'Ничья', drawProb, effWx, evDraw, null);

    // Total
    if (totalOverProb !== null && totalLine) {
      const tp = totalOverProb, tup = 1 - tp;
      if (tp >= 0.53 && totalOverOdds)
        addPred('total', `Тотал (${totalLine})`, `Больше ${totalLine}`,
          tp, totalOverOdds, ev(tp, totalOverOdds), null);
      else if (tup >= 0.53 && totalUnderOdds)
        addPred('total', `Тотал (${totalLine})`, `Меньше ${totalLine}`,
          tup, totalUnderOdds, ev(tup, totalUnderOdds), null);
    }

    // Handicap
    if (hdpHomeProb !== null) {
      const hdpSign = (hdpLine || 0) > 0 ? '+' : '';
      if (hdpHomeProb >= 0.53 && hdpHomeOdds)
        addPred('handicap', 'Гандикап',
          `${homeTeam} (${hdpSign}${hdpLine})`,
          hdpHomeProb, hdpHomeOdds, ev(hdpHomeProb, hdpHomeOdds), true);
      else if (hdpAwayProb >= 0.53 && hdpAwayOdds) {
        const al = -(hdpLine || 0), as2 = al > 0 ? '+' : '';
        addPred('handicap', 'Гандикап',
          `${awayTeam} (${as2}${al})`,
          hdpAwayProb, hdpAwayOdds, ev(hdpAwayProb, hdpAwayOdds), false);
      }
    }

    preds.sort((a, b) => b.evPct - a.evPct);

    const bestSig = preds[0]?.signal || 'none';
    const topEV   = preds[0]?.evPct  || 0;
    const topProb = preds[0]?.prob    || 0.5;
    const topConf = confidence(topProb, topEV);

    const parts = [w1Odds ? 1/w1Odds : 0, wxOdds ? 1/wxOdds : 0, w2Odds ? 1/w2Odds : 0];
    const margin = (w1Odds && w2Odds)
      ? ((parts.reduce((a,b) => a+b, 0) - 1) * 100).toFixed(1) : null;

    return {
      ...event,
      predictions: preds, bestSignal: bestSig, topEV, topConf,
      momentum, leonMargin: margin,
      matchWinHomeProb: Math.round(homeWinProb * 100),
      matchWinAwayProb: Math.round(awayWinProb * 100),
      drawProb: Math.round(drawProb * 100),
      momentumAdj: +(adj * 100).toFixed(1),
      setWinHomeProb: Math.round(homeWinProb * 100),
      doneSets: [], currentPts: 0,
    };
  }

  // ── TENNIS ────────────────────────────────────────────────
  function isSetDoneTennis(h, a) {
    if (h >= 6 && h - a >= 2) return true;
    if (a >= 6 && a - h >= 2) return true;
    if (h >= 7 || a >= 7) return true;
    return false;
  }

  function gameWinProb(hG, aG) {
    const diff = hG - aG, total = hG + aG;
    if (hG >= 6 && diff >= 2) return 1.0;
    if (aG >= 6 && -diff >= 2) return 0.0;
    if (hG >= 7 || aG >= 7) return hG > aG ? 1.0 : 0.0;
    const scale = 0.04 + (total / 12) * 0.08;
    return Math.max(0.05, Math.min(0.95, 0.5 + diff * scale));
  }

  function matchWinTennis(hS, aS, swP, stw) {
    if (hS >= stw) return 1.0;
    if (aS >= stw) return 0.0;
    const cache = {};
    function dp(h, a) {
      if (h >= stw) return 1.0;
      if (a >= stw) return 0.0;
      const k = `${h}_${a}`;
      if (cache[k] !== undefined) return cache[k];
      return (cache[k] = swP * dp(h+1, a) + (1-swP) * dp(h, a+1));
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

    const setWinRaw = Math.max(0.05, Math.min(0.95,
      gameWinProb(currentHomePts || 0, currentAwayPts || 0)
    ));
    let histSetWin = 0.5;
    if (doneSets.length >= 1) {
      const hw = doneSets.filter(s => s.home > s.away).length;
      histSetWin = (hw + 0.5) / (doneSets.length + 1);
    }
    const setWinFinal = Math.max(0.05, Math.min(0.95, 0.6 * setWinRaw + 0.4 * histSetWin));

    const matchModel = matchWinTennis(homeSets, awaySets, setWinFinal, STW);
    const base = noVig2(w1Odds, w2Odds);
    const trueHome = (w1Odds && w2Odds)
      ? 0.55 * matchModel + 0.45 * base.home : matchModel;
    const trueAway = 1 - trueHome;

    const effW1 = w1Odds || Math.max(1.1, 1 / (matchModel * 0.93));
    const effW2 = w2Odds || Math.max(1.1, 1 / ((1 - matchModel) * 0.93));
    const evM1 = ev(trueHome, effW1), evM2 = ev(trueAway, effW2);

    // Total games
    let totalOverProb = null;
    if (totalLine && totalOverOdds && totalUnderOdds) {
      const doneGames = doneSets.reduce((s, x) => s + x.home + x.away, 0);
      const curGames  = (currentHomePts || 0) + (currentAwayPts || 0);
      const avgSet    = doneSets.length > 0 ? doneGames / doneSets.length : 9;
      const cache = {};
      function dpS(h, a) {
        if (h >= STW || a >= STW) return 0;
        const k = `${h}:${a}`;
        if (cache[k] !== undefined) return cache[k];
        return (cache[k] = 1 + setWinFinal * dpS(h+1, a) + (1-setWinFinal) * dpS(h, a+1));
      }
      const remSets = setWinFinal * dpS(homeSets+1, awaySets) +
                      (1-setWinFinal) * dpS(homeSets, awaySets+1);
      const estRemCur = Math.max(0, avgSet - curGames);
      const estTotal  = doneGames + curGames + estRemCur + remSets * avgSet;
      totalOverProb = Math.max(0.1, Math.min(0.9, 0.5 + (estTotal - totalLine) * 0.04));
    }

    // Handicap by sets (DP)
    let hdpHomeProb = null, hdpAwayProb = null;
    if (hdpLine !== null && hdpLine !== undefined && hdpHomeOdds && hdpAwayOdds) {
      const cache = {};
      function hdpDP(h, a) {
        if (h >= STW) { const d = h-a; return (d + hdpLine) > 0 ? [1,0] : [0,1]; }
        if (a >= STW) { const d = h-a; return (d + hdpLine) > 0 ? [1,0] : [0,1]; }
        const k = `${h}:${a}`;
        if (cache[k]) return cache[k];
        const hw = hdpDP(h+1, a), aw = hdpDP(h, a+1);
        return (cache[k] = [
          setWinFinal*hw[0]+(1-setWinFinal)*aw[0],
          setWinFinal*hw[1]+(1-setWinFinal)*aw[1],
        ]);
      }
      [hdpHomeProb, hdpAwayProb] = hdpDP(homeSets, awaySets);
    }

    const momentum = Math.max(5, Math.min(95, 50 + (currentHomePts - currentAwayPts) * 6));
    const preds = [];

    function addPred(tag, market, label, prob, odds, evPct, ph) {
      if (homeSets >= STW || awaySets >= STW) return;
      const sig = signalLevel(evPct, prob);
      if (sig === 'none') return;
      preds.push({ tag, market, label, prob, odds, evPct,
        kelly: kelly(prob, odds, bankroll), signal: sig, predictedHome: ph });
    }

    if (trueHome >= 0.55) addPred('match', 'Победитель', homeTeam, trueHome, effW1, evM1, true);
    else if (trueAway >= 0.55) addPred('match', 'Победитель', awayTeam, trueAway, effW2, evM2, false);

    if (totalOverProb !== null && totalLine) {
      const up = 1 - totalOverProb;
      if (totalOverProb >= 0.55 && totalOverOdds)
        addPred('total', `Тотал геймов (${totalLine})`, `Больше ${totalLine}`,
          totalOverProb, totalOverOdds, ev(totalOverProb, totalOverOdds), null);
      else if (up >= 0.55 && totalUnderOdds)
        addPred('total', `Тотал геймов (${totalLine})`, `Меньше ${totalLine}`,
          up, totalUnderOdds, ev(up, totalUnderOdds), null);
    }

    if (hdpHomeProb !== null) {
      const awayHdp = -(hdpLine || 0);
      const hs2 = (hdpLine || 0) > 0 ? '+' : '';
      if (hdpHomeProb >= 0.55 && hdpHomeOdds)
        addPred('handicap', 'Фора по сетам',
          `${homeTeam} (${hs2}${hdpLine})`, hdpHomeProb, hdpHomeOdds,
          ev(hdpHomeProb, hdpHomeOdds), true);
      else if (hdpAwayProb >= 0.55 && hdpAwayOdds) {
        const as2 = awayHdp > 0 ? '+' : '';
        addPred('handicap', 'Фора по сетам',
          `${awayTeam} (${as2}${awayHdp})`, hdpAwayProb, hdpAwayOdds,
          ev(hdpAwayProb, hdpAwayOdds), false);
      }
    }

    preds.sort((a, b) => b.evPct - a.evPct);
    const bestSig = preds[0]?.signal || 'none';
    const topEV   = preds[0]?.evPct  || 0;
    const topProb = preds[0]?.prob    || 0.5;
    const topConf = confidence(topProb, topEV);
    const margin  = w1Odds && w2Odds
      ? ((1/w1Odds + 1/w2Odds - 1) * 100).toFixed(1) : null;

    return {
      ...event,
      predictions: preds, bestSignal: bestSig, topEV, topConf,
      momentum, leonMargin: margin,
      matchWinHomeProb: Math.round(trueHome * 100),
      matchWinAwayProb: Math.round(trueAway * 100),
      drawProb: 0,
      momentumAdj: +((setWinRaw - 0.5) * 10).toFixed(1),
      setWinHomeProb: Math.round(setWinRaw * 100),
      doneSets, currentPts: (currentHomePts || 0) + (currentAwayPts || 0),
    };
  }

  function analyze(event, bankroll = 1000) {
    const s = event.sport || 'tt';
    if (s === 'football' || s === 'hockey') return analyzeGoalSport(event, bankroll, s);
    if (s === 'tennis')   return analyzeTennis(event, bankroll);
    return null;
  }

  return { analyze, isSetDoneTennis };
})();