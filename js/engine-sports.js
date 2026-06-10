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
    if (evPct >= 7  && prob >= 0.58 && edge >= 0.04) return 'high';
    if (evPct >= 3.5 && prob >= 0.52 && edge >= 0.025) return 'medium';
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
  //   6. Football team form/H2H from SofaScore adds confirmation layer

  function analyzeGoalSport(event, bankroll, sport, teamStats) {
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
    const scoreDiffNow = homeScore - awayScore;

    function addPred(tag, market, label, modelProb, mktImplied, odds, evPct, ph) {
      if (!odds || odds <= 1.1 || modelProb < 0.01) return;
      const edge = modelProb - mktImplied;
      const sig = signalLevel(evPct, modelProb, edge);
      if (sig === 'none') return;

      // Sanity: skip total predictions that are already resolved by current score
      if (tag === 'total' || tag === 'h1tot') {
        const currentTotal = homeScore + awayScore;
        const lineNum = parseFloat(label.replace(/[^\d.]/g, ''));
        if (!isNaN(lineNum)) {
          if (label.startsWith('Больше') && currentTotal > lineNum) return; // already over
          if (label.startsWith('Меньше') && currentTotal > lineNum) return; // already over, under impossible
        }
      }

      // Tag comeback bets (score vs model disagree)
      let isComeback = false;
      if (tag === 'match' && ph !== null) {
        const homeLeading = scoreDiffNow > 0;
        const modelFavHome = ph === true;
        if (homeLeading && !modelFavHome) isComeback = true;   // home leads, model says away
        if (!homeLeading && scoreDiffNow < 0 && modelFavHome) isComeback = true; // away leads, model says home
      }

      preds.push({
        tag, market, label, prob: modelProb, odds, evPct,
        kelly: kelly(modelProb, odds, bankroll), signal: sig, predictedHome: ph,
        isComeback,
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

    // ── Helper: compute over/under prob for any total line ────
    function totalProb(line) {
      let ov = 0;
      for (let ri = 0; ri <= 9; ri++) {
        for (let rj = 0; rj <= 9; rj++) {
          if (homeScore + ri + awayScore + rj > line) ov += pPMF(ri, lh) * pPMF(rj, la);
        }
      }
      return { over: Math.min(0.99, ov), under: Math.max(0.01, 1 - ov) };
    }

    // ── Helper: compute hdp prob for any handicap line ────────
    function hdpProb(line) {
      let hProb = 0;
      for (let ri = 0; ri <= 9; ri++) {
        for (let rj = 0; rj <= 9; rj++) {
          if ((homeScore + ri - awayScore - rj) + line > 0) hProb += pPMF(ri, lh) * pPMF(rj, la);
        }
      }
      return { home: Math.min(0.99, hProb), away: Math.max(0.01, 1 - hProb) };
    }

    // Main total (primary line from _odds_football)
    if (totalLine != null && totalOverOdds && totalUnderOdds) {
      const tp  = totalProb(totalLine);
      const mkt = noVigTotal(totalOverOdds, totalUnderOdds);
      addPred('total', `Тотал (${totalLine})`, `Больше ${totalLine}`, tp.over, mkt.over, totalOverOdds, ev(tp.over, totalOverOdds), null);
      addPred('total', `Тотал (${totalLine})`, `Меньше ${totalLine}`, tp.under, mkt.under, totalUnderOdds, ev(tp.under, totalUnderOdds), null);
    }

    // All other total lines
    for (const [line, overOdds, underOdds] of (event.allTotals || [])) {
      if (line === totalLine) continue;
      const tp  = totalProb(line);
      const mkt = noVigTotal(overOdds, underOdds);
      addPred('total', `Тотал (${line})`, `Больше ${line}`, tp.over, mkt.over, overOdds, ev(tp.over, overOdds), null);
      addPred('total', `Тотал (${line})`, `Меньше ${line}`, tp.under, mkt.under, underOdds, ev(tp.under, underOdds), null);
    }

    // Main handicap
    if (hdpLine != null && hdpHomeOdds && hdpAwayOdds) {
      const hp  = hdpProb(hdpLine);
      const mkt = noVigTotal(hdpHomeOdds, hdpAwayOdds);
      const al  = -hdpLine;
      addPred('handicap', `Фора (${hdpLine > 0 ? '+' : ''}${hdpLine})`, `${homeTeam} (${hdpLine > 0 ? '+' : ''}${hdpLine})`, hp.home, mkt.over, hdpHomeOdds, ev(hp.home, hdpHomeOdds), true);
      addPred('handicap', `Фора (${al > 0 ? '+' : ''}${al})`, `${awayTeam} (${al > 0 ? '+' : ''}${al})`, hp.away, mkt.under, hdpAwayOdds, ev(hp.away, hdpAwayOdds), false);
    }

    // All other handicap lines
    for (const [line, homeOdds, awayOdds] of (event.allHdps || [])) {
      if (line === hdpLine) continue;
      const hp  = hdpProb(line);
      const mkt = noVigTotal(homeOdds, awayOdds);
      const al  = -line;
      addPred('handicap', `Фора (${line > 0 ? '+' : ''}${line})`, `${homeTeam} (${line > 0 ? '+' : ''}${line})`, hp.home, mkt.over, homeOdds, ev(hp.home, homeOdds), true);
      addPred('handicap', `Фора (${al > 0 ? '+' : ''}${al})`, `${awayTeam} (${al > 0 ? '+' : ''}${al})`, hp.away, mkt.under, awayOdds, ev(hp.away, awayOdds), false);
    }

    // BTTS (обе забьют) — P = (1 - e^-lh) * (1 - e^-la)
    if (isFootball && event.bttsYes && event.bttsNo) {
      const pY = (1 - Math.exp(-lh)) * (1 - Math.exp(-la));
      const pN = 1 - pY;
      const mkt = noVigTotal(event.bttsYes, event.bttsNo);
      addPred('btts', 'Обе забьют', 'Да', pY, mkt.over, event.bttsYes, ev(pY, event.bttsYes), null);
      addPred('btts', 'Обе забьют', 'Нет', pN, mkt.under, event.bttsNo, ev(pN, event.bttsNo), null);
    }

    // Double chance
    if (isFootball && event.dc1x) {
      const p1x = model.p1 + model.px;
      const pX2 = model.px + model.p2;
      const p12 = model.p1 + model.p2;
      const tot = (event.dc1x ? 1/event.dc1x : 0) + (event.dcX2 ? 1/event.dcX2 : 0) + (event.dc12 ? 1/event.dc12 : 0) || 1;
      if (event.dc1x)  addPred('dc', 'Двойной шанс', '1X', p1x, (1/event.dc1x)/tot, event.dc1x, ev(p1x, event.dc1x), true);
      if (event.dcX2)  addPred('dc', 'Двойной шанс', 'X2', pX2, (1/event.dcX2)/tot, event.dcX2, ev(pX2, event.dcX2), false);
      if (event.dc12)  addPred('dc', 'Двойной шанс', '12', p12, (1/event.dc12)/tot, event.dc12, ev(p12, event.dc12), null);
    }

    // First half (λ/2 approximation for remaining time — adjust for period)
    if (isFootball && (event.h1w1 || event.h1TotOver)) {
      const periodFrac = period === 1 ? 0.48 : 0.0; // 1H goals = ~48% total
      const lh1 = lh * periodFrac, la1 = la * periodFrac;
      if (lh1 > 0 && la1 > 0) {
        if (event.h1w1 && event.h1w2) {
          const [h1p1, h1px, h1p2] = poissonMatchProbs(lh1, la1);
          const mktH1 = event.h1wx ? noVig3(event.h1w1, event.h1wx, event.h1w2) : noVig2(event.h1w1, event.h1w2);
          addPred('h1', '1-й тайм', homeTeam, h1p1, mktH1.home, event.h1w1, ev(h1p1, event.h1w1), true);
          addPred('h1', '1-й тайм', awayTeam, h1p2, mktH1.away, event.h1w2, ev(h1p2, event.h1w2), false);
          if (event.h1wx) addPred('h1', '1-й тайм', 'Ничья', h1px, mktH1.draw, event.h1wx, ev(h1px, event.h1wx), null);
        }
        if (event.h1TotOver && event.h1TotUnder && event.h1TotLine != null) {
          let h1Ov = 0;
          for (let i = 0; i <= 7; i++) for (let j = 0; j <= 7; j++)
            if (i + j > event.h1TotLine) h1Ov += pPMF(i, lh1) * pPMF(j, la1);
          const mktH1T = noVigTotal(event.h1TotOver, event.h1TotUnder);
          addPred('h1tot', `Тотал 1-го тайма (${event.h1TotLine})`, `Больше ${event.h1TotLine}`, h1Ov, mktH1T.over, event.h1TotOver, ev(h1Ov, event.h1TotOver), null);
          addPred('h1tot', `Тотал 1-го тайма (${event.h1TotLine})`, `Меньше ${event.h1TotLine}`, 1 - h1Ov, mktH1T.under, event.h1TotUnder, ev(1 - h1Ov, event.h1TotUnder), null);
        }
      }
    }

    preds.sort((a, b) => b.evPct - a.evPct);

    const scoreDiff = homeScore - awayScore;
    const momentum  = Math.max(5, Math.min(95, 50 + scoreDiff * 12));
    const bestSig   = preds[0]?.signal || 'none';
    const topEV     = preds[0]?.evPct  || 0;
    const topProb   = preds[0]?.prob    || 0.5;

    // ── Team stats confirmations (football) ────────────────
    let formOK  = null;  // true/false/null = form confirms/contradicts/unknown
    let h2hOK   = null;
    let fbStats = null;
    if (isFootball && teamStats) {
      const hs = teamStats.home, as_ = teamStats.away;
      const h2h = teamStats.h2h;
      const modelFavHome = model.p1 > model.p2;

      if (hs && as_ && hs.matches >= 3 && as_.matches >= 3) {
        // Does historical goal ratio agree with model?
        const statLh = hs.avgFor  * (as_.avgAgainst / 1.3 || 1);
        const statLa = as_.avgFor * (hs.avgAgainst  / 1.3 || 1);
        const statFavHome = statLh > statLa;
        // Does recent form agree?
        const formFavHome = hs.winRate > as_.winRate;
        formOK = (statFavHome === modelFavHome) && (formFavHome === modelFavHome);
        fbStats = { home: hs, away: as_, h2h };
      }
      if (h2h && h2h.total >= 2) {
        h2hOK = (h2h.homeWins > h2h.awayWins) === (model.p1 > model.p2);
      }
    }

    // Boost topConf when stats confirm
    const confirmBonus = (formOK === true ? 6 : 0) + (h2hOK === true ? 4 : 0);
    const topConf = confidence(topProb, topEV) + confirmBonus;

    const vigParts = [1/w1Odds, wxOdds ? 1/wxOdds : 0, 1/w2Odds];
    const margin = ((vigParts.reduce((a,b)=>a+b,0)-1)*100).toFixed(1);

    // Hot moment for UI verdict
    let hotMoment = 'НЕЙТРАЛЬНЫЙ';
    if (bestSig === 'high' && topEV >= 8) hotMoment = 'ГОРЯЧИЙ';
    else if (bestSig === 'high' || (bestSig === 'medium' && topEV >= 5)) hotMoment = 'ХОРОШИЙ';
    else if (bestSig === 'none') hotMoment = 'ХОЛОДНЫЙ';

    // Score distribution — remaining goals added to current score
    const scoreDistrib = {};
    if (isFootball) {
      for (let i = 0; i <= 6; i++) {
        for (let j = 0; j <= 6; j++) {
          const p = pPMF(i, lh) * pPMF(j, la);
          if (p >= 0.008) {
            const key = `${homeScore + i}-${awayScore + j}`; // use dash to avoid split issues
            scoreDistrib[key] = +p.toFixed(3);
          }
        }
      }
    }

    return {
      ...event,
      predictions: preds, bestSignal: bestSig, topEV, topConf: Math.min(95, topConf),
      momentum, leonMargin: margin,
      matchWinHomeProb: Math.round(model.p1 * 100),
      matchWinAwayProb: Math.round(model.p2 * 100),
      drawProb:         Math.round(model.px  * 100),
      momentumAdj:      +(scoreDiff * 1.5).toFixed(1),
      setWinHomeProb:   Math.round(model.p1 * 100),
      doneSets: [], currentPts: 0,
      hotMoment, scoreDistrib,
      setFavHome: model.p1 >= model.p2, setFavProb: Math.round(Math.max(model.p1, model.p2) * 100),
      histAgree: null, steamData: null, domData: null, nnProb: null, nnAgrees: null,
      formOK, h2hOK, fbStats,
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
  // extraData: { teamStats } for football (from SofaScore), null otherwise
  function analyze(event, bankroll = 1000, extraData = null) {
    const s = event.sport || 'tt';
    try {
      if (s === 'football' || s === 'hockey') return analyzeGoalSport(event, bankroll, s, extraData);
      if (s === 'tennis')                     return analyzeTennis(event, bankroll);
    } catch (e) {
      console.error(`[SportsEngine.${s}]`, e);
    }
    return null;
  }

  return { analyze, isSetDoneTennis };
})();