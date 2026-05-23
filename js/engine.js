// ============================================================
// TT Live Engine v7.0
// Рынки: Победитель матча · Тотал очков · Фора по сетам
// Алгоритмы: Point-level Markov + SMI + BPPI + RLP + Kelly
// ============================================================

const Engine = (() => {

  // ── Вспомогательные ──────────────────────────────────────
  function kelly(prob, odds, bank, frac = 0.25) {
    const b = odds - 1;
    const q = 1 - prob;
    const k = (b * prob - q) / b;
    const f = Math.max(0, k * frac);
    const stake = Math.max(Math.round(f * bank / 10) * 10, f > 0.001 ? 50 : 0);
    return { stake, pct: (f * 100).toFixed(1), raw: k };
  }

  function ev(prob, odds) {
    return ((prob * (odds - 1)) - (1 - prob)) * 100;
  }

  function noVigProb(w1odds, w2odds) {
    if (!w1odds || !w2odds) return { home: 0.5, away: 0.5 };
    const r1 = 1 / w1odds, r2 = 1 / w2odds, t = r1 + r2;
    return { home: r1 / t, away: r2 / t };
  }

  function isSetDone(h, a) {
    if (h >= 11 && h - a >= 2) return true;
    if (a >= 11 && a - h >= 2) return true;
    if (h >= 14 || a >= 14)    return true;
    return false;
  }

  // ── Вероятность выиграть партию (точечный Марков) ───────
  // Точнее чем простая формула: считаем DP по очкам
  const _setPCache = new Map();
  function setWinProbByScore(hPts, aPts, pp = 0.5) {
    if (isSetDone(hPts, aPts)) return hPts > aPts ? 1.0 : 0.0;
    const key = `${hPts}:${aPts}:${pp.toFixed(3)}`;
    if (_setPCache.has(key)) return _setPCache.get(key);

    // Deuce rule: at 10:10 (или выше), нужно 2 очка подряд
    function dpPoint(h, a) {
      if (isSetDone(h, a)) return h > a ? 1.0 : 0.0;
      // Счёт деюса: упрощаем до серии из 2 очков
      if (h >= 10 && a >= 10) {
        const p = pp, q = 1-pp;
        return (p*p) / (p*p + q*q); // P(home wins deuce)
      }
      const k = `${h}:${a}`;
      if (_setPCache.has(k+pp)) return _setPCache.get(k+pp);
      const v = pp * dpPoint(h+1, a) + (1-pp) * dpPoint(h, a+1);
      _setPCache.set(k+pp, v);
      return v;
    }

    // Оцениваем pp (вероятность выиграть очко) из текущего счёта
    const diff = hPts - aPts, total = hPts + aPts;
    // Нейтральная pp=0.5 скорректирована текущим счётом
    const progress = Math.min(1, total / 18);
    const rawPP = Math.max(0.30, Math.min(0.70, 0.5 + diff * (0.018 + progress * 0.025)));

    if (_setPCache.size > 2000) _setPCache.clear();
    const result = dpPoint(hPts, aPts);
    // Использовать rawPP как альтернативную оценку
    const r = 0.6 * result + 0.4 * Math.max(0.05, Math.min(0.95, 0.5 + diff * (0.04 + progress * 0.08)));
    _setPCache.set(key, r);
    return r;
  }

  // ── Вероятность выиграть матч (DP) ───────────────────────
  function matchWinProb(homeSets, awaySets, setWinP, setsToWin = 3) {
    if (homeSets >= setsToWin) return 1.0;
    if (awaySets >= setsToWin) return 0.0;
    const cache = {};
    function dp(h, a) {
      if (h >= setsToWin) return 1.0;
      if (a >= setsToWin) return 0.0;
      const key = `${h}_${a}`;
      if (cache[key] !== undefined) return cache[key];
      cache[key] = setWinP * dp(h + 1, a) + (1 - setWinP) * dp(h, a + 1);
      return cache[key];
    }
    return dp(homeSets, awaySets);
  }

  // ── Вероятности гандикапа по партиям (DP) ────────────────
  // Возвращает [P(хозяин выигрывает с форой), P(гость выигрывает с форой)]
  // hdpLine = -1.5 означает хозяин -1.5 (выигрывает 3:0 или 3:1)
  function handicapDP(hSets, aSets, setWinP, hdpLine, setsToWin = 3) {
    const cache = {};
    function dp(h, a) {
      if (h >= setsToWin) {
        const finalDiff = h - a; // e.g. 3-0=3, 3-1=2, 3-2=1
        const homeCovers = finalDiff + hdpLine > 0; // home -1.5: need diff >= 2
        return homeCovers ? [1, 0] : [0, 1];
      }
      if (a >= setsToWin) {
        const finalDiff = h - a; // e.g. 0-3=-3, 1-3=-2, 2-3=-1
        const homeCovers = finalDiff + hdpLine > 0;
        return homeCovers ? [1, 0] : [0, 1];
      }
      const key = `${h}:${a}`;
      if (cache[key]) return cache[key];
      const hw = dp(h + 1, a), aw = dp(h, a + 1);
      const r = [
        setWinP * hw[0] + (1 - setWinP) * aw[0],
        setWinP * hw[1] + (1 - setWinP) * aw[1],
      ];
      cache[key] = r;
      return r;
    }
    return dp(hSets, aSets);
  }

  // ── Ожидаемые очки в матче (для тотала очков) ────────────
  function expectedMatchPts(doneSets, clh, cla, setWinP, hSets, aSets, setsToWin) {
    const donePts  = doneSets.reduce((s, x) => s + x.home + x.away, 0);
    const curPts   = clh + cla;
    const avgSet   = doneSets.length > 0 ? donePts / doneSets.length : 21.5;
    const maxP     = Math.max(clh, cla);

    // Оставшиеся очки в текущей партии
    const estCurFinal = maxP >= 10
      ? curPts + Math.max(11 - maxP, 2) * 2
      : Math.max(curPts, avgSet);
    const remCur = Math.max(0, estCurFinal - curPts);

    // Ожидаемое число партий ПОСЛЕ текущей (DP)
    const cache = {};
    function dpS(h, a) {
      if (h >= setsToWin || a >= setsToWin) return 0;
      const key = `${h}:${a}`;
      if (cache[key] !== undefined) return cache[key];
      cache[key] = 1 + setWinP * dpS(h + 1, a) + (1 - setWinP) * dpS(h, a + 1);
      return cache[key];
    }
    const afterCurrent = setWinP * dpS(hSets + 1, aSets) + (1 - setWinP) * dpS(hSets, aSets + 1);

    return donePts + curPts + remCur + afterCurrent * avgSet;
  }

  // ── SMI — Set Momentum Index ──────────────────────────────
  function smi(doneSets) {
    if (!doneSets.length) return 0;
    const weights = [2.0, 1.6, 1.3, 1.0]; // [0] = самая последняя партия
    let wWins = 0, wTotal = 0;
    for (let i = 0; i < doneSets.length; i++) {
      const ri = doneSets.length - 1 - i; // ri=0 — последняя
      const w = weights[Math.min(ri, 3)];
      wWins  += (doneSets[i].home > doneSets[i].away ? 1 : 0) * w;
      wTotal += w;
    }
    return (wWins / wTotal - 0.5) * 0.10;
  }

  // ── BPPI — Big Points Performance Index ──────────────────
  function bppi(doneSets) {
    if (!doneSets.length) return 0;
    const margins = doneSets.map(s => s.home - s.away);
    const avg = margins.reduce((a, b) => a + b, 0) / margins.length;
    return (avg / 11) * 0.06;
  }

  // ── RLP — Recent Lead Pattern ─────────────────────────────
  function rlp(doneSets) {
    const recent = doneSets.slice(-2);
    if (!recent.length) return 0;
    const homeWins = recent.filter(s => s.home > s.away).length;
    return (homeWins / recent.length - 0.5) * 0.08;
  }

  // ── Прогноз ещё актуален? ─────────────────────────────────
  function isActionable(tag, hSets, aSets) {
    // Матч не завершён
    if (hSets >= 3 || aSets >= 3) return false;
    return true;
  }

  // ── Сигнал и уверенность ─────────────────────────────────
  function signalLevel(evPct, prob, edge) {
    const e = edge || 0;
    if (evPct >= 8  && prob >= 0.64 && e >= 0.05) return 'high';
    if (evPct >= 4  && prob >= 0.58 && e >= 0.03) return 'medium';
    if (evPct >= 1.5 && prob >= 0.54 && e >= 0.02) return 'low';
    return 'none';
  }

  function confidence(prob, evPct, setsPlayed) {
    let score = Math.round(prob * 100);
    if (evPct > 8)      score = Math.min(score + 9, 97);
    else if (evPct > 4) score = Math.min(score + 5, 95);
    else if (evPct < 0) score = Math.max(score - 10, 20);
    if (setsPlayed >= 2) score = Math.min(score + 3, 97);
    return Math.max(20, Math.min(97, score));
  }

  // ── ГЛАВНАЯ ФУНКЦИЯ ───────────────────────────────────────
  function analyze(event, bankroll = 1000) {
    const {
      homeTeam, awayTeam, homeSets, awaySets,
      sets, currentSetNum, currentHomePts, currentAwayPts,
      w1Odds, w2Odds,
      totalOverOdds, totalUnderOdds, totalLine,
      hdpHomeOdds, hdpAwayOdds, hdpLine,
      leonUrl,
    } = event;

    const setsToWin = 3;
    const doneSets  = (sets || []).filter(s => isSetDone(s.home, s.away));
    const totalSetsPlayed = homeSets + awaySets;

    // ── 1. Вероятность выиграть текущую партию ─────────────
    const setWinHomeRaw = Math.max(0.03, Math.min(0.97,
      setWinProbByScore(currentHomePts, currentAwayPts)
    ));

    // ── 2. Корректировка по истории + SMI/BPPI/RLP ─────────
    let avgSetWin = 0.5;
    if (doneSets.length >= 1) {
      const hw = doneSets.filter(s => s.home > s.away).length;
      avgSetWin = (hw + 0.5) / (doneSets.length + 1);
    }
    const momentumAdj = smi(doneSets) + bppi(doneSets) + rlp(doneSets);
    const setWinHomeFinal = Math.max(0.05, Math.min(0.95,
      0.65 * setWinHomeRaw + 0.35 * avgSetWin + momentumAdj
    ));

    // ── 3. Вероятность победы в матче ──────────────────────
    const matchWinHomeModel = matchWinProb(homeSets, awaySets, setWinHomeFinal, setsToWin);
    const marketProbs = noVigProb(w1Odds, w2Odds);

    const trueHomeProb = (w1Odds && w2Odds)
      ? 0.55 * matchWinHomeModel + 0.45 * marketProbs.home
      : matchWinHomeModel;
    const trueAwayProb = 1 - trueHomeProb;

    const effW1 = w1Odds || Math.max(1.1, (1 / matchWinHomeModel) * 0.93);
    const effW2 = w2Odds || Math.max(1.1, (1 / (1 - matchWinHomeModel)) * 0.93);

    const evM1 = ev(trueHomeProb, effW1);
    const evM2 = ev(trueAwayProb, effW2);

    // ── 4. Тотал очков ─────────────────────────────────────
    let totalOverProb = null;
    if (totalOverOdds && totalUnderOdds && totalLine) {
      const expPts = expectedMatchPts(
        doneSets, currentHomePts, currentAwayPts,
        setWinHomeFinal, homeSets, awaySets, setsToWin
      );
      const diff = expPts - totalLine;
      // Логистическая функция: σ ≈ 8-10 очков для матча
      totalOverProb = Math.max(0.1, Math.min(0.9, 0.5 + diff * 0.033));
    }

    // ── 5. Гандикап по сетам ───────────────────────────────
    let hdpHomeProb = null, hdpAwayProb = null;
    if (hdpHomeOdds && hdpAwayOdds && hdpLine !== null) {
      const [ph, pa] = handicapDP(homeSets, awaySets, setWinHomeFinal, hdpLine, setsToWin);
      hdpHomeProb = ph;
      hdpAwayProb = pa;
    }

    // ── Моментум для UI ───────────────────────────────────
    const rawMom = 50 + (currentHomePts - currentAwayPts) * 5 + momentumAdj * 100;
    const momentum = Math.max(5, Math.min(95, Math.round(rawMom)));

    // ── Сборка прогнозов ──────────────────────────────────
    const preds = [];

    const addPred = (tag, market, label, prob, mktProb, odds, evPct, predictedHome) => {
      if (!isActionable(tag, homeSets, awaySets)) return;
      const edge = prob - (mktProb || prob - 0.01);
      const sig = signalLevel(evPct, prob, edge);
      if (sig === 'none') return;
      preds.push({
        tag, market, label, prob, odds, evPct,
        kelly: kelly(prob, odds, bankroll),
        signal: sig,
        predictedHome,
      });
    };

    // А) Победитель матча
    if (trueHomeProb >= 0.55) {
      addPred('match', 'Победитель', homeTeam, trueHomeProb, marketProbs.home, effW1, evM1, true);
    } else if (trueAwayProb >= 0.55) {
      addPred('match', 'Победитель', awayTeam, trueAwayProb, marketProbs.away, effW2, evM2, false);
    }

    // Б) Тотал очков
    if (totalOverProb !== null && totalOverOdds && totalUnderOdds) {
      const label = `${totalLine}`;
      const tot = 1/totalOverOdds + 1/totalUnderOdds;
      const mktOver = (1/totalOverOdds) / tot;
      if (totalOverProb >= 0.55) {
        addPred('total', `Тотал очков (${label})`,
          `Больше ${label}`, totalOverProb, mktOver, totalOverOdds,
          ev(totalOverProb, totalOverOdds), null);
      } else if (1 - totalOverProb >= 0.55) {
        addPred('total', `Тотал очков (${label})`,
          `Меньше ${label}`, 1 - totalOverProb, 1-mktOver, totalUnderOdds,
          ev(1 - totalOverProb, totalUnderOdds), null);
      }
    }

    // В) Гандикап по сетам
    if (hdpHomeProb !== null && hdpHomeOdds && hdpAwayOdds) {
      const awayHdpLine = hdpLine !== null ? -hdpLine : null;
      const hdpSign = hdpLine > 0 ? '+' : '';
      const hdpTot = 1/hdpHomeOdds + 1/hdpAwayOdds;
      const mktHdpH = (1/hdpHomeOdds) / hdpTot;
      if (hdpHomeProb >= 0.55) {
        addPred('handicap', 'Фора по сетам',
          `${homeTeam} (${hdpSign}${hdpLine})`,
          hdpHomeProb, mktHdpH, hdpHomeOdds, ev(hdpHomeProb, hdpHomeOdds), true);
      } else if (hdpAwayProb >= 0.55) {
        const awaySign = awayHdpLine > 0 ? '+' : '';
        addPred('handicap', 'Фора по сетам',
          `${awayTeam} (${awaySign}${awayHdpLine})`,
          hdpAwayProb, 1-mktHdpH, hdpAwayOdds, ev(hdpAwayProb, hdpAwayOdds), false);
      }
    }

    preds.sort((a, b) => b.evPct - a.evPct);

    const bestSig = preds[0]?.signal || 'none';
    const topEV   = preds[0]?.evPct  || 0;
    const topProb = preds[0]?.prob    || 0.5;
    const topConf = confidence(topProb, topEV, totalSetsPlayed);

    const leonMargin = (w1Odds && w2Odds)
      ? ((1 / w1Odds + 1 / w2Odds - 1) * 100).toFixed(1)
      : null;

    return {
      ...event,
      predictions: preds,
      bestSignal: bestSig,
      topEV, topConf,
      momentum,
      leonMargin,
      matchWinHomeProb: Math.round(trueHomeProb * 100),
      matchWinAwayProb: Math.round(trueAwayProb * 100),
      setWinHomeProb:   Math.round(setWinHomeRaw * 100),
      doneSets,
      currentPts: currentHomePts + currentAwayPts,
      momentumAdj: +(momentumAdj * 100).toFixed(1),
    };
  }

  return { analyze, isSetDone };
})();