// ============================================================
// TT Live Engine v11.0
// Источники сигнала:
//   1. Текущий счёт + нестабильность (дюс = нет сигнала)
//   2. История партий матча (моментум, BPPI, RLP)
//   3. Архив игрока (win rate, форма, H2H, сеты, очки)
//   4. Движение котировок (умные деньги / стим)
//   5. Доминирование по очкам (насколько убедительны победы)
// HIGH = математика + (архив ИЛИ стим), нет дюса, нет противоречий
// ============================================================

const Engine = (() => {

  // ── Вспомогательные ──────────────────────────────────────
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

  function noVigProb(o1, o2) {
    if (!o1 || !o2) return { home: 0.5, away: 0.5 };
    const r1 = 1/o1, r2 = 1/o2, t = r1+r2;
    return { home: r1/t, away: r2/t };
  }

  function isSetDone(h, a) {
    if (h >= 11 && h - a >= 2) return true;
    if (a >= 11 && a - h >= 2) return true;
    if (h >= 14 || a >= 14)    return true;
    return false;
  }

  // ── Вероятность победы в партии по счёту ─────────────────
  // Учитываем близость к дюсу — снижаем уверенность
  function setWinProb(hPts, aPts) {
    if (isSetDone(hPts, aPts)) return hPts > aPts ? 1.0 : 0.0;

    const diff = hPts - aPts;
    const maxP = Math.max(hPts, aPts);
    const minP = Math.min(hPts, aPts);

    // Дюс: очень близко к равной игре
    if (hPts >= 9 && aPts >= 9) {
      // На деюсе вероятность пропорциональна разнице
      return Math.max(0.05, Math.min(0.95, 0.5 + diff * 0.22));
    }
    // Один игрок достиг 10, другой ≤ 8 — явное преимущество
    if (maxP >= 10) {
      const leader = hPts >= 10 ? 'home' : 'away';
      const d = Math.abs(diff);
      const p = 1 - Math.pow(0.5, d);
      return leader === 'home' ? p : 1 - p;
    }
    // Прогресс в партии
    const progress = maxP / 10;
    const scale = 0.04 + progress * 0.10;
    return Math.max(0.04, Math.min(0.96, 0.5 + diff * scale));
  }

  // ── Нестабильность ситуации (0 = стабильно, 1 = хаос) ────
  // Высокая нестабильность → не генерируем сигнал
  function situationInstability(hPts, aPts) {
    const diff = Math.abs(hPts - aPts);
    const maxP = Math.max(hPts, aPts);

    // Дюс: максимальная нестабильность
    if (hPts >= 9 && aPts >= 9 && diff <= 2) return 0.9;
    // Конец партии, близкий счёт
    if (maxP >= 9 && diff <= 2) return 0.7;
    // Середина партии, близкий счёт
    if (diff <= 1 && maxP >= 4) return 0.5;
    // Явное преимущество
    if (diff >= 5) return 0.0;
    if (diff >= 3) return 0.2;
    return 0.35;
  }

  // ── P(победа в матче) через DP ────────────────────────────
  function matchWinProb(hSets, aSets, setWinP, stw = 3) {
    if (hSets >= stw) return 1.0;
    if (aSets >= stw) return 0.0;
    const cache = {};
    function dp(h, a) {
      if (h >= stw) return 1.0;
      if (a >= stw) return 0.0;
      const k = `${h}_${a}`;
      if (cache[k] !== undefined) return cache[k];
      return (cache[k] = setWinP * dp(h+1, a) + (1-setWinP) * dp(h, a+1));
    }
    return dp(hSets, aSets);
  }

  // ── P(гандикап по сетам) через DP ────────────────────────
  function handicapDP(hSets, aSets, setWinP, hdpLine, stw = 3) {
    const cache = {};
    function dp(h, a) {
      if (h >= stw || a >= stw) {
        return (h - a) + hdpLine > 0 ? [1, 0] : [0, 1];
      }
      const k = `${h}:${a}`;
      if (cache[k]) return cache[k];
      const hw = dp(h+1, a), aw = dp(h, a+1);
      return (cache[k] = [
        setWinP*hw[0] + (1-setWinP)*aw[0],
        setWinP*hw[1] + (1-setWinP)*aw[1],
      ]);
    }
    return dp(hSets, aSets);
  }

  // ── Ожидаемое количество очков в матче ───────────────────
  function expectedMatchPts(doneSets, clh, cla, setWinP, hSets, aSets, stw) {
    const donePts = doneSets.reduce((s, x) => s + x.home + x.away, 0);
    const curPts  = clh + cla;
    const avgSet  = doneSets.length > 0 ? donePts / doneSets.length : 21.5;
    const maxP    = Math.max(clh, cla);

    const estCurFinal = maxP >= 10
      ? curPts + Math.max(11 - maxP, 2) * 2
      : Math.max(curPts, avgSet);
    const remCur = Math.max(0, estCurFinal - curPts);

    const cache = {};
    function dpS(h, a) {
      if (h >= stw || a >= stw) return 0;
      const k = `${h}:${a}`;
      if (cache[k] !== undefined) return cache[k];
      return (cache[k] = 1 + setWinP*dpS(h+1, a) + (1-setWinP)*dpS(h, a+1));
    }
    const afterCur = setWinP*dpS(hSets+1, aSets) + (1-setWinP)*dpS(hSets, aSets+1);
    return donePts + curPts + remCur + afterCur * avgSet;
  }

  // ── Доминирование по очкам в партиях ─────────────────────
  // Как убедительно побеждает каждый игрок (avg margin per set won)
  // Возвращает score: >0 = дом доминирует, <0 = гость доминирует
  function pointDominance(doneSets) {
    if (!doneSets.length) return { score: 0, homeAvg: 0, awayAvg: 0, decisive: false };
    const hMargins = doneSets.filter(s => s.home > s.away).map(s => s.home - s.away);
    const aMargins = doneSets.filter(s => s.away > s.home).map(s => s.away - s.home);
    const hAvg = hMargins.length ? hMargins.reduce((a,b)=>a+b,0)/hMargins.length : 0;
    const aAvg = aMargins.length ? aMargins.reduce((a,b)=>a+b,0)/aMargins.length : 0;
    // Взвешенный счёт с учётом количества побед
    const hScore = hAvg * hMargins.length;
    const aScore = aAvg * aMargins.length;
    const score  = (hScore - aScore) / doneSets.length;
    return {
      score: +(score / 6).toFixed(2),   // нормализовано -1..1
      homeAvg: +hAvg.toFixed(1),
      awayAvg: +aAvg.toFixed(1),
      decisive: hAvg >= 5 || aAvg >= 5, // кто-то выигрывает «разгромом»
    };
  }

  // ── Умные деньги (steam) ──────────────────────────────────
  // drift > 0 значит кф упали = ставили на этого игрока
  function steamSignal(movement, favorsHome) {
    if (!movement) return { agrees: null, strength: 0 };
    const drift = favorsHome ? movement.w1Drift : movement.w2Drift;
    if (!drift || Math.abs(drift) < 3) return { agrees: null, strength: 0 };
    const agrees = drift > 0; // кф упали на нашего игрока = умные деньги за нас
    const strength = Math.min(1, Math.abs(drift) / 15);
    return { agrees, strength };
  }

  // ── SMI — взвешенный моментум по партиям ─────────────────
  function smi(doneSets) {
    if (!doneSets.length) return 0;
    const weights = [2.5, 1.8, 1.3, 1.0]; // [0] = последняя
    let wW = 0, wT = 0;
    for (let i = 0; i < doneSets.length; i++) {
      const ri = doneSets.length - 1 - i;
      const w  = weights[Math.min(ri, 3)];
      wW += (doneSets[i].home > doneSets[i].away ? 1 : 0) * w;
      wT += w;
    }
    return (wW / wT - 0.5) * 0.12;
  }

  // ── BPPI — доминирование по очкам в партиях ──────────────
  function bppi(doneSets) {
    if (!doneSets.length) return 0;
    const margins = doneSets.map(s => s.home - s.away);
    const avg = margins.reduce((a, b) => a + b, 0) / margins.length;
    return (avg / 11) * 0.05;
  }

  // ── RLP — паттерн последних партий ───────────────────────
  function rlp(doneSets) {
    const recent = doneSets.slice(-2);
    if (!recent.length) return 0;
    const hw = recent.filter(s => s.home > s.away).length;
    return (hw / recent.length - 0.5) * 0.07;
  }

  // ── Архивный анализ ───────────────────────────────────────
  // Принимает history от /api/player-stats, возвращает {agree, strength, label}
  function evalHistory(history, modelFavorsHome) {
    if (!history) return { agree: null, strength: 0, label: null };
    const p1  = history.p1;   // home player stats
    const p2  = history.p2;   // away player stats
    const h2h = history.h2h;
    const signals = [];

    // Win rate signal (нужно >= 8 матчей у каждого)
    if (p1 && p2 && p1.matches >= 8 && p2.matches >= 8) {
      const diff = p1.winRate - p2.winRate;
      if (Math.abs(diff) >= 0.08) {
        signals.push({ favHome: diff > 0, strength: Math.min(1, Math.abs(diff) / 0.35) });
      }
    }

    // H2H signal (нужно >= 3 встречи)
    if (h2h && h2h.total >= 3) {
      const rate = h2h.p1Wins / h2h.total;
      const diff = rate - 0.5;
      if (Math.abs(diff) >= 0.15) {
        const w = Math.min(h2h.total, 12) / 12;
        signals.push({ favHome: diff > 0, strength: Math.min(1, Math.abs(diff) / 0.4) * w });
      }
    }

    // Recent form signal (последние 5 матчей)
    if (p1 && p2 && p1.form && p1.form.length >= 3 && p2.form && p2.form.length >= 3) {
      const r1 = p1.form.filter(f => f === 'W').length / p1.form.length;
      const r2 = p2.form.filter(f => f === 'W').length / p2.form.length;
      const diff = r1 - r2;
      if (Math.abs(diff) >= 0.2) {
        signals.push({ favHome: diff > 0, strength: Math.abs(diff) * 0.6 });
      }
    }

    if (!signals.length) return { agree: null, strength: 0, label: '—' };

    const agreeCount = signals.filter(s => s.favHome === modelFavorsHome).length;
    const strength   = signals.reduce((s, x) => s + x.strength, 0) / signals.length;
    const agree      = agreeCount > signals.length - agreeCount;

    // Build label for UI
    const parts = [];
    if (p1 && p2 && p1.matches >= 5) {
      parts.push(`${(p1.winRate*100).toFixed(0)}% vs ${(p2.winRate*100).toFixed(0)}%`);
    }
    if (h2h && h2h.total >= 3) {
      parts.push(`H2H ${h2h.p1Wins}-${h2h.p2Wins}`);
    }
    if (p1 && p1.form.length >= 3) {
      parts.push(`Форма: ${p1.form.join('')} / ${(p2 && p2.form || []).join('')}`);
    }
    const prefix = agree ? '✅' : '⚠️';
    const label  = parts.length ? `${prefix} ${parts.join(' · ')}` : null;

    return { agree, strength, label, signals: signals.length };
  }

  // ── Уровень сигнала ───────────────────────────────────────
  // HIGH = математика + минимум 1 из: архив / стим / доминирование / нейросеть
  function signalLevel(evPct, prob, instab, histAgree, histStrength, steamAgrees, domScore, nnAgrees) {
    if (instab > 0.6) return 'none';

    const archiveOK = histAgree  === true && histStrength >= 0.22;
    const steamOK   = steamAgrees === true;
    const domOK     = Math.abs(domScore || 0) >= 0.3;
    const nnOK      = nnAgrees   === true;

    const confirmations = (archiveOK?1:0) + (steamOK?1:0) + (domOK?1:0) + (nnOK?1:0);
    if (evPct >= 5.5 && prob >= 0.63 && instab <= 0.25 && confirmations >= 1) return 'high';

    // MEDIUM: хорошая математика, нет противоречий архива
    if (evPct >= 3 && prob >= 0.58 && instab <= 0.38 && histAgree !== false) return 'medium';
    if (evPct >= 4.5 && prob >= 0.61 && instab <= 0.3) return 'medium';

    // LOW: слабый сигнал
    if (evPct >= 1.5 && prob >= 0.55 && instab <= 0.5) return 'low';
    return 'none';
  }

  function confidence(prob, evPct, setsPlayed, instab) {
    let s = Math.round(prob * 100);
    if (evPct > 9)      s = Math.min(s + 8, 95);
    else if (evPct > 5) s = Math.min(s + 5, 93);
    else if (evPct > 2) s = Math.min(s + 2, 90);
    else if (evPct < 0) s = Math.max(s - 8, 20);
    if (setsPlayed >= 2) s = Math.min(s + 4, 95);
    // Снижаем уверенность при нестабильности
    s = Math.round(s * (1 - instab * 0.3));
    return Math.max(20, Math.min(95, s));
  }

  // ── ГЛАВНАЯ ФУНКЦИЯ ───────────────────────────────────────
  function analyze(event, bankroll = 1000, history = null, oddsMovement = null, scoreData = null) {
    const {
      homeTeam, awayTeam, homeSets, awaySets,
      sets, currentSetNum, currentHomePts, currentAwayPts,
      w1Odds, w2Odds,
      totalOverOdds, totalUnderOdds, totalLine,
      hdpHomeOdds, hdpAwayOdds, hdpLine,
    } = event;

    const stw      = 3;
    const doneSets = (sets || []).filter(s => isSetDone(s.home, s.away));
    const setsPlayed = homeSets + awaySets;

    // Матч закончен
    if (homeSets >= stw || awaySets >= stw) {
      return {
        ...event, predictions: [], bestSignal: 'none', topEV: 0, topConf: 0,
        momentum: 50, leonMargin: null,
        matchWinHomeProb: homeSets >= stw ? 100 : 0,
        matchWinAwayProb: awaySets >= stw ? 100 : 0,
        setWinHomeProb: 50, doneSets, currentPts: 0, momentumAdj: 0,
      };
    }

    // ── 1. Нестабильность текущей ситуации ────────────────
    const instab = situationInstability(currentHomePts, currentAwayPts);

    // ── 2. Вероятность выиграть текущую партию ─────────────
    const setWinRaw = setWinProb(currentHomePts, currentAwayPts);

    // ── 3. Моментум, история, доминирование ──────────────
    let avgSetWin = 0.5;
    if (doneSets.length >= 1) {
      const hw = doneSets.filter(s => s.home > s.away).length;
      avgSetWin = (hw + 0.5) / (doneSets.length + 1);
    }
    const momentumAdj = smi(doneSets) + bppi(doneSets) + rlp(doneSets);
    const domData = pointDominance(doneSets); // доминирование по очкам

    // Вес истории растёт с числом сыгранных партий
    const histWeight = Math.min(0.45, doneSets.length * 0.15);
    const setWinFinal = Math.max(0.05, Math.min(0.95,
      (1 - histWeight) * setWinRaw + histWeight * (avgSetWin + momentumAdj)
    ));

    // ── 4. Вероятность победы в матче ─────────────────────
    const matchModel = matchWinProb(homeSets, awaySets, setWinFinal, stw);
    const mktProbs   = noVigProb(w1Odds, w2Odds);

    // Финальная вероятность: блендинг модели и рынка
    const modelWeight = Math.min(0.70, 0.40 + doneSets.length * 0.12);
    let trueHome = Math.max(0.05, Math.min(0.95,
      modelWeight * matchModel + (1 - modelWeight) * mktProbs.home
    ));

    // ── Архивная коррекция ────────────────────────────────
    const hist = evalHistory(history, trueHome > 0.5);
    if (hist.agree !== null && hist.strength > 0.15) {
      const dir = trueHome > 0.5 ? 1 : -1;
      if (hist.agree) {
        // Архив подтверждает — усиливаем уверенность
        trueHome = Math.min(0.92, trueHome + dir * hist.strength * 0.07);
      } else {
        // Архив противоречит — ослабляем к 0.5
        trueHome = 0.5 + (trueHome - 0.5) * (1 - hist.strength * 0.45);
      }
      trueHome = Math.max(0.05, Math.min(0.95, trueHome));
    }

    // ── Стим (умные деньги) ────────────────────────────────
    const steam = steamSignal(oddsMovement, trueHome > 0.5);
    if (steam.agrees === true && steam.strength > 0.2) {
      // Умные деньги на нашего игрока — усиливаем
      const dir = trueHome > 0.5 ? 1 : -1;
      trueHome = Math.min(0.93, trueHome + dir * steam.strength * 0.06);
    } else if (steam.agrees === false && steam.strength > 0.3) {
      // Умные деньги против нашего игрока — ослабляем
      trueHome = 0.5 + (trueHome - 0.5) * (1 - steam.strength * 0.4);
    }
    trueHome = Math.max(0.05, Math.min(0.95, trueHome));

    // Доминирование: если дом. игрок выигрывает разгромом — поддерживаем прогноз
    if (domData.decisive && domData.score > 0.3) {
      trueHome = Math.min(0.93, trueHome + 0.025);
    } else if (domData.decisive && domData.score < -0.3) {
      trueHome = Math.max(0.07, trueHome - 0.025);
    }

    // ── Elo коррекция ─────────────────────────────────────
    const eloProb = history?.elo?.homeProb;
    if (eloProb !== undefined && Math.abs(eloProb - 0.5) >= 0.05) {
      const eloDir   = eloProb > 0.5 ? 1 : -1;
      const modelDir = trueHome > 0.5 ? 1 : -1;
      if (eloDir === modelDir) {
        trueHome = Math.min(0.92, trueHome + eloDir * Math.abs(eloProb - 0.5) * 0.04);
      } else {
        trueHome = 0.5 + (trueHome - 0.5) * 0.94;
      }
      trueHome = Math.max(0.05, Math.min(0.95, trueHome));
    }

    // ── Серия очков (runs boost) ──────────────────────────
    if (scoreData && scoreData.recentRun !== 0) {
      const runDir   = scoreData.recentRun > 0 ? 1 : -1;
      const modelDir = trueHome > 0.5 ? 1 : -1;
      if (runDir === modelDir) {
        trueHome = Math.min(0.93, Math.max(0.07, trueHome + runDir * 0.012));
      }
    }

    // ── Нейросеть (обученная на матчах Леона) ─────────────
    const nnProb = (typeof event.nnProb === 'number') ? event.nnProb : null;
    if (nnProb !== null) {
      const nnP   = nnProb / 100;
      const delta = Math.abs(nnP - 0.5);
      if (delta >= 0.07) {
        const nnDir    = nnP      > 0.5 ? 1 : -1;
        const modelDir = trueHome > 0.5 ? 1 : -1;
        if (nnDir === modelDir) {
          trueHome = Math.min(0.93, trueHome + nnDir * delta * 0.06);
        } else {
          trueHome = 0.5 + (trueHome - 0.5) * 0.88;
        }
        trueHome = Math.max(0.05, Math.min(0.95, trueHome));
      }
    }
    const nnAgrees = (nnProb !== null && Math.abs(nnProb/100 - 0.5) >= 0.07)
      ? (nnProb > 50) === (trueHome > 0.5)
      : null;

    const trueAway = 1 - trueHome;

    const effW1 = w1Odds || Math.max(1.05, 1 / (trueHome * 0.94));
    const effW2 = w2Odds || Math.max(1.05, 1 / (trueAway * 0.94));

    const evM1 = ev(trueHome, effW1);
    const evM2 = ev(trueAway, effW2);

    // ── 5. Тотал очков ────────────────────────────────────
    let totalOverProb = null;
    if (totalOverOdds && totalUnderOdds && totalLine) {
      const expPts = expectedMatchPts(
        doneSets, currentHomePts, currentAwayPts,
        setWinFinal, homeSets, awaySets, stw
      );
      const diff = expPts - totalLine;
      // Логистическая кривая, чуть более агрессивная чем раньше
      totalOverProb = Math.max(0.08, Math.min(0.92, 0.5 + diff * 0.036));
    }

    // ── 6. Гандикап по сетам ─────────────────────────────
    let hdpHomeProb = null, hdpAwayProb = null;
    if (hdpLine !== null && hdpLine !== undefined && hdpHomeOdds && hdpAwayOdds) {
      [hdpHomeProb, hdpAwayProb] = handicapDP(homeSets, awaySets, setWinFinal, hdpLine, stw);
    }

    // ── 7. Моментум для UI ────────────────────────────────
    const rawMom = 50 + (currentHomePts - currentAwayPts) * 5 + momentumAdj * 80;
    const momentum = Math.max(5, Math.min(95, Math.round(rawMom)));

    // ── 8. Сборка прогнозов ───────────────────────────────
    const preds = [];

    function addPred(tag, market, label, prob, mktProb, odds, evPct, ph) {
      if (!odds || odds <= 1.05) return;
      if (!isActionable(homeSets, awaySets)) return;
      const sig = signalLevel(evPct, prob, instab, hist.agree, hist.strength, steam.agrees, domData.score, nnAgrees);
      if (sig === 'none') return;
      preds.push({
        tag, market, label, prob, odds, evPct,
        kelly: kelly(prob, odds, bankroll),
        signal: sig, predictedHome: ph,
      });
    }

    // А) Победитель матча
    // Требуем минимальное расхождение модели с рынком для достоверности
    if (trueHome >= 0.57) {
      addPred('match', 'Победитель', homeTeam, trueHome, mktProbs.home, effW1, evM1, true);
    } else if (trueAway >= 0.57) {
      addPred('match', 'Победитель', awayTeam, trueAway, mktProbs.away, effW2, evM2, false);
    }

    // Б) Тотал очков
    if (totalOverProb !== null && totalOverOdds && totalUnderOdds) {
      const mktT = noVigProb(totalOverOdds, totalUnderOdds);
      const evO  = ev(totalOverProb, totalOverOdds);
      const evU  = ev(1-totalOverProb, totalUnderOdds);
      if (totalOverProb >= 0.57) {
        addPred('total', `Тотал очков (${totalLine})`, `Больше ${totalLine}`,
          totalOverProb, mktT.home, totalOverOdds, evO, null);
      } else if (1-totalOverProb >= 0.57) {
        addPred('total', `Тотал очков (${totalLine})`, `Меньше ${totalLine}`,
          1-totalOverProb, mktT.away, totalUnderOdds, evU, null);
      }
    }

    // В) Гандикап по сетам
    if (hdpHomeProb !== null && hdpHomeOdds && hdpAwayOdds) {
      const awayHdp = -(hdpLine || 0);
      const hdpSign = (hdpLine || 0) > 0 ? '+' : '';
      const mktH = noVigProb(hdpHomeOdds, hdpAwayOdds);
      if (hdpHomeProb >= 0.57) {
        addPred('handicap', 'Фора по сетам',
          `${homeTeam} (${hdpSign}${hdpLine})`,
          hdpHomeProb, mktH.home, hdpHomeOdds, ev(hdpHomeProb, hdpHomeOdds), true);
      } else if (hdpAwayProb >= 0.57) {
        const aSign = awayHdp > 0 ? '+' : '';
        addPred('handicap', 'Фора по сетам',
          `${awayTeam} (${aSign}${awayHdp})`,
          hdpAwayProb, mktH.away, hdpAwayOdds, ev(hdpAwayProb, hdpAwayOdds), false);
      }
    }

    preds.sort((a, b) => b.evPct - a.evPct);

    const bestSig    = preds[0]?.signal || 'none';
    const topEV      = preds[0]?.evPct  || 0;
    const topProb    = preds[0]?.prob    || 0.5;
    const topConf    = confidence(topProb, topEV, setsPlayed, instab);
    const scoreDistrib = matchScoreDistrib(homeSets, awaySets, setWinFinal, stw);

    const leonMargin = (w1Odds && w2Odds)
      ? ((1/w1Odds + 1/w2Odds - 1) * 100).toFixed(1) : null;

    return {
      ...event,
      predictions: preds, bestSignal: bestSig, topEV, topConf,
      momentum, leonMargin,
      matchWinHomeProb: Math.round(trueHome * 100),
      matchWinAwayProb: Math.round(trueAway * 100),
      setWinHomeProb:   Math.round(setWinRaw * 100),
      doneSets, currentPts: currentHomePts + currentAwayPts,
      momentumAdj: +(momentumAdj * 100).toFixed(1),
      histLabel:   hist.label,
      histAgree:   hist.agree,
      histStrength: hist.strength,
      histLoaded:  history !== null,
      domData,
      steamData:   { ...steam, drift: oddsMovement },
      scoreDistrib,
      nnProb,  nnAgrees,
      _scoreVel:   scoreData ? { home: scoreData.homeVel, away: scoreData.awayVel, run: scoreData.recentRun } : null,
      _eloData:    history?.elo || null,
      _instab: +instab.toFixed(2),
      _setWinFinal: +setWinFinal.toFixed(3),
    };
  }

  // ── Распределение итогового счёта матча ──────────────────
  // Возвращает {score: prob} напр. {"3:0":0.125,"3:1":0.23,...}
  function matchScoreDistrib(hSets, aSets, setWinP, stw = 3) {
    const p = setWinP, q = 1 - p;
    const result = {};
    function dp(h, a, prob) {
      if (h >= stw || a >= stw) {
        const k = `${h}:${a}`;
        result[k] = (result[k] || 0) + prob;
        return;
      }
      dp(h + 1, a, prob * p);
      dp(h, a + 1, prob * q);
    }
    dp(hSets, aSets, 1.0);
    const out = {};
    for (const [k, v] of Object.entries(result)) out[k] = +v.toFixed(3);
    return out;
  }

  function isActionable(hSets, aSets) {
    return hSets < 3 && aSets < 3;
  }

  return { analyze, isSetDone, matchScoreDistrib };
})();