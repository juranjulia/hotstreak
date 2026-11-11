// 吉祥物大狂奔 —— 比赛引擎（服务器和模拟共用）
// 卡牌构成以《Hot Streak Card Deck V2》为准
'use strict';

const MASCOTS = [
  { id: 'lion', name: '舞狮' },     // 赛道 1（最上）
  { id: 'cat',  name: '招财猫' },   // 赛道 2
  { id: 'dog',  name: '边牧' },     // 赛道 3
  { id: 'frog', name: '青蛙' },     // 赛道 4（最下）
];
const LANES = 4;
// 赛道参数：last = 正式赛道最后一格（终点线前一格）；stars 最后一个在终点线之后（到达即冲线）
// white = 折叠线：第 k 次折叠后必须到达 white[k-1] 格（含）以上；最后一条白线到终点线之间是“冲刺区”
const TRACK = {
  last: 9,                 // 第 1~9 格，跑过第 9 格即冲线
  stars: [3, 6, 9, 10],    // 第 10 格在终点线之后
  back: -3,                // 黄色缓冲区：第 -1 ~ -3 格
  white: [3, 5, 7],        // 白线①②③；第 7~9 格是冲刺区
};
const BURN = 3;

// ---------------- 卡牌（53 张） ----------------
// 每个吉祥物 11 张：起跑牌（恢复 +2，每场必定加入）、摔倒、掉头、+3、+2、−2、星星、
//   +1/+2/+3 后转弯（左边两条赛道向右转、右边两条向左转，即都朝赛道中间）、恢复 +1
// 全体牌 9 张：恢复 +2、恢复 +3、+1 ×2、+2 ×2、+3 ×2、−2（不碰撞，不能冲线）
function defaultConfig() {
  return {
    startMove: 2,
    perMascot: [['fall'], ['turn'], ['num', 3], ['num', 2], ['num', -2], ['star'],
      ['swerve', 1, 'in'], ['swerve', 2, 'in'], ['swerve', 3, 'in'], ['recover', 1]],
    green: [['all-recover', 2], ['all-recover', 3], ['all-num', 1], ['all-num', 1],
      ['all-num', 2], ['all-num', 2], ['all-num', 3], ['all-num', 3], ['all-num', -2]],
  };
}

function buildPool(cfg = defaultConfig()) {
  const cards = [];
  let k = 0;
  const add = c => { c.id = 'k' + (++k); cards.push(c); return c; };
  MASCOTS.forEach((_, m) => add({ kind: 'start', m, n: cfg.startMove }));
  MASCOTS.forEach((_, m) => cfg.perMascot.forEach(([kind, n, dir]) => {
    if (dir === 'in') dir = m < 2 ? 'R' : 'L';
    if (dir === 'out') dir = m < 2 ? 'L' : 'R';
    add({ kind, m, n, dir });
  }));
  cfg.green.forEach(([kind, n]) => add({ kind, m: null, n }));
  return cards;
}

function cardText(c) {
  const who = c.m != null ? MASCOTS[c.m].name : '全体';
  const sg = n => (n > 0 ? '+' + n : String(n));
  switch (c.kind) {
    case 'start': return `${who} 起跑：恢复后 ${sg(c.n)}`;
    case 'num': return `${who} ${sg(c.n)}`;
    case 'star': return `${who} ★ 星星`;
    case 'fall': return `${who} 摔倒`;
    case 'turn': return `${who} 掉头`;
    case 'swerve': return `${who} ${sg(c.n)} 后${c.dir === 'L' ? '向左' : '向右'}转弯`;
    case 'recover': return `${who} 恢复后 ${sg(c.n)}`;
    case 'all-num': return `全体 ${sg(c.n)}`;
    case 'all-recover': return `全体恢复后 ${sg(c.n)}`;
  }
  return '?';
}

// ---------------- 比赛状态 ----------------
function newRace() {
  return {
    ms: MASCOTS.map((_, i) => ({ lane: i + 1, row: 0, facing: 1, fallen: false, status: 'run', place: null,
      everFell: false, knocked: 0, maxRow: 0, dqReason: null })),
    podium: [null, null, null, null],   // podium[i] = 第 i+1 名的吉祥物
    tiePlace: {},                        // 同时出局时，押注按其中较低的名次结算
    boundary: TRACK.back,
    folds: 0,
    flipped: 0,
    over: false,
    flags: { fallen2: false, atLine2: false, crawlStretch: false, emptyStretch: null, sameSpace: false },
  };
}

const running = S => S.ms.map((x, i) => i).filter(i => S.ms[i].status === 'run');
const stretch = () => TRACK.white[TRACK.white.length - 1];

function finish(S, m, steps) {
  const x = S.ms[m];
  if (!S.podium.some(v => v != null && S.ms[v].status === 'fin')) {
    // 第一名冲线时：冲刺区（最后一条白线到终点）里有没有其他吉祥物
    S.flags.emptyStretch = !running(S).some(i => i !== m && S.ms[i].row >= stretch());
  }
  x.status = 'fin';
  const p = S.podium.indexOf(null);
  S.podium[p] = m; x.place = p + 1;
  steps.push({ m, type: 'finish', place: p + 1 });
}

// 出局：同一瞬间可能多个；放在最低的几个空名次，跑得远的名次更好；押注按其中最低名次结算
function disqualify(S, list, reason, steps) {
  list = list.filter(m => S.ms[m].status === 'run');
  if (!list.length) return;
  list.sort((a, b) => S.ms[b].row - S.ms[a].row || a - b);
  const free = [];
  for (let i = 3; i >= 0 && free.length < list.length; i--) if (S.podium[i] == null) free.push(i);
  free.reverse();                                        // 由好到差
  const worst = free[free.length - 1] + 1;
  list.forEach((m, k) => {
    const x = S.ms[m];
    x.status = 'dq'; x.dqReason = reason;
    S.podium[free[k]] = m; x.place = free[k] + 1;
    if (list.length > 1) S.tiePlace[m] = worst;
  });
  steps.push({ type: 'dq', ms: list.slice(), reason, places: list.map(m => S.ms[m].place) });
}

const occupants = (S, lane, row, except) => running(S).filter(i => i !== except && S.ms[i].lane === lane && S.ms[i].row === row);

// 被撞：站着的倒下，已经倒下的出局（击倒出局）
function knock(S, victims, steps, by) {
  for (const v of victims) {
    const x = S.ms[v];
    if (x.status !== 'run') continue;
    x.knocked++;
    if (x.fallen) disqualify(S, [v], 'ko', steps);
    else { x.fallen = true; x.everFell = true; steps.push({ m: v, type: 'knocked', by }); }
  }
}

function noteCrawl(S, x, from, to) {
  if (x.fallen && (from >= stretch() || to >= stretch())) S.flags.crawlStretch = true;
}

// 单个吉祥物移动 n 格（正数朝面对方向，负数反方向）；倒下时只能爬 1 格
function moveBy(S, m, n, steps) {
  const x = S.ms[m];
  if (x.fallen && n !== 0) n = Math.sign(n);
  const delta = n * x.facing;
  if (!delta) return true;
  const from = x.row, to = from + delta;
  noteCrawl(S, x, from, Math.min(to, TRACK.last));
  if (to > TRACK.last) {
    x.row = TRACK.last + 1;
    steps.push({ m, type: 'move', from, to: TRACK.last + 1, lane: x.lane });
    finish(S, m, steps);
    return false;
  }
  x.row = to; x.maxRow = Math.max(x.maxRow, to);
  steps.push({ m, type: 'move', from, to, lane: x.lane });
  if (to < S.boundary) { disqualify(S, [m], 'back', steps); return false; }
  return true;
}

function starTarget(x) {
  if (x.facing > 0) return TRACK.stars.find(r => r > x.row);
  const back = TRACK.stars.filter(r => r < x.row);
  return back.length ? back[back.length - 1] : null;
}

function recover(x, m, steps) {
  if (x.fallen || x.facing < 0) { x.fallen = false; x.facing = 1; steps.push({ m, type: 'recover' }); }
}

// ---------------- 结算一张牌：返回动画步骤 ----------------
function applyCard(S, c) {
  const steps = [];
  S.flipped++;
  if (c.m != null) {
    const m = c.m, x = S.ms[m];
    if (x.status !== 'run') { steps.push({ m, type: 'none' }); return end(S, steps); }
    const land = () => knock(S, occupants(S, x.lane, x.row, m), steps, m);
    switch (c.kind) {
      case 'num': if (moveBy(S, m, c.n, steps)) land(); break;
      case 'star': {
        if (x.fallen) { if (moveBy(S, m, 1, steps)) land(); break; }
        const t = starTarget(x);
        if (t == null) { steps.push({ m, type: 'none' }); break; }
        if (moveBy(S, m, Math.abs(t - x.row), steps)) land();
        break;
      }
      case 'fall':
        if (x.fallen) disqualify(S, [m], 'ko', steps);
        else { x.fallen = true; x.everFell = true; steps.push({ m, type: 'fall' }); }
        break;
      case 'turn': x.facing *= -1; steps.push({ m, type: 'turn', facing: x.facing }); break;
      case 'start':
      case 'recover': recover(x, m, steps); if (moveBy(S, m, c.n, steps)) land(); break;
      case 'swerve': {
        if (!moveBy(S, m, c.n, steps)) break;
        const lane = x.lane + (c.dir === 'L' ? -1 : 1) * x.facing;
        steps.push({ m, type: 'swerve', from: x.lane, to: lane, row: x.row });
        x.lane = lane;
        if (lane < 1 || lane > LANES) { disqualify(S, [m], 'edge', steps); break; }
        land();
        break;
      }
    }
    return end(S, steps);
  }

  // 全体牌：动画上一个接一个播放，规则上同时生效（不碰撞、不能冲线、同时出局）
  const outs = [];
  for (const m of running(S)) {
    const x = S.ms[m];
    if (c.kind === 'all-recover') recover(x, m, steps);
    let n = x.fallen ? Math.sign(c.n) : c.n;
    let to = x.row + n * x.facing;
    if (to > TRACK.last) to = TRACK.last;
    noteCrawl(S, x, x.row, to);
    if (to !== x.row) steps.push({ m, type: 'move', from: x.row, to, lane: x.lane });
    else steps.push({ m, type: 'none' });
    x.row = to; x.maxRow = Math.max(x.maxRow, to);
    if (to < S.boundary) outs.push(m);
  }
  if (outs.length) disqualify(S, outs, 'back', steps);
  return end(S, steps);
}

function observe(S) {
  const r = running(S).map(i => S.ms[i]);
  if (r.filter(x => x.fallen).length >= 2) S.flags.fallen2 = true;
  if (r.filter(x => x.row === TRACK.last).length >= 2) S.flags.atLine2 = true;
  const cells = new Set();
  for (const x of r) { const k = x.lane + ':' + x.row; if (cells.has(k)) S.flags.sameSpace = true; cells.add(k); }
}

function end(S, steps) {
  observe(S);
  if (S.ms.filter(x => x.status !== 'run').length >= 3 && !S.over) {
    S.over = true;
    for (const m of running(S)) { const p = S.podium.indexOf(null); S.podium[p] = m; S.ms[m].place = p + 1; S.ms[m].status = 'last'; }
    steps.push({ type: 'over' });
  }
  return steps;
}

// 牌堆用完：赛道后端折叠到下一条白线，还没越过的出局
function fold(S) {
  const steps = [];
  S.folds++;
  const line = S.folds <= TRACK.white.length ? TRACK.white[S.folds - 1] : TRACK.last + 1;
  S.boundary = line;
  steps.push({ type: 'fold', line, folds: S.folds });
  const outs = running(S).filter(m => S.ms[m].row < line);
  if (outs.length) disqualify(S, outs, 'fold', steps);
  return end(S, steps);
}

// ---------------- 跑完整一场：返回最终状态和时间线 ----------------
function runRace(deck, rng) {
  const S = newRace();
  const shuffle = a => { a = a.slice(); for (let i = a.length - 1; i > 0; i--) { const j = Math.floor(rng() * (i + 1)); [a[i], a[j]] = [a[j], a[i]]; } return a; };
  const timeline = [];
  let pile = shuffle(deck), i = BURN;
  timeline.push({ type: 'burn', cards: pile.slice(0, BURN).map(c => c.id) });
  let guard = 0;
  while (!S.over && guard++ < 500) {
    if (i >= pile.length) {
      timeline.push({ type: 'reshuffle', steps: fold(S) });
      if (S.over) break;
      pile = shuffle(deck); i = BURN;
      timeline.push({ type: 'burn', cards: pile.slice(0, BURN).map(c => c.id) });
      continue;
    }
    const c = pile[i++];
    timeline.push({ type: 'card', card: c.id, steps: applyCard(S, c) });
  }
  return { S, timeline };
}

// 押注结算用的名次（同时出局按较低名次）
const payPlace = (S, m) => S.tiePlace[m] || S.ms[m].place;

// ---------------- 12 张附加赌注卡（自动判定） ----------------
const SIDE_BETS = [
  ...MASCOTS.map((mm, m) => ({ id: 'bottom' + m, text: `${mm.name}会排在后两名吗？`, test: S => payPlace(S, m) >= 3 })),
  { id: 'fallen2',  text: '会有至少 2 个吉祥物同时处于摔倒状态吗？', test: S => S.flags.fallen2 },
  { id: 'atLine2',  text: '会有至少 2 个吉祥物同时停在终点线前一格吗？', test: S => S.flags.atLine2 },
  { id: 'anyDQ',    text: '会有至少 1 个吉祥物被取消资格吗？', test: S => S.ms.some(x => x.status === 'dq') },
  { id: 'crawl',    text: '会有吉祥物在冲刺区里爬行吗？（爬进、爬出冲刺区也算）', test: S => S.flags.crawlStretch },
  { id: 'empty',    text: '第一名冲线时，冲刺区里会没有其他吉祥物吗？', test: S => S.flags.emptyStretch === true },
  { id: 'oob',      text: '会有吉祥物跑出赛道吗？（从后端、侧边跑出，或被折叠的赛道淘汰）', test: S => S.ms.some(x => ['back', 'edge', 'fold'].includes(x.dqReason)) },
  { id: 'same',     text: '会有 2 个吉祥物同时停在同一格吗？', test: S => S.flags.sameSpace },
  { id: 'ko',       text: '会有吉祥物被击倒出局吗？（已经倒下时又摔倒）', test: S => S.ms.some(x => x.dqReason === 'ko') },
];

module.exports = { MASCOTS, LANES, TRACK, BURN, defaultConfig, buildPool, cardText,
  newRace, applyCard, fold, runRace, payPlace, SIDE_BETS };
