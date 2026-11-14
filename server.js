// 吉祥物大狂奔 —— 2~8 人联机服务器（零依赖）
// 运行：node server.js   （默认端口 3000，可用环境变量 PORT 修改）
'use strict';
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const E = require('./engine');

const PORT = Number(process.env.PORT) || 3000;
const ROOM_TTL = 6 * 3600 * 1000;
const MIN_PLAYERS = 2, MAX_PLAYERS = 8, RACES = 3, START_MONEY = 10;
const HTML = fs.readFileSync(path.join(__dirname, 'index.html'));

// 动画节奏（毫秒）：翻牌 1.5 秒，每个吉祥物的动作 1 秒
const SPEED = Number(process.env.HS_SPEED) || 1;   // 仅测试用：加快动画
const T_FLIP = 1500 / SPEED, T_BEAT = 1000 / SPEED, T_BURN = 1500 / SPEED, T_FOLD = 2500 / SPEED, T_END = 2000 / SPEED;
const T_AUTO = 20000 / SPEED;      // 轮到的人 20 秒没翻牌，程序自动替他翻

// 赔率：吉祥物票 [第1名, 第2名, 第3名]；附加赌注票 [猜对, 猜错]；第 1 张最先被拿，赔率最高
const PAY = {
  m: [
    { safe: [6, 4, 2], risky: [11, 1, 0] },
    { safe: [5, 3, 2], risky: [9, 1, 0] },
    { safe: [4, 3, 1], risky: [7, 1, 0] },
  ],
  s: [
    { safe: [4, 0], risky: [5, -3] },
    { safe: [3, 0], risky: [4, -3] },
    { safe: [2, 0], risky: [3, -3] },
  ],
};

const rid = () => crypto.randomBytes(8).toString('hex');
const rng = () => crypto.randomInt(4294967296) / 4294967296;
const shuffle = a => { a = a.slice(); for (let i = a.length - 1; i > 0; i--) { const j = crypto.randomInt(i + 1); [a[i], a[j]] = [a[j], a[i]]; } return a; };
class GameError extends Error {}
const fail = m => { throw new GameError(m); };

const rooms = new Map();
function newCode() { let c; do { c = String(1000 + crypto.randomInt(9000)); } while (rooms.has(c)); return c; }
function cleanName(n) { n = String(n || '').trim().slice(0, 10); return n || '玩家'; }
function newPlayer(name) { return { id: rid(), token: rid(), name: cleanName(name), clients: new Set(), money: START_MONEY, hand: [], ready: false }; }

const POOL = E.buildPool();
const CARD = Object.fromEntries(POOL.map(c => [c.id, c]));
const cardOut = id => { const c = CARD[id]; return { id, kind: c.kind, m: c.m, n: c.n, dir: c.dir, text: E.cardText(c) }; };
const sub = room => (room.players.length === 2 ? 2 : 1);           // 每人每场加入牌堆的张数
const perTickets = room => (room.players.length === 2 ? 3 : 2);    // 每人每场拿几张票

// ---------------- 对局流程 ----------------
function startGame(room) {
  const n = room.players.length;
  room.players.forEach(p => { p.money = START_MONEY; p.hand = []; p.ready = false; });
  const starts = POOL.filter(c => c.kind === 'start').map(c => c.id);
  const rest = shuffle(POOL.filter(c => c.kind !== 'start').map(c => c.id));
  const randomN = 18 - 4 - n * sub(room);
  room.pub = starts.concat(rest.splice(0, randomN));
  const hs = n === 2 ? 4 : 3;
  room.players.forEach(p => { p.hand = rest.splice(0, hs); });
  room.sideOrder = shuffle(E.SIDE_BETS.map(b => b.id));
  room.first = crypto.randomInt(n);
  room.race = 0;
  room.history = [];
  startRace(room);
}

function startRace(room) {
  room.race += 1;
  room.phase = 'bet';
  room.sideId = room.sideOrder[room.race - 1];
  room.stacks = { m: [0, 1, 2, 3].map(() => [0, 1, 2]), yes: [0, 1, 2], no: [0, 1, 2] };
  room.tickets = Object.fromEntries(room.players.map(p => [p.id, []]));
  room.submitted = {};
  room.raceData = null; room.result = null;
  const n = room.players.length, first = (room.first + room.race - 1) % n;
  room.order = [];
  for (let r = 0; r < perTickets(room); r++)
    for (let i = 0; i < n; i++) room.order.push(room.players[(first + (r % 2 ? n - 1 - i : i)) % n].id);
  room.pos = 0;
  room.players.forEach(p => { p.ready = false; });
}

function pickTicket(room, p, a) {
  if (room.phase !== 'bet') fail('现在不是选票阶段');
  if (room.order[room.pos] !== p.id) fail('还没轮到你选票');
  const side = a.side === 'risky' ? 'risky' : 'safe';
  let t;
  if (/^m[0-3]$/.test(a.stack)) {
    const m = Number(a.stack[1]), st = room.stacks.m[m];
    if (!st.length) fail('这叠票已经被拿完了');
    t = { type: 'm', m, k: st.shift(), side };
  } else if (a.stack === 'yes' || a.stack === 'no') {
    const st = room.stacks[a.stack];
    if (!st.length) fail('这叠票已经被拿完了');
    t = { type: 's', yes: a.stack === 'yes', k: st.shift(), side };
  } else fail('请选择一叠票');
  t.pay = (t.type === 'm' ? PAY.m : PAY.s)[t.k][side];
  t.dbl = false;
  room.tickets[p.id].push(t);
  room.pos++;
  if (room.pos >= room.order.length) {
    room.phase = room.race === RACES ? 'double' : 'submit';
    room.doubled = {};
  }
}

// ---------------- 比赛：玩家轮流翻牌，自己挑第几张 ----------------
// 牌堆洗好后背面朝上排成一排，轮到的人挑一张翻开，引擎当场结算这张牌。
// 开场弃 3 张、牌堆用完时的洗牌折叠由程序自动进行。还没翻开的牌不会发给任何浏览器。
function startRaceRun(room) {
  room.deck = room.pub.concat(...room.players.map(p => room.submitted[p.id]));
  room.phase = 'race';
  room.raceResult = E.newRace();
  room.lastEnd = Date.now() + 800 / SPEED;
  room.flipIdx = (room.first + room.race - 1) % room.players.length;   // 本场选票先手的人先翻
  room.raceData = { id: rid(), items: [], turn: null, readyAt: 0, autoAt: 0, over: false, flips: 0, left: 0, pass: 0 };
  startPass(room);
  nextTurn(room, false);
}

// 洗牌 → 弃掉 3 张 → 剩下的背面朝上等着翻
function startPass(room) {
  const pile = shuffle(room.deck);
  const burned = pile.splice(0, E.BURN);
  room.pile = pile;
  room.raceData.pass++;
  queue(room, [{ type: 'burn', cards: burned }], null);
}

// 把一段引擎结果变成动画，接在上一段动画后面公开
function queue(room, timeline, by) {
  const items = buildSchedule(timeline);
  if (!items.length) return;
  const start = Math.max(Date.now(), room.lastEnd), t0 = items[0].at;
  for (const it of items) room.raceData.items.push({ ...it, at: start + it.at - t0, ...(it.kind === 'flip' ? { by } : {}) });
  const last = items[items.length - 1];
  room.lastEnd = start + last.at + last.dur - t0;
}

function nextTurn(room, advance) {
  clearTimeout(room.timer);
  const RD = room.raceData, S = room.raceResult;
  RD.left = room.pile.length;
  if (S.over) {
    // 比赛结束：动画播完后结算
    RD.over = true; RD.turn = null;
    room.timer = setTimeout(() => { settle(room); broadcast(room); }, room.lastEnd - Date.now() + T_END);
    return;
  }
  if (advance) room.flipIdx = (room.flipIdx + 1) % room.players.length;
  RD.turn = room.players[room.flipIdx].id;
  RD.readyAt = room.lastEnd;                 // 上一张的动画播完后才能翻
  RD.autoAt = room.lastEnd + T_AUTO;
  const race = room.race;
  room.timer = setTimeout(() => {
    if (room.phase !== 'race' || room.race !== race || RD.turn == null) return;
    flip(room, null, null);
    broadcast(room);
  }, RD.autoAt - Date.now());
}

// 翻开第 pos 张（从 0 数起）；没指定就随机挑一张
function flip(room, p, pos) {
  const RD = room.raceData, S = room.raceResult;
  if (!(Number.isInteger(pos) && pos >= 0 && pos < room.pile.length)) pos = crypto.randomInt(room.pile.length);
  const id = room.pile.splice(pos, 1)[0];
  const who = p ? p.name : `自动（替${room.players[room.flipIdx].name}）`;
  queue(room, [{ type: 'card', card: id, steps: E.applyCard(S, CARD[id]), pos: pos + 1 }], who);
  RD.flips++;
  // 牌堆翻完还没结束：洗牌、折叠赛道、再弃 3 张
  if (!S.over && !room.pile.length) {
    queue(room, [{ type: 'reshuffle', steps: E.fold(S) }], null);
    if (!S.over) startPass(room);
  }
  nextTurn(room, true);
}

// 把引擎的时间线拆成“节拍”：翻牌 1.5 秒，然后每个吉祥物的动作各 1 秒
function buildSchedule(timeline) {
  const out = [];
  let t = 0;
  for (const e of timeline) {
    if (e.type === 'burn') { out.push({ at: t, dur: T_BURN, kind: 'burn', n: e.cards.length }); t += T_BURN; continue; }
    if (e.type === 'reshuffle') {
      out.push({ at: t, dur: T_FOLD, kind: 'fold', steps: e.steps, text: foldText(e.steps) }); t += T_FOLD; continue;
    }
    const card = cardOut(e.card);
    out.push({ at: t, dur: T_FLIP, kind: 'flip', card, pos: e.pos }); t += T_FLIP;
    // 按动作者分组成节拍：被撞倒、出局、比赛结束都归到当前动作者的那一拍
    const beats = [];
    for (const st of e.steps) {
      const actor = ['knocked', 'dq', 'over'].includes(st.type) ? null : st.m;
      let cur = beats[beats.length - 1];
      if (!cur || (actor != null && cur.actor !== actor && cur.actor != null)) { cur = { kind: 'beat', actor, steps: [] }; beats.push(cur); }
      if (cur.actor == null && actor != null) cur.actor = actor;
      cur.steps.push(st);
    }
    for (const b of beats) {
      if (b.steps.every(x => x.type === 'none')) continue;
      b.steps = b.steps.filter(x => x.type !== 'none');
      b.at = t; b.dur = T_BEAT; b.text = beatText(b.steps);
      out.push(b); t += T_BEAT;
    }
  }
  return out;
}

const NAME = m => E.MASCOTS[m].name;
const REASON = { edge: '冲出了赛道边缘', back: '从后端跑出了赛道', ko: '被击倒出局', fold: '被折叠的赛道淘汰' };
function beatText(steps) {
  const parts = [];
  for (const s of steps) {
    if (s.type === 'move') parts.push(s.to > E.TRACK.last ? `${NAME(s.m)}冲过终点线` : `${NAME(s.m)}${s.to > s.from ? '前进' : '后退'}到第 ${s.to} 格`);
    else if (s.type === 'swerve') parts.push(`${NAME(s.m)}转弯到赛道 ${s.to}`);
    else if (s.type === 'fall') parts.push(`${NAME(s.m)}摔倒了`);
    else if (s.type === 'knocked') parts.push(`撞倒了${NAME(s.m)}！`);
    else if (s.type === 'turn') parts.push(`${NAME(s.m)}${s.facing > 0 ? '转回面向终点' : '掉头了'}`);
    else if (s.type === 'recover') parts.push(`${NAME(s.m)}站了起来`);
    else if (s.type === 'finish') parts.push(`🏁 ${NAME(s.m)}获得第 ${s.place} 名！`);
    else if (s.type === 'dq') parts.push(`❌ ${s.ms.map(NAME).join('、')}${REASON[s.reason]}`);
    else if (s.type === 'over') parts.push('比赛结束！');
  }
  return parts.join('，');
}
function foldText(steps) {
  const f = steps.find(s => s.type === 'fold');
  const dq = steps.find(s => s.type === 'dq');
  return `牌堆用完！重新洗牌，赛道折叠到白线${'①②③'[f.folds - 1] || ''}` + (dq ? `，${dq.ms.map(NAME).join('、')}被淘汰` : '') + (steps.some(s => s.type === 'over') ? '。比赛结束！' : '');
}

// 比赛动画结束：结算
function settle(room) {
  if (room.phase !== 'race') return;
  const S = room.raceResult;
  const side = E.SIDE_BETS.find(b => b.id === room.sideId);
  const happened = side.test(S);
  const rows = room.players.map(p => {
    const ts = room.tickets[p.id].map(t => {
      let v;
      if (t.type === 'm') { const pl = E.payPlace(S, t.m); v = pl <= 3 ? t.pay[pl - 1] : 0; t.place = pl; }
      else { t.right = happened === t.yes; v = t.right ? t.pay[0] : t.pay[1]; }
      t.value = v * (t.dbl ? 2 : 1);
      return t;
    });
    const delta = ts.reduce((s, t) => s + t.value, 0);
    const before = p.money;
    p.money = Math.max(0, p.money + delta);
    return { id: p.id, tickets: ts, delta, before, after: p.money };
  });
  const podium = S.podium.map(m => ({ m, status: S.ms[m].status, reason: S.ms[m].dqReason, payPlace: E.payPlace(S, m) }));
  room.result = { podium, side: { id: side.id, text: side.text, happened }, rows };
  room.history.push({ race: room.race, podium, side: room.result.side });
  room.phase = room.race === RACES ? 'end' : 'payout';
  room.players.forEach(p => { p.ready = false; });
}

function nextRace(room) {
  // 牌堆洗匀，每人补牌，剩下的作为下一场公开的牌
  const deck = shuffle(room.deck);
  room.players.forEach(p => { p.hand.push(...deck.splice(0, sub(room))); });
  room.pub = deck;
  startRace(room);
}

// ---------------- 状态下发 ----------------
function stateFor(room, me) {
  const inGame = room.phase !== 'lobby';
  const show = ['race', 'payout', 'end'].includes(room.phase);
  return {
    code: room.code, phase: room.phase, host: room.hostId, you: me.id, now: Date.now(),
    mascots: E.MASCOTS, track: E.TRACK, pay: PAY, races: RACES,
    players: room.players.map(p => ({ id: p.id, name: p.name, online: p.clients.size > 0, money: p.money, ready: p.ready,
      submitted: !!(room.submitted && room.submitted[p.id]), doubled: !!(room.doubled && room.doubled[p.id] != null),
      handCount: p.hand.length })),
    race: inGame ? room.race : 0,
    side: inGame ? { id: room.sideId, text: E.SIDE_BETS.find(b => b.id === room.sideId).text } : null,
    stacks: inGame ? room.stacks : null,
    order: inGame ? room.order : [], pos: inGame ? room.pos : 0,
    // 拿到的票是公开的；双倍选择在比赛开始后公开
    tickets: inGame ? Object.fromEntries(Object.entries(room.tickets).map(([id, ts]) =>
      [id, ts.map(t => ({ ...t, dbl: id === me.id || show ? t.dbl : false }))])) : {},
    hand: me.hand.map(cardOut),
    mySubmitted: room.submitted && room.submitted[me.id] ? room.submitted[me.id].map(cardOut) : null,
    pub: inGame ? room.pub.map(cardOut) : [],
    perTickets: perTickets(room), sub: sub(room),
    raceData: show ? room.raceData : null,
    result: ['payout', 'end'].includes(room.phase) ? room.result : null,
    history: room.history || [],
  };
}
function broadcast(room) {
  room.touched = Date.now();
  for (const p of room.players) {
    const data = 'data: ' + JSON.stringify(stateFor(room, p)) + '\n\n';
    for (const res of p.clients) res.write(data);
  }
}

// ---------------- 操作 ----------------
function act(room, p, a) {
  const inGame = room.phase !== 'lobby';
  switch (a.type) {
    case 'start':
      if (p.id !== room.hostId) fail('只有房主能开始游戏');
      if (inGame) fail('游戏已经开始了');
      if (room.players.length < MIN_PLAYERS) fail(`至少需要 ${MIN_PLAYERS} 人`);
      return startGame(room);
    case 'pick': return pickTicket(room, p, a);
    case 'double': {
      if (room.phase !== 'double') fail('现在不是选双倍的时候');
      const i = Number(a.index), ts = room.tickets[p.id];
      if (!(i >= 0 && i < ts.length)) fail('请选择一张票');
      ts.forEach((t, k) => { t.dbl = k === i; });
      room.doubled[p.id] = i;
      if (room.players.every(x => room.doubled[x.id] != null)) room.phase = 'submit';
      return;
    }
    case 'submit': {
      if (room.phase !== 'submit') fail('现在不是出牌阶段');
      if (room.submitted[p.id]) fail('你已经出过牌了');
      const ids = Array.isArray(a.cards) ? [...new Set(a.cards)] : [];
      if (ids.length !== sub(room)) fail(`请选择 ${sub(room)} 张牌`);
      if (ids.some(id => !p.hand.includes(id))) fail('你没有这张牌');
      p.hand = p.hand.filter(id => !ids.includes(id));
      room.submitted[p.id] = ids;
      if (room.players.every(x => room.submitted[x.id])) startRaceRun(room);
      return;
    }
    case 'flip': {
      if (room.phase !== 'race') fail('现在不是比赛阶段');
      const RD = room.raceData;
      if (RD.over || RD.turn == null) fail('比赛已经结束了');
      if (RD.turn !== p.id) fail('还没轮到你翻牌');
      if (Date.now() < RD.readyAt - 250 / SPEED) fail('等上一张牌的动画播完再翻');
      const pos = a.pos == null ? null : Number(a.pos) - 1;      // 网页上从 1 数起
      if (pos != null && !(Number.isInteger(pos) && pos >= 0 && pos < room.pile.length)) fail(`请选第 1 到第 ${room.pile.length} 张`);
      return flip(room, p, pos);
    }
    case 'next': {
      if (room.phase !== 'payout') return;
      p.ready = true;
      const online = room.players.filter(x => x.clients.size > 0);
      if (online.every(x => x.ready)) nextRace(room);
      return;
    }
    case 'lobby':
      if (p.id !== room.hostId) fail('只有房主能操作');
      clearTimeout(room.timer);
      room.phase = 'lobby';
      room.players.forEach(x => { x.hand = []; x.ready = false; x.money = START_MONEY; });
      return;
    case 'leave':
      if (inGame && room.phase !== 'end') fail('游戏进行中不能离开，可以请房主结束本局');
      for (const res of p.clients) res.end();
      room.players = room.players.filter(x => x !== p);
      if (!room.players.length) { rooms.delete(room.code); return 'gone'; }
      if (room.hostId === p.id) room.hostId = room.players[0].id;
      return;
  }
  fail('未知操作');
}

// ---------------- HTTP ----------------
function readBody(req) {
  return new Promise((resolve, reject) => {
    let d = '';
    req.on('data', c => { d += c; if (d.length > 10000) { req.destroy(); reject(); } });
    req.on('end', () => { try { resolve(JSON.parse(d || '{}')); } catch { resolve({}); } });
    req.on('error', reject);
  });
}
function json(res, code, obj) {
  res.writeHead(code, { 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store' });
  res.end(JSON.stringify(obj));
}
function auth(b) {
  const room = rooms.get(String(b.code || ''));
  if (!room) return { err: [404, '房间不存在或已过期'] };
  const p = room.players.find(x => x.id === b.id && x.token === b.token);
  if (!p) return { err: [403, '你不在这个房间里'] };
  return { room, p };
}

const server = http.createServer(async (req, res) => {
  const url = new URL(req.url, 'http://x');
  try {
    if (req.method === 'GET' && (url.pathname === '/' || url.pathname === '/index.html')) {
      res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-cache' });
      return res.end(HTML);
    }
    if (req.method === 'GET' && url.pathname === '/api/events') {
      const a = auth(Object.fromEntries(url.searchParams));
      if (a.err) { res.writeHead(a.err[0]); return res.end(); }
      res.writeHead(200, { 'Content-Type': 'text/event-stream; charset=utf-8', 'Cache-Control': 'no-cache, no-transform',
        'Connection': 'keep-alive', 'X-Accel-Buffering': 'no' });
      res.write('retry: 2000\n\n');
      a.p.clients.add(res);
      broadcast(a.room);
      const ping = setInterval(() => res.write(': ping\n\n'), 15000);
      req.on('close', () => { clearInterval(ping); a.p.clients.delete(res); if (rooms.has(a.room.code)) broadcast(a.room); });
      return;
    }
    if (req.method !== 'POST') { res.writeHead(404); return res.end(); }
    const b = await readBody(req);

    if (url.pathname === '/api/create') {
      const p = newPlayer(b.name);
      const room = { code: newCode(), hostId: p.id, players: [p], phase: 'lobby', touched: Date.now(), history: [] };
      rooms.set(room.code, room);
      return json(res, 200, { code: room.code, id: p.id, token: p.token });
    }
    if (url.pathname === '/api/join') {
      const room = rooms.get(String(b.code || '').trim());
      if (!room) return json(res, 404, { error: '房间不存在或已过期' });
      const back = room.players.find(x => x.id === b.id && x.token === b.token);
      if (back) return json(res, 200, { code: room.code, id: back.id, token: back.token });
      const nm = cleanName(b.name), inGame = room.phase !== 'lobby';
      const seat = room.players.find(x => x.name === nm && !x.clients.size) || (inGame && room.players.find(x => x.name === nm));
      if (seat) return json(res, 200, { code: room.code, id: seat.id, token: seat.token });
      if (inGame) {
        const off = room.players.filter(x => !x.clients.size).map(x => `「${x.name}」`);
        return json(res, 409, { error: off.length ? `游戏已经开始了。如果你是掉线的玩家，请填写原来的名字再点加入：${off.join('、')}` : '这个房间的游戏已经开始了' });
      }
      if (room.players.length >= MAX_PLAYERS) return json(res, 409, { error: `房间已满（最多 ${MAX_PLAYERS} 人）` });
      const p = newPlayer(b.name);
      room.players.push(p);
      broadcast(room);
      return json(res, 200, { code: room.code, id: p.id, token: p.token });
    }
    if (url.pathname === '/api/action') {
      const a = auth(b);
      if (a.err) return json(res, a.err[0], { error: a.err[1] });
      let r;
      try { r = act(a.room, a.p, b); }
      catch (e) { if (e instanceof GameError) return json(res, 400, { error: e.message }); throw e; }
      if (r !== 'gone') broadcast(a.room);
      return json(res, 200, { ok: true });
    }
    res.writeHead(404); res.end();
  } catch (e) {
    console.error(e);
    if (!res.headersSent) json(res, 500, { error: '服务器出错了' });
  }
});

setInterval(() => {
  const now = Date.now();
  for (const [code, room] of rooms)
    if (!room.players.some(p => p.clients.size) && now - room.touched > ROOM_TTL) { clearTimeout(room.timer); rooms.delete(code); }
}, 10 * 60 * 1000);

if (require.main === module) server.listen(PORT, () => console.log(`吉祥物大狂奔已启动： http://localhost:${PORT}`));
module.exports = { server, rooms, PAY, buildSchedule };
