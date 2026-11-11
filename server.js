// 密电对决 —— 4~8 人、两队对抗的解码猜词游戏（零依赖联机服务器）
// 运行：node server.js   （默认端口 3000，可用环境变量 PORT 修改）
'use strict';
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');

const PORT = Number(process.env.PORT) || 3000;
const ROOM_TTL = 6 * 3600 * 1000;
const MAX_PLAYERS = 8;
const MAX_ROUNDS = 8;
const TEAM_MIN = 2, TEAM_MAX = 4;
const TEAMS = ['red', 'blue'];
const TNAME = { red: '红队', blue: '蓝队' };
const other = t => (t === 'red' ? 'blue' : 'red');

const HTML = fs.readFileSync(path.join(__dirname, 'index.html'));
const WORDS = (() => {
  const d = JSON.parse(fs.readFileSync(path.join(__dirname, 'words.json'), 'utf8'));
  return [...new Set(Object.values(d.categories).flat())];
})();

// 24 种密码：1~4 中取 3 个不重复的数字排列
const CODES = [];
for (let a = 1; a <= 4; a++) for (let b = 1; b <= 4; b++) for (let c = 1; c <= 4; c++)
  if (a !== b && b !== c && a !== c) CODES.push([a, b, c]);

const rid = () => crypto.randomBytes(8).toString('hex');
const pick = a => a[crypto.randomInt(a.length)];
const shuffle = a => { for (let i = a.length - 1; i > 0; i--) { const j = crypto.randomInt(i + 1); [a[i], a[j]] = [a[j], a[i]]; } return a; };
const norm = s => String(s || '').normalize('NFKC').toLowerCase().replace(/[\s\p{P}]+/gu, '');
const same = (a, b) => Array.isArray(a) && Array.isArray(b) && a.length === 3 && a.every((x, i) => x === b[i]);
class GameError extends Error {}
const fail = m => { throw new GameError(m); };

const rooms = new Map();
function newCode() { let c; do { c = String(1000 + crypto.randomInt(9000)); } while (rooms.has(c)); return c; }
function cleanName(n) { n = String(n || '').trim().slice(0, 10); return n || '玩家'; }
function newPlayer(name) { return { id: rid(), token: rid(), name: cleanName(name), team: null, ready: false, clients: new Set() }; }

const members = (room, t) => room.players.filter(p => p.team === t);

// ---------------- 对局 ----------------
function newTeamState(words) {
  return {
    words, tokens: { intercept: 0, miss: 0 },
    sheet: [[], [], [], []],          // 1~4 号关键词下历次出现过的提示
    encoder: null, code: null, clues: null, draft: ['', '', ''], deadline: 0,
    answers: { own: [0, 0, 0], intercept: [0, 0, 0], editor: null }, locked: false,
  };
}

function startGame(room) {
  const words = shuffle([...WORDS]).slice(0, 8);
  room.teams = { red: newTeamState(words.slice(0, 4)), blue: newTeamState(words.slice(4, 8)) };
  room.chat = { red: [], blue: [] };
  room.history = [];
  room.round = 0;
  room.result = null;
  sys(room, 'red', '游戏开始！你们的 4 个关键词在左上方，只有本队能看到。');
  sys(room, 'blue', '游戏开始！你们的 4 个关键词在左上方，只有本队能看到。');
  startRound(room);
}

function startRound(room) {
  room.round += 1;
  room.phase = 'clue';
  for (const t of TEAMS) {
    const T = room.teams[t], m = members(room, t);
    T.encoder = m[(room.round - 1) % m.length].id;
    T.code = pick(CODES);
    T.clues = null; T.draft = ['', '', '']; T.deadline = 0;
    T.answers = { own: [0, 0, 0], intercept: [0, 0, 0], editor: null };
    T.locked = false;
  }
  for (const p of room.players) p.ready = false;
  clearTimeout(room.timer);
}

function submitClues(room, t, clues, auto) {
  const T = room.teams[t];
  T.clues = clues;
  T.deadline = 0;
  const o = room.teams[other(t)];
  // 计时：一队先交，另一队开始倒计时
  if (room.settings.timer && !o.clues && !o.deadline) {
    o.deadline = Date.now() + room.settings.seconds * 1000;
    clearTimeout(room.timer);
    room.timer = setTimeout(() => {
      if (room.phase !== 'clue' || o.clues) return;
      const bad = x => o.words.some(w => norm(x).includes(norm(w)));
      submitClues(room, other(t), o.draft.map(x => { x = String(x || '').trim().slice(0, 20); return x && !bad(x) ? x : '（超时）'; }), true);
      broadcast(room);
    }, room.settings.seconds * 1000 + 300);
  }
  if (auto) sys(room, t, '时间到！加密者没写完（或含有关键词）的提示自动记为“（超时）”。');
  if (room.teams.red.clues && room.teams.blue.clues) {
    clearTimeout(room.timer);
    room.phase = 'guess';
    room.roundRec = { round: room.round };
    // 每轮交换先后顺序：单数轮先处理红队密码，双数轮先处理蓝队
    startCode(room, room.round % 2 === 1 ? 'red' : 'blue');
  }
}

// ---------------- 破译 / 拦截：一次只处理一个队的密码 ----------------
// 处理 X 队密码时：X 队（加密者除外）破译，Y 队全员拦截（第 1 轮没有拦截）
function startCode(room, t) {
  room.cur = t;
  clearTimeout(room.timer);
  for (const x of TEAMS) { room.teams[x].locked = false; room.teams[x].deadline = 0; }
  const msg = room.round >= 2 ? `现在处理${TNAME[t]}的密码：${TNAME[t]}破译，${TNAME[other(t)]}拦截。` : `现在处理${TNAME[t]}的密码：${TNAME[t]}破译（第一轮没有拦截）。`;
  for (const x of TEAMS) sys(room, x, msg);
}

// 锁定即最终提交；一方锁定后另一方开始倒计时，时间到自动锁定当前答案
function lockTeam(room, t, by) {
  const T = room.teams[t];
  T.locked = true;
  T.deadline = 0;
  sys(room, t, by ? `${by} 锁定了答案。` : '时间到！已自动锁定当前答案，没选完整的部分算猜错。');
  const X = room.cur, Y = other(X);
  const need = room.round >= 2 ? [X, Y] : [X];
  if (need.every(x => room.teams[x].locked)) { clearTimeout(room.timer); return resolveCode(room); }
  const waiting = need.find(x => !room.teams[x].locked);
  const W = room.teams[waiting];
  if (room.settings.timer && !W.deadline) {
    W.deadline = Date.now() + room.settings.seconds * 1000;
    clearTimeout(room.timer);
    const cur = room.cur, rnd = room.round;
    room.timer = setTimeout(() => {
      if (room.phase !== 'guess' || room.cur !== cur || room.round !== rnd || W.locked) return;
      lockTeam(room, waiting, null);
      broadcast(room);
    }, room.settings.seconds * 1000 + 300);
  }
}

function resolveCode(room) {
  const t = room.cur, T = room.teams[t], O = room.teams[other(t)];
  const ownOk = same(T.answers.own, T.code);
  const icpt = room.round >= 2 ? O.answers.intercept : null;
  const icptOk = room.round >= 2 && same(icpt, T.code);
  if (!ownOk) T.tokens.miss++;
  if (icptOk) O.tokens.intercept++;
  T.code.forEach((d, i) => T.sheet[d - 1].push(T.clues[i]));
  room.roundRec[t] = { encoder: T.encoder, clues: T.clues, code: T.code, own: T.answers.own, ownOk, intercept: icpt, interceptOk: icptOk };
  if (!room.roundRec[other(t)]) return startCode(room, other(t));

  // 两个密码都处理完：本轮揭晓，判定胜负
  room.history.push(room.roundRec);
  room.phase = 'reveal';
  room.cur = null;
  for (const p of room.players) p.ready = false;
  const r = room.teams.red, b = room.teams.blue;
  const redWin = r.tokens.intercept >= 2 || b.tokens.miss >= 2;
  const blueWin = b.tokens.intercept >= 2 || r.tokens.miss >= 2;
  if (redWin !== blueWin) return end(room, redWin ? 'red' : 'blue', 'normal');
  if (redWin || room.round >= MAX_ROUNDS) {
    const sr = r.tokens.intercept - r.tokens.miss, sb = b.tokens.intercept - b.tokens.miss;
    return end(room, sr > sb ? 'red' : sb > sr ? 'blue' : null, redWin ? 'both' : 'rounds');
  }
}

function end(room, winner, how) {
  room.phase = 'end';
  const score = t => room.teams[t].tokens.intercept - room.teams[t].tokens.miss;
  room.result = { winner, how, score: { red: score('red'), blue: score('blue') } };
}

function sys(room, t, text) { pushChat(room, t, { sys: true, text }); }
function pushChat(room, t, msg) {
  room.chat[t].push({ n: ++room.seq, ...msg });
  if (room.chat[t].length > 150) room.chat[t].shift();
}

// ---------------- 状态下发（每人只拿到该看的） ----------------
function stateFor(room, me) {
  const ended = room.phase === 'end';
  const teams = {};
  if (room.teams) for (const t of TEAMS) {
    const T = room.teams[t], mine = me.team === t, enc = me.id === T.encoder;
    teams[t] = {
      tokens: T.tokens, sheet: T.sheet, encoder: T.encoder,
      words: mine || ended ? T.words : null,
      code: (enc && ['clue', 'guess'].includes(room.phase)) || ['reveal', 'end'].includes(room.phase) || (room.phase === 'guess' && room.roundRec[t]) ? T.code : null,
      cluesIn: !!T.clues,
      // 提示按顺序公开：正在处理或已经处理过的密码才显示提示
      clues: ['reveal', 'end'].includes(room.phase) || (room.phase === 'guess' && (room.cur === t || room.roundRec[t])) ? T.clues : null,
      draft: enc && room.phase === 'clue' ? T.draft : null,
      deadline: ['clue', 'guess'].includes(room.phase) ? T.deadline : 0,
      answers: mine ? T.answers : null,
      locked: T.locked,
    };
  }
  return {
    code: room.code, phase: room.phase, host: room.hostId, you: me.id, myTeam: me.team,
    settings: room.settings, round: room.round, maxRounds: MAX_ROUNDS, now: Date.now(),
    cur: room.phase === 'guess' ? room.cur : null,
    roundRec: room.phase === 'guess' ? room.roundRec : null,
    players: room.players.map(p => ({ id: p.id, name: p.name, team: p.team, online: p.clients.size > 0, ready: p.ready })),
    teams: room.teams ? teams : null,
    history: room.history || [],
    chat: me.team && room.chat ? room.chat[me.team] : [],
    result: room.result,
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
function digits(a) {
  if (!Array.isArray(a) || a.length !== 3) fail('答案格式不对');
  return a.map(x => { const n = Number(x); if (![0, 1, 2, 3, 4].includes(n)) fail('只能选 1~4'); return n; });
}
const complete = a => a.every(x => x >= 1) && new Set(a).size === 3;

function act(room, p, a) {
  const inGame = ['clue', 'guess', 'reveal'].includes(room.phase);
  const T = p.team && room.teams ? room.teams[p.team] : null;
  switch (a.type) {
    case 'team': {
      if (room.phase !== 'lobby' && room.phase !== 'end') fail('游戏进行中不能换队');
      const t = TEAMS.includes(a.team) ? a.team : null;
      if (t && t !== p.team && members(room, t).length >= TEAM_MAX) fail(`${TNAME[t]}已经满 ${TEAM_MAX} 人了`);
      p.team = t; return;
    }
    case 'settings':
      if (p.id !== room.hostId) fail('只有房主能修改设置');
      if (inGame) fail('游戏进行中不能修改设置');
      room.settings = { timer: !!a.timer, seconds: [30, 60, 90, 120].includes(Number(a.seconds)) ? Number(a.seconds) : 60 };
      return;
    case 'start': {
      if (p.id !== room.hostId) fail('只有房主能开始游戏');
      if (inGame) fail('游戏已经开始了');
      const nr = members(room, 'red').length, nb = members(room, 'blue').length;
      if (room.players.some(x => !x.team)) fail('还有人没有选队');
      if (nr < TEAM_MIN || nb < TEAM_MIN) fail(`每队至少 ${TEAM_MIN} 人`);
      return startGame(room);
    }
    case 'chat': {
      if (!T || !room.chat) fail('选队并开始游戏后才能使用队内聊天');
      const text = String(a.text || '').trim().slice(0, 200);
      if (!text) return;
      return pushChat(room, p.team, { from: p.id, name: p.name, text });
    }
    case 'draft':
      if (room.phase !== 'clue' || !T || T.encoder !== p.id || T.clues) return;
      if (Array.isArray(a.clues)) T.draft = [0, 1, 2].map(i => String(a.clues[i] || '').slice(0, 20));
      return 'quiet';
    case 'clues': {
      if (room.phase !== 'clue' || !T || T.encoder !== p.id) fail('现在不是你写提示的时候');
      if (T.clues) fail('提示已经提交了');
      const c = [0, 1, 2].map(i => String((a.clues || [])[i] || '').trim().slice(0, 20));
      if (c.some(x => !x)) fail('三条提示都要写');
      for (const x of c) for (const w of T.words)
        if (norm(x).includes(norm(w))) fail(`提示「${x}」包含了关键词「${w}」，换一个吧`);
      return submitClues(room, p.team, c);
    }
    case 'answer': {
      if (room.phase !== 'guess' || !T) fail('现在不是破译阶段');
      if (T.locked) fail('你们已经锁定答案了');
      const decoding = p.team === room.cur;
      const kind = a.kind === 'intercept' ? 'intercept' : 'own';
      if (kind === 'own' && !decoding) fail(`现在处理的是${TNAME[room.cur]}的密码，你们这次负责拦截`);
      if (kind === 'intercept' && decoding) fail('现在轮到你们破译本队密码');
      if (kind === 'own' && T.encoder === p.id) fail('加密者不能参与本队破译');
      if (kind === 'intercept' && room.round < 2) fail('第一轮不能拦截');
      T.answers[kind] = digits(a.digits);
      T.answers.editor = p.id;
      return;
    }
    case 'lock': {
      if (room.phase !== 'guess' || !T) fail('现在不是破译阶段');
      if (T.locked) return;
      if (p.team === room.cur) {
        if (T.encoder === p.id) fail('请让本队破译者来锁定答案');
        if (!complete(T.answers.own)) fail('先把三位数选完整（三个数字不能重复）');
      } else {
        if (room.round < 2) fail('第一轮不能拦截');
        if (!complete(T.answers.intercept)) fail('先把拦截的三位数选完整（三个数字不能重复）');
      }
      return lockTeam(room, p.team, p.name);
    }
    case 'unlock':
      fail('锁定后不能取消');
    case 'next': {
      if (room.phase !== 'reveal') return;
      p.ready = true;
      const online = room.players.filter(x => x.clients.size > 0);
      if (online.every(x => x.ready)) startRound(room);
      return;
    }
    case 'lobby':
      if (p.id !== room.hostId) fail('只有房主能操作');
      clearTimeout(room.timer);
      room.phase = 'lobby'; room.teams = null; room.chat = null; room.history = []; room.round = 0; room.result = null;
      room.players.forEach(x => { x.ready = false; });
      return;
    case 'leave':
      if (inGame) fail('游戏进行中不能离开，可以请房主结束本局');
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
      const room = { code: newCode(), hostId: p.id, players: [p], phase: 'lobby', settings: { timer: false, seconds: 60 },
        teams: null, chat: null, history: [], round: 0, result: null, cur: null, roundRec: null, seq: 0, timer: null, touched: Date.now() };
      rooms.set(room.code, room);
      return json(res, 200, { code: room.code, id: p.id, token: p.token });
    }
    if (url.pathname === '/api/join') {
      const room = rooms.get(String(b.code || '').trim());
      if (!room) return json(res, 404, { error: '房间不存在或已过期' });
      const back = room.players.find(x => x.id === b.id && x.token === b.token);
      if (back) return json(res, 200, { code: room.code, id: back.id, token: back.token });
      // 用原来的名字找回座位（浏览器丢失了登录信息时），优先匹配掉线的人
      const nm = cleanName(b.name);
      const inGame = ['clue', 'guess', 'reveal'].includes(room.phase);
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
      if (r !== 'quiet' && r !== 'gone') broadcast(a.room);
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

if (require.main === module) server.listen(PORT, () => console.log(`密电对决已启动： http://localhost:${PORT}`));
module.exports = { server, rooms };
