'use strict';

const express         = require('express');
const { createServer }= require('http');
const { Server }      = require('socket.io');
const path            = require('path');
const { spawn }       = require('child_process');

const PORT = process.env.PORT || 3000;
const app        = express();
const httpServer = createServer(app);
const io         = new Server(httpServer);

app.use(express.static(path.join(__dirname, 'public')));

// ─── Constants ───────────────────────────────────────────────────────────────
const T = 36;
const EMPTY = 0, WALL = 1, BLOCK = 2;
const TICK_RATE = 25; // ticks/second
const DISCONNECT_TIMEOUT_LOBBY = 10_000;  // 10 s Karenzzeit in der Lobby
const DISCONNECT_TIMEOUT_GAME  = 30_000;  // 30 s Karenzzeit im Spiel
const HB = T * 0.38;
const MAX_PLAYERS = 16;

const COLORS = [
  { body: '#2277ee', head: '#ffddb0' }, // blau
  { body: '#dd2222', head: '#ffaaaa' }, // rot
  { body: '#22aa44', head: '#aaffaa' }, // grün
  { body: '#ddaa22', head: '#ffeebb' }, // gelb
  { body: '#aa22dd', head: '#ddaaff' }, // lila
  { body: '#22dddd', head: '#aaffff' }, // cyan
  { body: '#dd6622', head: '#ffcc99' }, // orange
  { body: '#dd2299', head: '#ffaadd' }, // pink
  { body: '#6699ff', head: '#ccddff' }, // hellblau
  { body: '#99dd22', head: '#ddff99' }, // limette
  { body: '#ff6688', head: '#ffccdd' }, // lachs
  { body: '#22ddaa', head: '#aaffee' }, // türkis
  { body: '#885511', head: '#ddbb88' }, // braun
  { body: '#888822', head: '#ffffaa' }, // olive
  { body: '#8822aa', head: '#cc88ff' }, // dunkelviolett
  { body: '#228888', head: '#88eeff' }, // petrol
];

// Spielfeldgröße abhängig von Spieleranzahl (immer ungerade für Wandraster)
function getGridSize(n) {
  if (n <= 4) return { cols: 15, rows: 15 };
  if (n <= 8) return { cols: 19, rows: 19 };
  return { cols: 25, rows: 25 };
}

// Startpositionen gleichmäßig verteilt; Ecken zuerst, dann Kanten, dann Innen
function getSpawns(cols, rows) {
  if (cols === 15) return [
    { tx: 1,  ty: 1  }, { tx: 13, ty: 1  },
    { tx: 1,  ty: 13 }, { tx: 13, ty: 13 },
  ];
  if (cols === 19) return [
    { tx: 1,  ty: 1  }, { tx: 17, ty: 1  }, { tx: 1,  ty: 17 }, { tx: 17, ty: 17 },
    { tx: 9,  ty: 1  }, { tx: 1,  ty: 9  }, { tx: 17, ty: 9  }, { tx: 9,  ty: 17 },
  ];
  // 25x25: 4×4-Raster, Ecken → Außenkanten → Innenpunkte
  return [
    { tx: 1,  ty: 1  }, { tx: 23, ty: 1  }, { tx: 1,  ty: 23 }, { tx: 23, ty: 23 },
    { tx: 7,  ty: 1  }, { tx: 17, ty: 1  }, { tx: 1,  ty: 7  }, { tx: 1,  ty: 17 },
    { tx: 23, ty: 7  }, { tx: 23, ty: 17 }, { tx: 7,  ty: 23 }, { tx: 17, ty: 23 },
    { tx: 7,  ty: 7  }, { tx: 17, ty: 7  }, { tx: 7,  ty: 17 }, { tx: 17, ty: 17 },
  ];
}

// ─── Global state ────────────────────────────────────────────────────────────
let session   = null;
let tunnelUrl = null;

// ─── Grid ────────────────────────────────────────────────────────────────────
function buildGrid(numPlayers, cols, rows, spawns) {
  const g = Array.from({ length: rows }, () => new Array(cols).fill(EMPTY));

  for (let y = 0; y < rows; y++)
    for (let x = 0; x < cols; x++)
      if (x === 0 || y === 0 || x === cols - 1 || y === rows - 1 || (x % 2 === 0 && y % 2 === 0))
        g[y][x] = WALL;

  // Clear L-shaped safe zone around each active spawn
  const safe = new Set();
  for (let i = 0; i < numPlayers; i++) {
    const { tx, ty } = spawns[i];
    const dx = tx < cols / 2 ? 1 : -1;
    const dy = ty < rows / 2 ? 1 : -1;
    safe.add(`${tx},${ty}`);
    for (let d = 1; d <= 2; d++) {
      safe.add(`${tx + dx * d},${ty}`);
      safe.add(`${tx},${ty + dy * d}`);
    }
  }

  for (let y = 1; y < rows - 1; y++)
    for (let x = 1; x < cols - 1; x++)
      if (g[y][x] === EMPTY && !safe.has(`${x},${y}`) && Math.random() < 0.45)
        g[y][x] = BLOCK;

  return g;
}

// ─── Field shrink ────────────────────────────────────────────────────────────
function findFreeSpot(minX, minY, maxX, maxY) {
  const occupied = new Set(
    [...session.players.values()]
      .filter(p => p.alive)
      .map(p => `${Math.floor(p.x/T)},${Math.floor(p.y/T)}`)
  );
  const free = [];
  for (let y = minY; y <= maxY; y++)
    for (let x = minX; x <= maxX; x++)
      if (session.grid[y][x] === EMPTY && !hasBomb(x, y) && !occupied.has(`${x},${y}`))
        free.push({ x, y });
  if (!free.length) return null;
  return free[Math.floor(Math.random() * free.length)];
}

function doShrink() {
  const border = session.shrinkBorder;
  const cols = session.cols, rows = session.rows;

  for (let x = border; x < cols - border; x++) {
    session.grid[border][x] = WALL;
    session.grid[rows - 1 - border][x] = WALL;
  }
  for (let y = border + 1; y < rows - border - 1; y++) {
    session.grid[y][border] = WALL;
    session.grid[y][cols - 1 - border] = WALL;
  }

  session.shrinkBorder++;
  const nb = session.shrinkBorder;

  session.bombs      = session.bombs.filter(b  => b.tx >= nb && b.tx < cols-nb && b.ty >= nb && b.ty < rows-nb);
  session.powerups   = session.powerups.filter(pu => pu.x >= nb && pu.x < cols-nb && pu.y >= nb && pu.y < rows-nb);
  session.explosions = session.explosions.filter(e  => e.x  >= nb && e.x  < cols-nb && e.y  >= nb && e.y  < rows-nb);
  for (const [key, entry] of session.burning)
    if (entry.x < nb || entry.x >= cols-nb || entry.y < nb || entry.y >= rows-nb)
      session.burning.delete(key);

  for (const [, player] of session.players) {
    if (!player.alive) continue;
    const ptx = Math.floor(player.x / T), pty = Math.floor(player.y / T);
    if (isSolid(ptx, pty)) {
      const spot = findFreeSpot(nb, nb, cols - 1 - nb, rows - 1 - nb);
      if (spot) { player.x = (spot.x + 0.5) * T; player.y = (spot.y + 0.5) * T; }
    }
  }

  emitSound('shrink');
}

// ─── Game helpers ────────────────────────────────────────────────────────────
function tileAt(x, y) {
  if (x < 0 || y < 0 || x >= session.cols || y >= session.rows) return WALL;
  return session.grid[y][x];
}
function isSolid(x, y)     { const t = tileAt(x, y); return t === WALL || t === BLOCK; }
function hasBomb(x, y)     { return session.bombs.some(b => b.tx === x && b.ty === y); }
function hasExplosion(x, y){ return session.explosions.some(e => e.x === x && e.y === y); }

function collidesAt(ent, px, py) {
  for (const cx of [px - HB, px + HB]) {
    for (const cy of [py - HB, py + HB]) {
      const tx = Math.floor(cx / T), ty = Math.floor(cy / T);
      if (isSolid(tx, ty)) return true;
      if (hasBomb(tx, ty)) {
        const overlaps = ent.x + HB > tx * T && ent.x - HB < (tx + 1) * T &&
                         ent.y + HB > ty * T && ent.y - HB < (ty + 1) * T;
        if (!overlaps) return true;
      }
    }
  }
  return false;
}

function tryMove(ent, dx, dy, dt) {
  const spd = ent.speed * dt;
  if (!collidesAt(ent, ent.x + dx * spd, ent.y)) ent.x += dx * spd;
  if (!collidesAt(ent, ent.x, ent.y + dy * spd)) ent.y += dy * spd;

  const SNAP = T * 0.45;
  if (dx !== 0) {
    const cy = Math.round((ent.y - T / 2) / T) * T + T / 2;
    const d  = cy - ent.y;
    if (Math.abs(d) > 0.5 && Math.abs(d) < SNAP) {
      const step = Math.sign(d) * Math.min(Math.abs(d), spd);
      if (!collidesAt(ent, ent.x, ent.y + step)) ent.y += step;
    }
  }
  if (dy !== 0) {
    const cx = Math.round((ent.x - T / 2) / T) * T + T / 2;
    const d  = cx - ent.x;
    if (Math.abs(d) > 0.5 && Math.abs(d) < SNAP) {
      const step = Math.sign(d) * Math.min(Math.abs(d), spd);
      if (!collidesAt(ent, ent.x + step, ent.y)) ent.x += step;
    }
  }
}

function addExp(x, y) {
  const e = session.explosions.find(e => e.x === x && e.y === y);
  if (e) { e.timer = 0.8; return; }
  session.explosions.push({ x, y, timer: 0.8 });
}

function emitSound(type) {
  if (session) io.to(`session:${session.id}`).emit('sound', { type });
}

function explodeBomb(bomb) {
  const idx = session.bombs.indexOf(bomb);
  if (idx < 0) return;

  const owner = bomb.ownerId ? session.players.get(bomb.ownerId) : null;
  if (owner) owner.activeBombs = Math.max(0, owner.activeBombs - 1);
  session.bombs.splice(idx, 1);
  emitSound('boom');
  addExp(bomb.tx, bomb.ty);

  for (const [ddx, ddy] of [[1,0],[-1,0],[0,1],[0,-1]]) {
    for (let i = 1; i <= bomb.range; i++) {
      const ex = bomb.tx + ddx * i, ey = bomb.ty + ddy * i;
      const t  = tileAt(ex, ey);
      if (t === WALL) break;
      const bkey = `${ex},${ey}`;
      if (session.burning.has(bkey)) break;
      addExp(ex, ey);
      if (t === BLOCK) {
        const ptype = Math.random() < 0.3
          ? ['bomb', 'fire', 'speed'][Math.floor(Math.random() * 3)]
          : null;
        session.burning.set(bkey, { x: ex, y: ey, timer: 0.82, powerupType: ptype });
        break;
      }
      const cb = session.bombs.find(b => b.tx === ex && b.ty === ey);
      if (cb) { explodeBomb(cb); break; }
    }
  }
}

function dropBomb(player) {
  if (player.activeBombs >= player.maxBombs) return;
  const tx = Math.floor(player.x / T), ty = Math.floor(player.y / T);
  if (hasBomb(tx, ty)) return;
  player.activeBombs++;
  session.bombs.push({ tx, ty, timer: 3, range: player.fireRange, ownerId: player.socketId });
  emitSound('place');
}

// ─── Game tick ───────────────────────────────────────────────────────────────
function tick() {
  if (!session || session.phase !== 'playing') return;

  const now = Date.now();
  const dt  = Math.min((now - session.lastTickTime) / 1000, 0.05);
  session.lastTickTime = now;

  // Field shrink check
  if (session.shrinkBorder < session.maxShrinkBorder) {
    if (!session.shrinkWarningSent && now >= session.nextShrinkTime - 3000) {
      session.shrinkWarningSent = true;
      emitSound('shrink-warn');
    }
    if (now >= session.nextShrinkTime) {
      doShrink();
      if (session.shrinkBorder < session.maxShrinkBorder) {
        session.nextShrinkTime  = now + 60000;
        session.shrinkWarningSent = false;
      }
    }
  }

  // Move players & place bombs
  for (const [, player] of session.players) {
    if (!player.alive) continue;
    const k = player.keys;
    let dx = 0, dy = 0;
    if (k.left)  dx = -1;
    if (k.right) dx =  1;
    if (k.up)    dy = -1;
    if (k.down)  dy =  1;
    if (dx !== 0) dy = 0;
    tryMove(player, dx, dy, dt);

    if (k.bomb) {
      const tx = Math.floor(player.x / T), ty = Math.floor(player.y / T);
      if (tx !== player.lastBombTx || ty !== player.lastBombTy) {
        player.lastBombTx = tx; player.lastBombTy = ty;
        dropBomb(player);
      }
    } else {
      player.lastBombTx = -1; player.lastBombTy = -1;
    }
  }

  // Bombs countdown
  for (const b of [...session.bombs]) {
    b.timer -= dt;
    if (b.timer <= 0 && session.bombs.includes(b)) explodeBomb(b);
  }

  // Explosions fade
  for (let i = session.explosions.length - 1; i >= 0; i--) {
    session.explosions[i].timer -= dt;
    if (session.explosions[i].timer <= 0) session.explosions.splice(i, 1);
  }

  // Burning blocks clear
  for (const [key, entry] of session.burning) {
    entry.timer -= dt;
    if (entry.timer <= 0) {
      session.grid[entry.y][entry.x] = EMPTY;
      if (entry.powerupType) session.powerups.push({ x: entry.x, y: entry.y, type: entry.powerupType });
      session.burning.delete(key);
    }
  }

  // Powerups destroyed by explosion
  for (let i = session.powerups.length - 1; i >= 0; i--)
    if (hasExplosion(session.powerups[i].x, session.powerups[i].y))
      session.powerups.splice(i, 1);

  // Hit detection & powerup pickup
  const alivePlayers = [];
  for (const [, player] of session.players) {
    if (!player.alive) continue;
    const ptx = Math.floor(player.x / T), pty = Math.floor(player.y / T);
    if (hasExplosion(ptx, pty)) {
      player.alive = false;
      emitSound('die');
      continue;
    }
    alivePlayers.push(player);
    const pIdx = session.powerups.findIndex(pu => pu.x === ptx && pu.y === pty);
    if (pIdx >= 0) {
      const pu = session.powerups[pIdx];
      if (pu.type === 'bomb')  player.maxBombs++;
      if (pu.type === 'fire')  player.fireRange++;
      if (pu.type === 'speed') { player.speed += 25; player.speedLevel++; }
      session.powerups.splice(pIdx, 1);
      emitSound('pickup');
    }
  }

  // Win condition
  const threshold = session.players.size > 1 ? 1 : 0;
  if (alivePlayers.length <= threshold) {
    session.phase  = 'ended';
    session.winner = alivePlayers.length === 1 ? alivePlayers[0].name : null;
    clearInterval(session.tickInterval);
    session.tickInterval = null;
    emitSound(session.winner ? 'win' : 'die');
    io.emit('session-updated', sessionInfo());
  }

  broadcastState();
}

// ─── Session helpers ─────────────────────────────────────────────────────────
function generateId() {
  return Math.random().toString(36).substring(2, 8).toUpperCase();
}

function sessionInfo() {
  if (!session) return null;
  const base = tunnelUrl || `http://localhost:${PORT}`;
  return {
    id:        session.id,
    phase:     session.phase,
    winner:    session.winner,
    shareLink: `${base}/game.html?session=${session.id}`,
    players:   [...session.players.values()].map(p => ({
      socketId:    p.socketId,
      name:        p.name,
      slot:        p.slot,
      color:       p.color,
      alive:       p.alive,
      disconnected: p.disconnected || false,
      maxBombs:    p.maxBombs,
      fireRange:   p.fireRange,
      speedLevel:  p.speedLevel,
    })),
  };
}

function broadcastState() {
  if (!session) return;
  const state = {
    phase:      session.phase,
    winner:     session.winner,
    cols:       session.cols,
    rows:       session.rows,
    grid:       session.grid ? session.grid.flat() : null,
    players:    [...session.players.values()].map(p => ({
      socketId:    p.socketId,
      name:        p.name,
      slot:        p.slot,
      color:       p.color,
      x: p.x, y: p.y,
      alive:       p.alive,
      disconnected: p.disconnected || false,
      speed:       p.speed,
      maxBombs:    p.maxBombs,
      activeBombs: p.activeBombs,
      fireRange:   p.fireRange,
      speedLevel:  p.speedLevel,
    })),
    bombs:      session.bombs.map(b => ({ tx:b.tx, ty:b.ty, timer:b.timer, range:b.range })),
    explosions: session.explosions,
    powerups:   session.powerups,
    shrinkBorder:    session.shrinkBorder    ?? 0,
    maxShrinkBorder: session.maxShrinkBorder ?? 0,
    shrinkIn:        (session.maxShrinkBorder > 0 && session.shrinkBorder < session.maxShrinkBorder)
                       ? Math.max(0, session.nextShrinkTime - Date.now())
                       : null,
  };
  io.to(`session:${session.id}`).emit('game-state', state);
}

function startGame() {
  if (!session || session.phase !== 'lobby' || session.players.size === 0) return false;

  // Remove players still in disconnected grace period
  for (const [id, p] of [...session.players]) {
    if (p.disconnected) {
      clearTimeout(p.disconnectTimer);
      session.players.delete(id);
    }
  }
  if (session.players.size === 0) return false;

  session.phase  = 'playing';
  session.winner = null;
  session.bombs  = [];
  session.explosions = [];
  session.burning    = new Map();
  session.powerups   = [];

  const { cols, rows } = getGridSize(session.players.size);
  session.cols = cols;
  session.rows = rows;
  const spawns = getSpawns(cols, rows);
  session.grid = buildGrid(session.players.size, cols, rows, spawns);

  let slotIdx = 0;
  for (const [, player] of session.players) {
    const spawn = spawns[slotIdx % spawns.length];
    player.x          = (spawn.tx + 0.5) * T;
    player.y          = (spawn.ty + 0.5) * T;
    player.alive      = true;
    player.maxBombs   = 1;
    player.activeBombs= 0;
    player.fireRange  = 2;
    player.speed      = 90;
    player.speedLevel = 1;
    player.lastBombTx = -1;
    player.lastBombTy = -1;
    player.slot       = slotIdx;
    player.color      = COLORS[slotIdx];
    slotIdx++;
  }

  session.lastTickTime    = Date.now();
  session.shrinkBorder    = 1;
  session.maxShrinkBorder = Math.floor((Math.min(cols, rows) - 3) / 2);
  session.nextShrinkTime  = Date.now() + 60000;
  session.shrinkWarningSent = false;
  session.tickInterval = setInterval(tick, 1000 / TICK_RATE);
  return true;
}

// ─── Disconnect helpers ───────────────────────────────────────────────────────
function expelPlayer(player) {
  if (!session) return;
  player.disconnectTimer = null;
  if (session.phase === 'playing') {
    player.alive       = false;
    player.disconnected = false;
  } else {
    session.players.delete(player.socketId);
    let i = 0;
    for (const [, p] of session.players) { p.slot = i; p.color = COLORS[i]; i++; }
  }
  if (session.players.size === 0) {
    if (session.tickInterval) clearInterval(session.tickInterval);
    session = null;
  }
  io.emit('session-updated', sessionInfo());
}

// ─── Socket.IO ───────────────────────────────────────────────────────────────
io.on('connection', (socket) => {
  socket.emit('server-status', { tunnelUrl, session: sessionInfo() });

  // ── Admin: create session ──────────────────────────────────────────────────
  socket.on('create-session', () => {
    if (session && session.players.size > 0) {
      socket.emit('error-msg', 'Es gibt bereits eine aktive Session mit Spielern.');
      return;
    }
    if (session?.tickInterval) clearInterval(session.tickInterval);

    const id = generateId();
    session = {
      id,
      hostSocketId: socket.id,
      phase: 'lobby',
      players: new Map(),
      grid: null,
      bombs: [], explosions: [],
      burning: new Map(), powerups: [],
      lastTickTime: 0, tickInterval: null, winner: null,
    };
    socket.emit('session-created', sessionInfo());
    io.emit('session-updated', sessionInfo());
  });

  // ── Player: join session ───────────────────────────────────────────────────
  socket.on('join-session', ({ sessionId, name }) => {
    if (!session || session.id !== sessionId) {
      socket.emit('error-msg', 'Session nicht gefunden.');
      return;
    }

    // Reconnect: restore a temporarily disconnected player by name
    const trimmedName = (name || '').substring(0, 20);
    const reconnecting = trimmedName
      ? [...session.players.values()].find(p => p.disconnected && p.name === trimmedName)
      : null;
    if (reconnecting) {
      clearTimeout(reconnecting.disconnectTimer);
      session.players.delete(reconnecting.socketId);
      reconnecting.socketId       = socket.id;
      reconnecting.disconnected   = false;
      reconnecting.disconnectTimer = null;
      session.players.set(socket.id, reconnecting);
      socket.join(`session:${session.id}`);
      socket.emit('joined', { slot: reconnecting.slot, color: reconnecting.color, sessionId: session.id });
      if (session.phase === 'playing') {
        socket.emit('game-started');
        broadcastState();
      }
      io.emit('session-updated', sessionInfo());
      return;
    }

    if (session.players.size >= MAX_PLAYERS) {
      socket.emit('error-msg', `Session ist voll (max. ${MAX_PLAYERS} Spieler).`);
      return;
    }
    if (session.phase !== 'lobby') {
      socket.emit('error-msg', 'Das Spiel läuft bereits.');
      return;
    }
    const slot = session.players.size;
    const player = {
      socketId: socket.id,
      name:    (name || `Spieler ${slot + 1}`).substring(0, 20),
      slot,
      color:   COLORS[slot],
      alive:   true,
      x: 0, y: 0, speed: 90,
      maxBombs: 1, activeBombs: 0,
      fireRange: 2, speedLevel: 1,
      lastBombTx: -1, lastBombTy: -1,
      keys: { left:false, right:false, up:false, down:false, bomb:false },
    };
    session.players.set(socket.id, player);
    socket.join(`session:${session.id}`);
    socket.emit('joined', { slot, color: COLORS[slot], sessionId: session.id });
    io.emit('session-updated', sessionInfo());
  });

  // ── Admin: start game ──────────────────────────────────────────────────────
  socket.on('start-game', () => {
    if (!session || socket.id !== session.hostSocketId) {
      socket.emit('error-msg', 'Nur der Host kann das Spiel starten.');
      return;
    }
    if (session.players.size === 0) {
      socket.emit('error-msg', 'Keine Spieler in der Session.');
      return;
    }
    if (startGame()) {
      io.to(`session:${session.id}`).emit('game-started');
      io.emit('session-updated', sessionInfo());
      broadcastState();
    }
  });

  // ── Admin: restart ─────────────────────────────────────────────────────────
  socket.on('restart-game', () => {
    if (!session || socket.id !== session.hostSocketId) return;
    if (session.phase === 'playing') clearInterval(session.tickInterval);
    session.phase   = 'lobby';
    session.winner  = null;
    session.grid    = null;
    session.bombs   = [];
    session.explosions = [];
    session.burning = new Map();
    session.powerups = [];
    session.tickInterval    = null;
    session.shrinkBorder    = 0;
    session.maxShrinkBorder = 0;
    session.nextShrinkTime  = null;
    session.shrinkWarningSent = false;
    io.to(`session:${session.id}`).emit('game-restarted');
    io.emit('session-updated', sessionInfo());
  });

  // ── Player: input ──────────────────────────────────────────────────────────
  socket.on('input-update', (keys) => {
    if (!session) return;
    const player = session.players.get(socket.id);
    if (player && player.alive) player.keys = keys;
  });

  // ── Admin: reclaim host (after page refresh) ───────────────────────────────
  socket.on('claim-host', () => {
    if (!session) return;
    const hostGone = !io.sockets.sockets.get(session.hostSocketId);
    if (hostGone) {
      session.hostSocketId = socket.id;
      socket.emit('host-claimed');
    }
  });

  // ── Disconnect ─────────────────────────────────────────────────────────────
  socket.on('disconnect', () => {
    if (!session) return;
    if (session.players.has(socket.id)) {
      const player  = session.players.get(socket.id);
      const timeout = session.phase === 'playing'
        ? DISCONNECT_TIMEOUT_GAME
        : DISCONNECT_TIMEOUT_LOBBY;
      player.disconnected    = true;
      player.disconnectTimer = setTimeout(() => expelPlayer(player), timeout);
      io.emit('session-updated', sessionInfo());
    }
  });
});

// ─── Local network IP ─────────────────────────────────────────────────────────
function getLocalIP() {
  const nets = require('os').networkInterfaces();
  for (const name of Object.keys(nets))
    for (const net of nets[name])
      if (net.family === 'IPv4' && !net.internal) return net.address;
  return null;
}

// ─── Tunnel via Cloudflare (keine Account nötig, stabile URL) ─────────────────
function startCloudflaredTunnel() {
  return new Promise((resolve) => {
    const { bin } = require('cloudflared');
    console.log('  Erstelle Cloudflare-Tunnel...');

    const proc = spawn(bin, [
      'tunnel', '--no-autoupdate', '--url', `http://localhost:${PORT}`
    ], { stdio: ['ignore', 'pipe', 'pipe'] });

    let resolved = false;
    const timer = setTimeout(() => {
      if (!resolved) { resolved = true; resolve(null); }
    }, 30000);

    function tryParse(data) {
      const m = data.toString().match(/https:\/\/[a-z0-9-]+\.trycloudflare\.com/);
      if (m && !resolved) {
        resolved = true;
        clearTimeout(timer);
        tunnelUrl = m[0];
        console.log(`  Öffentliche URL: ${tunnelUrl}\n`);
        io.emit('server-status', { tunnelUrl, session: sessionInfo() });
        resolve(proc);
      }
    }

    proc.stdout.on('data', tryParse);
    proc.stderr.on('data', tryParse);

    proc.on('close', () => {
      if (!resolved) { resolved = true; clearTimeout(timer); resolve(null); }
      if (tunnelUrl) {
        console.warn('  Cloudflare-Tunnel getrennt – verbinde neu...');
        tunnelUrl = null;
        io.emit('server-status', { tunnelUrl: null, session: sessionInfo() });
        setTimeout(startCloudflaredTunnel, 3000);
      }
    });
  });
}

// ─── Fallback: SSH-Tunnel (localhost.run) ─────────────────────────────────────
function startSSHTunnel() {
  return new Promise((resolve) => {
    console.log('  Fallback: SSH-Tunnel (localhost.run)...');

    const proc = spawn('ssh', [
      '-o', 'StrictHostKeyChecking=no',
      '-o', 'ServerAliveInterval=15',
      '-o', 'ServerAliveCountMax=100',
      '-o', 'ExitOnForwardFailure=yes',
      '-o', 'LogLevel=ERROR',
      '-R', `80:localhost:${PORT}`,
      'nokey@localhost.run',
    ], { stdio: ['ignore', 'pipe', 'pipe'] });

    let resolved = false;
    const timer = setTimeout(() => {
      if (!resolved) { resolved = true; resolve(null); }
    }, 20000);

    function tryParse(data) {
      const m = data.toString().match(/https:\/\/[a-z0-9]+\.lhr\.life/);
      if (m && !resolved) {
        resolved = true;
        clearTimeout(timer);
        tunnelUrl = m[0];
        console.log(`  Öffentliche URL: ${tunnelUrl}\n`);
        io.emit('server-status', { tunnelUrl, session: sessionInfo() });
        resolve(proc);
      }
    }

    proc.stdout.on('data', tryParse);
    proc.stderr.on('data', tryParse);

    proc.on('close', () => {
      if (!resolved) { resolved = true; clearTimeout(timer); resolve(null); }
      if (tunnelUrl) {
        console.warn('  SSH-Tunnel getrennt – verbinde neu...');
        tunnelUrl = null;
        io.emit('server-status', { tunnelUrl: null, session: sessionInfo() });
        setTimeout(startSSHTunnel, 3000);
      }
    });
  });
}

// ─── Start server ─────────────────────────────────────────────────────────────
const localIP = getLocalIP();

httpServer.listen(PORT, async () => {
  console.log(`\n  Bomberman Multiplayer Server\n`);
  console.log(`  Admin:  http://localhost:${PORT}/`);
  if (localIP) console.log(`  LAN:    http://${localIP}:${PORT}/game.html?session=<ID>`);
  console.log();

  let tunnelProc = await startCloudflaredTunnel();
  if (!tunnelProc) tunnelProc = await startSSHTunnel();
  if (!tunnelProc) {
    console.warn('  Kein öffentlicher Tunnel. Spieler müssen im gleichen Netzwerk sein.');
    if (localIP) console.warn(`  LAN-URL: http://${localIP}:${PORT}\n`);
  }

  process.on('SIGINT', () => {
    if (tunnelProc) tunnelProc.kill();
    process.exit(0);
  });
});
