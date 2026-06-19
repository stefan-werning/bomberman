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
const COLS = 15, ROWS = 15, T = 36;
const EMPTY = 0, WALL = 1, BLOCK = 2;
const TICK_RATE = 25; // ticks/second
const HB = T * 0.38;

const SPAWNS = [
  { tx: 1,        ty: 1        },
  { tx: COLS - 2, ty: 1        },
  { tx: 1,        ty: ROWS - 2 },
  { tx: COLS - 2, ty: ROWS - 2 },
];

const COLORS = [
  { body: '#2277ee', head: '#ffddb0' },
  { body: '#dd2222', head: '#ffaaaa' },
  { body: '#22aa44', head: '#aaffaa' },
  { body: '#ddaa22', head: '#ffeebb' },
];

// ─── Global state ────────────────────────────────────────────────────────────
let session   = null;
let tunnelUrl = null;

// ─── Grid ────────────────────────────────────────────────────────────────────
function buildGrid(numPlayers) {
  const g = Array.from({ length: ROWS }, () => new Array(COLS).fill(EMPTY));

  for (let y = 0; y < ROWS; y++)
    for (let x = 0; x < COLS; x++)
      if (x === 0 || y === 0 || x === COLS - 1 || y === ROWS - 1 || (x % 2 === 0 && y % 2 === 0))
        g[y][x] = WALL;

  // Clear L-shaped safe zone around each active spawn
  const safe = new Set();
  for (let i = 0; i < numPlayers; i++) {
    const { tx, ty } = SPAWNS[i];
    const dx = tx < COLS / 2 ? 1 : -1;
    const dy = ty < ROWS / 2 ? 1 : -1;
    safe.add(`${tx},${ty}`);
    for (let d = 1; d <= 2; d++) {
      safe.add(`${tx + dx * d},${ty}`);
      safe.add(`${tx},${ty + dy * d}`);
    }
  }

  for (let y = 1; y < ROWS - 1; y++)
    for (let x = 1; x < COLS - 1; x++)
      if (g[y][x] === EMPTY && !safe.has(`${x},${y}`) && Math.random() < 0.45)
        g[y][x] = BLOCK;

  return g;
}

// ─── Game helpers ────────────────────────────────────────────────────────────
function tileAt(x, y) {
  if (x < 0 || y < 0 || x >= COLS || y >= ROWS) return WALL;
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
      socketId:   p.socketId,
      name:       p.name,
      slot:       p.slot,
      color:      p.color,
      alive:      p.alive,
      maxBombs:   p.maxBombs,
      fireRange:  p.fireRange,
      speedLevel: p.speedLevel,
    })),
  };
}

function broadcastState() {
  if (!session) return;
  const state = {
    phase:      session.phase,
    winner:     session.winner,
    grid:       session.grid ? session.grid.flat() : null,
    players:    [...session.players.values()].map(p => ({
      socketId:   p.socketId,
      name:       p.name,
      slot:       p.slot,
      color:      p.color,
      x: p.x, y: p.y,
      alive:      p.alive,
      maxBombs:   p.maxBombs,
      activeBombs:p.activeBombs,
      fireRange:  p.fireRange,
      speedLevel: p.speedLevel,
    })),
    bombs:      session.bombs.map(b => ({ tx:b.tx, ty:b.ty, timer:b.timer, range:b.range })),
    explosions: session.explosions,
    powerups:   session.powerups,
  };
  io.to(`session:${session.id}`).emit('game-state', state);
}

function startGame() {
  if (!session || session.phase !== 'lobby' || session.players.size === 0) return false;
  session.phase  = 'playing';
  session.winner = null;
  session.bombs  = [];
  session.explosions = [];
  session.burning    = new Map();
  session.powerups   = [];
  session.grid       = buildGrid(session.players.size);

  let slotIdx = 0;
  for (const [, player] of session.players) {
    const spawn = SPAWNS[slotIdx % 4];
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

  session.lastTickTime = Date.now();
  session.tickInterval = setInterval(tick, 1000 / TICK_RATE);
  return true;
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
    if (session.players.size >= 4) {
      socket.emit('error-msg', 'Session ist voll (max. 4 Spieler).');
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
    session.tickInterval = null;
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
      const player = session.players.get(socket.id);
      if (session.phase === 'playing') {
        player.alive = false; // mark as dead, game continues
      } else {
        session.players.delete(socket.id);
        // Repack slots
        let i = 0;
        for (const [, p] of session.players) { p.slot = i; p.color = COLORS[i]; i++; }
      }
      if (session.players.size === 0) {
        if (session.tickInterval) clearInterval(session.tickInterval);
        session = null;
      }
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
