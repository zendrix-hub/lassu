const { app, BrowserWindow, Menu, Tray, clipboard, dialog, ipcMain, nativeImage, powerMonitor, screen, shell } = require('electron');
const fs = require('fs');
const path = require('path');
const { getPhase, generateAgenda, dueItems, minutesOfDay, dateKey, nextWorkday } = require('./src/schedule');
const { habitStats, computeStreak, missedYesterday, daysRidden, weekSummary } = require('./src/habits');
const { quoteFor } = require('./src/quotes');
const { withPage, readUpTo } = require('./src/pages');
const { withTopic, advanceTopic } = require('./src/topics');
const { trayState, tooltipText, trayClickOpens, onFire, resultDelivery, trayFrame, onBlur, minimizeAtStartup } = require('./src/attention');
const { startSession, sessionLeft, sessionProgress, sessionStale, sessionOutcome } = require('./src/session');
const { cardFor, cardBounds, resultMode, stackFor, stackBounds, clampToArea, centred, dimmedFor } = require('./src/card');
const { noteFor, dailyPath, dailyHeader, captureLine, cleanCapture, todaysCaptures, scaffold } = require('./src/brain');
const { makeItem, promptText, tokenize, answerFrom, warmupFor, choicesFor, grade, weekStats } = require('./src/quiz');
const { autoDoneKeys } = require('./src/autodone');
const { eyesConfig, eyesStep, eyesCount, eyesRested, eyesBounds } = require('./src/eyes');

const CONFIG_PATH = path.join(__dirname, 'config', 'schedule.json');
const PANEL = { width: 360, height: 640 };
const EDGE = 16;
const TICK_MS = 15000;
const PULSE_MS = 800;
const ASSETS = path.join(__dirname, 'renderer', 'assets');

let cfg;
let widget;
let cardWin; // the on-screen card: quick reminders and sessions come to you (Atomic Habits: make it obvious)
let stackWin; // a second card for whatever comes up while the main card is busy (e.g. a running session)
let peekWin; // brief preview of a trail item while hovering it in the panel
let eyesWin; // 20-20-20: a card in the middle of a dimmed screen, every 20 minutes of screen time
let eyesSince = null; // when the current stretch of screen time began
let tray;
let trayImages;
let pulseFrame = 0;
let pulseTimer = null;
let shownTray = { frame: null, tip: null }; // what the shell currently shows, to skip no-op redraws
let state = { log: {}, bookmarks: {}, quiz: [], quizLog: [] };
let lastTick = { day: null, min: 0 };
let pending = []; // fired reminders not yet answered, oldest first
let riderTurn = 0;
const snoozes = new Map();
const seenKeys = new Set(); // pending reminders the user has already looked at (pulse → steady orange)
let session = null; // the running session timer, if any
let sessionTimer = null;
let sessionBig = true; // the running timer: big in the middle, or shrunk to the pill ("Use the PC")
let lastResult = null; // shown once, the next time the panel opens
let lastBranded = null; // { title, at } for the tray tooltip
let lastBlurMs = 0;
let quitting = false;
let card = null; // { key, mode } currently on screen
let cardHeight = 200; // measured by the card renderer
let cardHold = false; // the card is showing a result and fading out; don't switch it yet
const dismissed = new Set(); // quick cards that faded without an answer (they stay due in the tray)
let endedKey = null; // a session whose timer ran out and waits for Brand it
let stack = null; // { key, mode: 'quick' | 'preview' } in the second card
let stackHeight = 140;
let stackHold = false;
const previewed = new Set(); // overlapping sessions already shown as "up next" (they stay due)

const statePath = () => path.join(app.getPath('userData'), 'lassu-state.json');
const brainRoot = () => path.join(app.getPath('documents'), 'second-brain');

/* ---------- second brain: plain Markdown under Documents\second-brain ---------- */

// Create the PARA folders, README and each habit's note once; never overwrite what's there.
function ensureBrain() {
  for (const f of scaffold(cfg.habits)) {
    const file = path.join(brainRoot(), f.path);
    if (fs.existsSync(file)) continue;
    fs.mkdirSync(path.dirname(file), { recursive: true });
    fs.writeFileSync(file, f.content);
  }
}

function appendLine(rel, line, header) {
  const file = path.join(brainRoot(), rel);
  fs.mkdirSync(path.dirname(file), { recursive: true });
  if (!fs.existsSync(file)) fs.writeFileSync(file, header);
  fs.appendFileSync(file, `${line}\n`);
}

// Capture: one line into the session's note and into today's daily note.
function capture({ habitId, title, text }) {
  const clean = cleanCapture(text);
  if (!clean) return null;
  const now = new Date();
  const habit = cfg.habits.find(h => h.id === habitId) || {};
  const note = noteFor(habit);
  const line = captureLine(now, title, clean);
  appendLine(note, line, `# ${path.basename(note, '.md')}\n\n`);
  appendLine(dailyPath(now), line, dailyHeader(now));
  return { note: path.basename(note, '.md') };
}

/* ---------- warm-up quiz (Tue/Thu, start of study sessions) and the Friday review ---------- */

// Due quiz items for a pending session, with the answer hidden in `prompt` and choices when there are enough.
function warmup(key) {
  const item = pending.find(p => p.key === key);
  const habit = item && cfg.habits.find(h => h.id === item.habitId);
  if (!habit?.note || !habit.quiz) return []; // study sessions only (not Saddle Up / Sundown)
  return warmupFor(state.quiz, habit.note, new Date()).map(q => ({ id: q.id, prompt: promptText(q), text: q.text, answer: q.answer, choices: choicesFor(q, state.quiz) }));
}

function answerQuiz(id, correct) {
  if (!state.quiz.some(q => q.id === id)) return; // unknown item: don't count it in the Friday score
  const now = new Date();
  state.quiz = state.quiz.map(q => (q.id === id ? grade(q, correct, now) : q));
  state.quizLog.push({ id, date: dateKey(now), correct: !!correct });
  saveState();
}

// A journal line becomes a quiz item when the user taps its answer words (the Markdown journal is untouched).
// `from`/`to` are token indexes from tokenize(text), so the exact tapped words are blanked later.
function addQuiz({ habitId, text, from, to }) {
  const habit = cfg.habits.find(h => h.id === habitId);
  if (!habit?.note || !habit.quiz) return false;
  const toks = tokenize(text);
  if (!toks[from] || !toks[to] || from > to) return false;
  const { answer, at } = answerFrom(text, toks, from, to);
  const item = makeItem({ habitId, note: habit.note, text, answer, at, now: new Date() });
  if (!item) return false;
  state.quiz.push(item);
  saveState();
  return true;
}

// Friday review: this week's captures (Mon → today) and the warm-up score.
function weekReview() {
  const now = new Date();
  const monday = new Date(now.getFullYear(), now.getMonth(), now.getDate() - ((now.getDay() + 6) % 7), 12);
  const captures = [];
  for (let d = new Date(monday); dateKey(d) <= dateKey(now); d.setDate(d.getDate() + 1)) {
    try {
      captures.push(...todaysCaptures(fs.readFileSync(path.join(brainRoot(), dailyPath(d)), 'utf8')));
    } catch { /* no captures that day */ }
  }
  return { captures, stats: weekStats(state.quizLog, now) };
}

// Express: keep one capture to use this week.
function keepCapture(line) {
  const now = new Date();
  appendLine('2-Areas/Reflection.md', `- ⭐ Use this week (${dateKey(now)}): ${cleanCapture(line)}`, '# Reflection\n\n');
  return true;
}

function todayCaptures() {
  try {
    return todaysCaptures(fs.readFileSync(path.join(brainRoot(), dailyPath(new Date())), 'utf8'));
  } catch {
    return [];
  }
}

function loadConfig() {
  cfg = JSON.parse(fs.readFileSync(CONFIG_PATH, 'utf8'));
}

function loadState() {
  try {
    state = { ...state, ...JSON.parse(fs.readFileSync(statePath(), 'utf8')) };
  } catch {
    /* first run */
  }
}

function saveState() {
  fs.mkdirSync(path.dirname(statePath()), { recursive: true });
  fs.writeFileSync(statePath(), JSON.stringify(state, null, 2));
}

// Agenda item as shown: page in the dose, topic of the day in the title.
const decorate = (item, now) => withTopic(withPage(item, now, state.bookmarks), now, state.bookmarks);

function snapshot() {
  const now = new Date();
  const agenda = generateAgenda(now, cfg);
  const dayLog = state.log[dateKey(now)] || {};
  return {
    now: now.getTime(),
    phase: getPhase(now, cfg),
    nextWorkday: nextWorkday(now, cfg).getDay(),
    cfg: { workdays: cfg.workdays, workStart: cfg.workStart, workEnd: cfg.workEnd, lunchStart: cfg.lunchStart, lunchEnd: cfg.lunchEnd, snoozeMinutes: cfg.snoozeMinutes },
    agenda: agenda.map(i => decorate(i, now)),
    dayLog,
    pending: pending.map(i => decorate(i, now)),
    session: session && { key: session.key, title: session.title, secs: session.secs, left: sessionLeft(session, now.getTime()) },
    stats: habitStats(agenda, dayLog),
    habits: cfg.habits.map(h => ({
      id: h.id,
      name: h.name,
      icon: h.icon,
      streak: computeStreak(state.log, cfg, now, h.id),
      missedYesterday: missedYesterday(state.log, cfg, now, h.id),
    })),
    week: weekSummary(state.log, cfg, now),
    quote: quoteFor(now, agenda, pending),
    daysRidden: daysRidden(state.log),
    card,
    stack,
  };
}

function broadcast() {
  updateCards();
  const s = snapshot();
  for (const w of [widget, cardWin, stackWin]) if (w && !w.isDestroyed()) w.webContents.send('state', s);
  updateTray();
}

/* ---------- the card: comes onto the screen by itself, in the middle over a dimmed screen ---------- */

function placeCard() {
  cardWin.setBounds(cardBounds(screen.getPrimaryDisplay().workArea, cardHold ? resultMode(card.mode) : card.mode, cardHeight));
  if (stack) placeStack();
}

function placeStack() {
  stackWin.setBounds(stackBounds(screen.getPrimaryDisplay().workArea, cardWin.getBounds(), stackHold ? resultMode(stack.mode) : stack.mode, stackHeight, card?.mode));
}

// Bring a card up. In the middle it takes the keyboard (you're meant to stop and do it); on the edge it doesn't.
function present(win, mode) {
  win.setAlwaysOnTop(true, 'screen-saver');
  if (!centred(mode)) return win.showInactive(); // visible, but your keyboard stays where you were typing
  win.show();
  win.moveTop();
  app.focus({ steal: true });
  win.focus();
}

const screenDimmed = () => dimmedFor({ main: cardWin?.isVisible() && card, stack: stackWin?.isVisible() && stack });

// The second card: shows below (or above) the main card and fades; the main card never moves for it.
function updateStack() {
  if (!stackWin || stackHold) return;
  const next = cardWin.isVisible() ? stackFor({ pending, dismissed, previewed, main: card }) : null;
  if (!next) {
    stack = null;
    if (stackWin.isVisible()) stackWin.hide();
    return;
  }
  const fresh = !stack || stack.key !== next.key;
  stack = next;
  seenKeys.add(next.key);
  placeStack();
  if (!stackWin.isVisible() || fresh) present(stackWin, next.mode);
  if (fresh) stackWin.webContents.send('card-new');
}

function updateCard() {
  if (!cardWin || cardHold) return;
  const next = cardFor({ pending, dismissed, sessionKey: session?.key ?? null, sessionBig, endedKey, panelOpen: widget && panelOpen() });
  if (!next) {
    card = null;
    if (cardWin.isVisible()) cardWin.hide();
    return;
  }
  const fresh = !card || card.key !== next.key || card.mode !== next.mode;
  card = next;
  seenKeys.add(next.key); // on screen = seen: the tray stops pulsing
  placeCard();
  if (!cardWin.isVisible() || fresh) present(cardWin, next.mode);
  if (fresh) cardWin.webContents.send('card-new');
}

function updateCards() {
  updateCard();
  updateStack();
}

/* ---------- tray: the quiet badge ---------- */

const panelOpen = () => widget.isVisible() && !widget.isMinimized();

function nextUp(now) {
  const dayLog = state.log[dateKey(now)] || {};
  const min = minutesOfDay(now);
  const item = generateAgenda(now, cfg).find(i => i.min > min && !dayLog[i.key]);
  return item && { title: decorate(item, now).title, time: item.time };
}

function updateTray() {
  if (!tray) return;
  const now = new Date();
  const look = trayState({ pendingKeys: pending.map(p => p.key), seenKeys, runningKey: session?.key ?? null });
  setPulsing(look === 'due-pulse');
  const frame = trayFrame(look, pulseFrame);
  if (frame !== shownTray.frame) tray.setImage(trayImages[frame]);
  const tip = tooltipText({
    phaseId: getPhase(now, cfg).id,
    running: session && { title: session.title, left: sessionLeft(session, now.getTime()) },
    pending: pending.filter(p => p.key !== session?.key).map(p => ({ title: decorate(p, now).title })),
    next: nextUp(now),
    lastBranded,
    nowMs: now.getTime(),
  });
  if (tip !== shownTray.tip) tray.setToolTip(tip);
  shownTray = { frame, tip };
}

// The 800 ms pulse runs only while something unseen is due; at rest the tray is redrawn only on state changes.
function setPulsing(on) {
  if (on === !!pulseTimer) return;
  if (on) pulseTimer = setInterval(() => { pulseFrame ^= 1; updateTray(); }, PULSE_MS);
  else {
    clearInterval(pulseTimer);
    pulseTimer = null;
    pulseFrame = 0;
  }
}

function createTray() {
  // 1x and 2x representations so Windows picks a sharp one at 125–200% display scaling
  const img = name => {
    const src = nativeImage.createFromPath(path.join(ASSETS, name));
    const out = nativeImage.createEmpty();
    for (const scaleFactor of [1, 2]) out.addRepresentation({ scaleFactor, buffer: src.resize({ width: 16 * scaleFactor, height: 16 * scaleFactor, quality: 'best' }).toPNG() });
    return out;
  };
  trayImages = { normal: img('icon.png'), dueA: img('tray-due-a.png'), dueB: img('tray-due-b.png') };
  tray = new Tray(trayImages.normal);
  tray.setContextMenu(Menu.buildFromTemplate([
    { label: 'Open Lassu', click: showPanel },
    { type: 'separator' },
    { label: 'Quit', click: confirmQuit },
  ]));
  tray.on('click', () => {
    if (trayClickOpens({ panelVisible: panelOpen(), lastBlurMs, nowMs: Date.now() })) showPanel();
    else widget.minimize();
  });
  updateTray();
}

async function confirmQuit() {
  const { response } = await dialog.showMessageBox({ type: 'question', buttons: ['Quit', 'Cancel'], defaultId: 1, cancelId: 1, title: 'Lassu', message: 'Unsaddle and quit Lassu for today?' });
  if (response !== 0) return;
  quitting = true;
  app.quit();
}

/* ---------- the panel: a normal window that opens on click ---------- */

// Bottom-right of the primary display's work area, just above the tray.
function anchoredBounds() {
  const { workArea: wa } = screen.getPrimaryDisplay();
  return { x: wa.x + wa.width - PANEL.width - EDGE, y: wa.y + wa.height - PANEL.height - EDGE, ...PANEL };
}

function showPanel() {
  widget.setBounds(anchoredBounds());
  const wasMinimized = widget.isMinimized();
  if (wasMinimized) widget.restore(); // fires 'restore' → panelShown
  widget.setBounds(anchoredBounds()); // Windows may restore a minimized window to its old spot
  widget.show();
  widget.focus();
  if (!wasMinimized) panelShown();
}

// Whenever the panel comes up (tray, taskbar button, second launch): stop the glow, mark what's due as seen.
function panelShown() {
  widget.flashFrame(false);
  for (const p of pending) seenKeys.add(p.key);
  widget.webContents.send('panel-opened');
  broadcast();
}

/* ---------- reminders ---------- */

function fire(item) {
  if (pending.some(p => p.key === item.key)) return; // already due: no second glow for the same reminder
  pending.push({ ...item, rider: (riderTurn++ % 2) + 1, firedMin: Math.floor(minutesOfDay(new Date())) });
  const { seen } = onFire({ panelOpen: panelOpen() });
  if (seen) seenKeys.add(item.key);
  else seenKeys.delete(item.key); // a snooze coming back is unseen again
  dismissed.delete(item.key);
  previewed.delete(item.key);
  broadcast();
  const win = stack && stack.key === item.key ? stackWin : cardWin; // the card that shows it plays the clink
  if (win && !win.isDestroyed()) win.webContents.send('clink');
}

function resolve(key) {
  pending = pending.filter(p => p.key !== key);
  seenKeys.delete(key);
  dismissed.delete(key);
  previewed.delete(key);
  if (endedKey === key) endedKey = null;
  clearTimeout(snoozes.get(key));
  snoozes.delete(key);
  if (session?.key === key) stopSession();
}

// The panel shows results itself when you click; only results made while it's put away wait for the next open.
function remember(kind, item, now) {
  const result = item && { kind, title: decorate(item, now).title, streak: computeStreak(state.log, cfg, now, item.habitId) };
  lastResult = resultDelivery({ panelOpen: panelOpen() }) === 'hold' ? result : null;
  return result;
}

// Log a result for today's item and clear it from what's due (no card result, no broadcast).
function logItem(key, status, now) {
  const dayLog = (state.log[dateKey(now)] ??= {});
  const item = generateAgenda(now, cfg).find(i => i.key === key);
  if (item && status === 'done' && dayLog[key] !== 'done') state.bookmarks = advanceTopic(item, now, state.bookmarks);
  dayLog[key] = status;
  resolve(key);
  saveState();
  return item;
}

function markItem(key, status) {
  const now = new Date();
  const item = logItem(key, status, now);
  const result = remember(status === 'done' ? 'branded' : 'skipped', item, now);
  broadcast();
  return { snap: snapshot(), result };
}

/* ---------- 20-20-20: give your eyes a timer (friction removed: remembering) ---------- */

// Waits while a centred card is up (one thing at a time in front of you).
function eyesTick() {
  if (!eyesWin || eyesWin.isDestroyed()) return;
  const now = new Date();
  const o = eyesConfig(cfg);
  const step = eyesStep({ since: eyesSince, nowMs: now.getTime(), idleSecs: powerMonitor.getSystemIdleTime(), showing: eyesWin.isVisible() || screenDimmed() }, o);
  eyesSince = step.since;
  if (!step.fire) return;
  eyesWin.setBounds(eyesBounds(screen.getPrimaryDisplay().workArea));
  eyesWin.setAlwaysOnTop(true, 'screen-saver');
  eyesWin.show(); // in the middle, and it takes the keyboard: stop, look out the window
  eyesWin.moveTop();
  eyesWin.focus();
  eyesWin.webContents.send('eyes', { secs: o.lookSeconds, count: eyesCount(state.eyes, dateKey(now)) });
}

/* ---------- session timer (main process, survives the panel being minimized) ---------- */

function stopSession() {
  clearInterval(sessionTimer);
  sessionTimer = null;
  session = null;
  if (widget && !widget.isDestroyed()) widget.setProgressBar(-1);
}

function sessionTick() {
  if (!session) return;
  const now = Date.now();
  const outcome = sessionOutcome(session, now, dateKey(new Date(now)));
  if (outcome === 'stale') { // e.g. the PC slept through midnight: drop it, never brand today's item
    stopSession();
    broadcast();
    return;
  }
  if (outcome === 'done') {
    // Time's up = done: branded for you; the card opens full size on "Branded ✓" and asks for the journal line
    const key = session.key;
    const item = pending.find(p => p.key === key);
    endedKey = key;
    stopSession();
    updateCard(); // pill → full card, so the result has room
    const showing = !!item && !!card && card.key === key && cardWin.isVisible();
    if (showing) {
      cardHold = true;
      cardWin.webContents.send('auto-branded', decorate(item, new Date()));
      cardWin.webContents.send('clink');
    }
    logItem(key, 'done', new Date());
    broadcast();
    return;
  }
  widget.setProgressBar(sessionProgress(session, now));
  broadcast();
}

function tick() {
  const now = new Date();
  const day = dateKey(now);
  const min = minutesOfDay(now);

  if (lastTick.day !== day) {
    pending = [];
    seenKeys.clear();
    dismissed.clear();
    previewed.clear();
    endedKey = null;
  }
  if (session && sessionStale(session, day)) stopSession(); // dropped at midnight, not branded
  const from = lastTick.day === day ? lastTick.min : -1;
  for (const item of dueItems(generateAgenda(now, cfg), from, min)) {
    if (!(state.log[day] || {})[item.key]) fire(item);
  }
  // Still "now" after its time has passed → you did it: checked as done (never the running session or a card in use)
  const busyKeys = [cardHold && card?.key, stackHold && stack?.key].filter(Boolean);
  for (const key of autoDoneKeys({ pending: pending.map(p => decorate(p, now)), nowMin: min, sessionKey: session?.key ?? null, busyKeys })) {
    logItem(key, 'done', now);
  }
  lastTick = { day, min };
  broadcast();
}

const webPreferences = { preload: path.join(__dirname, 'preload.js'), contextIsolation: true, nodeIntegration: false, backgroundThrottling: false };
const icon = path.join(ASSETS, 'icon.png');
const APP_ID = 'Zendrix.Lassu.Widget'; // Windows caches the taskbar icon per app ID; a new ID forces a refresh
const frameless = { icon, frame: false, transparent: true, resizable: false, maximizable: false, fullscreenable: false, backgroundColor: '#00000000' };

// Windows takes the taskbar icon from a Start-menu shortcut carrying the same app ID, not from the window.
// Keep one in place (it also gives Lassu a Start-menu entry).
function writeTaskbarShortcut() {
  const lnk = path.join(app.getPath('appData'), 'Microsoft', 'Windows', 'Start Menu', 'Programs', 'Lassu.lnk');
  shell.writeShortcutLink(lnk, 'create', {
    target: process.execPath,
    args: app.isPackaged ? '' : `"${app.getAppPath()}"`,
    icon: path.join(ASSETS, 'icon.ico'),
    iconIndex: 0,
    appUserModelId: APP_ID,
    description: 'Lassu — catch the habit, keep the calm.',
  });
}

function createPanel() {
  widget = new BrowserWindow({ ...anchoredBounds(), ...frameless, show: false, title: 'Lassu', webPreferences });
  if (process.platform === 'win32') {
    widget.setAppDetails({
      appId: APP_ID,
      appIconPath: path.join(ASSETS, 'icon.ico'),
      relaunchCommand: `"${process.execPath}"${app.isPackaged ? '' : ` "${app.getAppPath()}"`}`,
      relaunchDisplayName: 'Lassu',
    });
  }
  widget.loadFile(path.join(__dirname, 'renderer', 'index.html'));
  // a taskbar button that can glow, nothing on screen (unless the tray was already clicked during launch)
  widget.once('ready-to-show', () => minimizeAtStartup({ visible: widget.isVisible() }) && widget.minimize());
  widget.webContents.on('did-finish-load', tick);
  // Clicking back into your work puts the panel away.
  widget.on('blur', () => {
    const { minimize, lastBlurMs: at } = onBlur({ minimized: widget.isMinimized(), nowMs: Date.now() });
    if (at !== null) lastBlurMs = at;
    if (minimize) widget.minimize();
  });
  widget.on('restore', panelShown); // taskbar-button click
  // Closing only puts the panel away; quitting is in the tray menu.
  widget.on('close', e => {
    if (quitting) return;
    e.preventDefault();
    widget.minimize();
  });
  widget.on('closed', () => app.quit());
  widget.on('minimize', () => { // panel put away → the card may come back; the trail preview goes
    if (peekWin && !peekWin.isDestroyed()) peekWin.hide();
    broadcast();
  });
  widget.on('restore', broadcast);
}

function createCard() {
  cardWin = new BrowserWindow({
    ...cardBounds(screen.getPrimaryDisplay().workArea, 'session', cardHeight),
    ...frameless, show: false, skipTaskbar: true, focusable: true, title: 'Lassu card', webPreferences,
  });
  cardWin.loadFile(path.join(__dirname, 'renderer', 'card.html'), { query: { slot: 'main' } });
  cardWin.webContents.on('did-finish-load', broadcast);
  stackWin = new BrowserWindow({
    ...cardBounds(screen.getPrimaryDisplay().workArea, 'quick', stackHeight),
    ...frameless, show: false, skipTaskbar: true, focusable: true, title: 'Lassu card (next)', webPreferences,
  });
  stackWin.loadFile(path.join(__dirname, 'renderer', 'card.html'), { query: { slot: 'stack' } });
  stackWin.webContents.on('did-finish-load', broadcast);
  peekWin = new BrowserWindow({ width: 300, height: 260, ...frameless, show: false, skipTaskbar: true, focusable: false, title: 'Lassu preview', webPreferences });
  peekWin.loadFile(path.join(__dirname, 'renderer', 'peek.html'));
  eyesWin = new BrowserWindow({ ...eyesBounds(screen.getPrimaryDisplay().workArea), ...frameless, show: false, skipTaskbar: true, focusable: true, title: 'Lassu eyes', webPreferences });
  eyesWin.loadFile(path.join(__dirname, 'renderer', 'eyes.html'));
}

ipcMain.handle('get-state', () => snapshot());
ipcMain.handle('mark', (_e, key, status) => markItem(key, status).snap);

ipcMain.handle('snooze', (_e, key) => {
  const item = pending.find(p => p.key === key);
  resolve(key);
  if (item) snoozes.set(key, setTimeout(() => fire(item), cfg.snoozeMinutes * 60000));
  remember('snoozed', item, new Date());
  broadcast();
  return cfg.snoozeMinutes;
});

ipcMain.handle('start-session', (_e, key) => {
  const item = pending.find(p => p.key === key);
  if (!item) return snapshot();
  stopSession();
  session = startSession(decorate(item, new Date()), Date.now());
  sessionBig = !item.usesPc; // e.g. the AP reviewer chat: start as the pill so the PC stays usable
  sessionTimer = setInterval(sessionTick, 1000);
  sessionTick();
  return snapshot();
});
ipcMain.on('session-size', (_e, big) => { // "Use the PC" ↔ expand
  sessionBig = !!big;
  broadcast();
});
ipcMain.handle('stop-session', () => {
  stopSession();
  broadcast();
  return snapshot();
});
ipcMain.handle('take-result', () => {
  const r = lastResult;
  lastResult = null;
  return r;
});
ipcMain.on('hide-panel', () => widget.minimize());
ipcMain.on('card-height', (_e, h, slot) => {
  if (slot === 'stack') {
    stackHeight = Math.ceil(h);
    if (stack) placeStack();
    return;
  }
  cardHeight = Math.ceil(h);
  if (card) placeCard();
});
ipcMain.on('card-previewed', (_e, key) => { // an overlapping session's "up next" card faded; it stays due
  previewed.add(key);
  broadcast();
});
ipcMain.on('card-dismiss', (_e, key) => { // an untouched quick card faded out
  dismissed.add(key);
  broadcast();
});
ipcMain.on('card-hold', (_e, on, slot) => { // the card shows a result, then fades; switch only after that
  if (slot === 'stack') stackHold = !!on;
  else {
    cardHold = !!on;
    if (on && card) placeCard(); // e.g. Brand it on the pill: grow to fit the result
  }
  if (!on) broadcast();
});
ipcMain.on('open-panel', () => showPanel());
ipcMain.handle('capture', (_e, entry) => capture(entry));
ipcMain.handle('today-captures', () => todayCaptures());
ipcMain.handle('warmup', (_e, key) => warmup(key));
ipcMain.handle('quiz-answer', (_e, id, correct) => answerQuiz(id, correct));
ipcMain.handle('quiz-add', (_e, entry) => addQuiz(entry));
ipcMain.handle('tokenize', (_e, text) => tokenize(String(text)));
ipcMain.handle('week-review', () => weekReview());
ipcMain.handle('keep-capture', (_e, line) => keepCapture(line));
// In-order books: "I read up to page n" → the next session opens at n + 1 (no page quota, any amount counts).
ipcMain.handle('read-up-to', (_e, habitId, n) => {
  const habit = cfg.habits.find(h => h.id === habitId);
  if (!habit) return null;
  state.bookmarks = readUpTo({ ...habit, habitId }, state.bookmarks, Number(n));
  saveState();
  broadcast();
  return state.bookmarks[habitId] ?? null;
});

// Trail preview: a small card just left of the panel, level with the hovered row.
const PEEK = { width: 300, height: 260 };
ipcMain.on('peek', (_e, key, rowTop) => {
  const now = new Date();
  const item = generateAgenda(now, cfg).find(i => i.key === key);
  if (!item || !panelOpen()) return;
  const b = widget.getBounds();
  const { workArea: wa } = screen.getPrimaryDisplay();
  const y = Math.min(Math.max(b.y + Math.round(rowTop) - 20, wa.y), wa.y + wa.height - PEEK.height);
  peekWin.setBounds({ x: b.x - PEEK.width - 4, y, ...PEEK });
  peekWin.webContents.send('peek-item', decorate(item, now));
  if (!peekWin.isVisible()) {
    peekWin.setAlwaysOnTop(true, 'floating');
    peekWin.showInactive();
  }
});
ipcMain.on('peek-hide', () => peekWin && !peekWin.isDestroyed() && peekWin.hide());
ipcMain.on('peek-height', (_e, h) => { // grew to fit its content: keep it on screen
  peekWin.setBounds(clampToArea({ ...peekWin.getBounds(), height: Math.ceil(h) }, screen.getPrimaryDisplay().workArea));
});
ipcMain.on('eyes-done', () => { // the 20 seconds ran out: rested, counted for today
  state.eyes = eyesRested(state.eyes, dateKey(new Date()));
  saveState();
  eyesWin.hide();
});
ipcMain.on('eyes-skip', () => eyesWin.hide());
ipcMain.on('copy', (_e, text) => clipboard.writeText(String(text)));

if (!app.requestSingleInstanceLock()) {
  app.quit();
} else {
  app.on('second-instance', () => widget && showPanel());
  app.on('before-quit', () => { quitting = true; });
  app.whenReady().then(() => {
    app.setAppUserModelId(APP_ID);
    loadConfig();
    loadState();
    ensureBrain();
    if (process.platform === 'win32') {
      writeTaskbarShortcut();
      app.setLoginItemSettings({
        openAtLogin: !!cfg.launchAtLogin,
        path: process.execPath,
        args: app.isPackaged ? [] : [app.getAppPath()],
      });
    }
    lastTick = { day: dateKey(new Date()), min: minutesOfDay(new Date()) };
    createPanel();
    createCard();
    createTray();
    setInterval(tick, TICK_MS);
    setInterval(eyesTick, TICK_MS);
    eyesTick();
    // Locked or asleep: your eyes rested; the next stretch starts when you're back.
    for (const ev of ['lock-screen', 'suspend', 'resume', 'unlock-screen']) powerMonitor.on(ev, () => { eyesSince = null; });
  });
  app.on('window-all-closed', () => app.quit());
}
