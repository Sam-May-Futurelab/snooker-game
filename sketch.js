/*
COMMENTARY (≤ 500 words)

Design overview  
The simulator is built using p5.js for rendering and Matter.js for physics. The table is modelled as a green playing surface surrounded by a wooden frame, with all measurements derived from the overall table size so the real snooker proportions are preserved (table width = table length / 2). Ball size is calculated relative to the table (ballDiameter = tableWidth / 36), and pocket size follows the required ratio (1.5 × ball diameter). Key markings such as the baulk line, D arc, and colour spots are also computed proportionally, which allows the layout to scale cleanly to different canvas sizes without distortion.

Modes and ball layout  
Balls are organised into arrays (reds, colours, cue) and created through a shared createBall() helper so that physics behaviour and visual effects are consistent across all balls. Three modes are supported. Mode 1 places the standard snooker layout with 15 reds in a triangle and the colours on their spots. Mode 2 generates clustered reds using random placement with overlap rejection, with a fallback layout if space becomes too tight. Mode 3 is a practice layout that spaces reds evenly to encourage repeated shot setups. In all modes, coloured balls remain on the table.

Physics choices  
All balls are Matter.js circular balls with tuned restitution and air friction so they roll and slow down in a natural way. Cushions are separate static bodies with higher restitution than the balls, which helps rebounds feel distinct from ball-to-ball collisions. Pockets are not physical holes; instead, a ball is considered potted when its centre enters a pocket radius and is then removed from the world. This avoids instability around pocket edges while still allowing reliable potting. If the cue ball is potted, it is removed and must be reinserted inside the D.

Cue and interaction  
The cue is rendered as a stick aligned to an aim angle, Aiming is controlled primarily by the mouse, with keyboard keys (A/D) for fine rotation. Shot power can be adjusted using W/S or by click-dragging away from the cue ball. When shooting, a single impulse force is applied using Matter.Body.applyForce. This avoids an elastic or “slingshot” feel while keeping all motion handled by the physics engine. The cue ball starts off the table and can only be placed by clicking inside the D.

Visual feedback and animation  
Moving balls leave short fading trails to indicate direction and speed. A brief expanding ring appears when the cue strikes the cue ball, and a short shrink/fade animation plays when a ball is potted. These effects are purely visual but help make interactions clearer and more responsive.

Extension - unique feature !
A trajectory predictor is included as a training aid. While aiming, a ray is cast from the cue ball and reflects off cushions, stopping at the first predicted collision with either a cushion or another ball. This is implemented using analytic ray–circle intersection for balls and ray–AABB intersection for the table bounds, followed by vector reflection for cushion bounces. Additionally, a theme switcher (C key) cycles through three table appearance presets, and a scrolling shot log tracks all attempts with potted ball indicators.

*/

// ---------- Matter aliases ----------
const {
  Engine,
  World,
  Bodies,
  Body,
  Composite,
  Vector,
} = Matter;

// ---------- Global state ----------
let engine;
let world;

let table; // computed geometry
let cushions = [];
let pockets = [];

let reds = [];
let colours = [];
let cueBall = null;

let mode = 1; // 1=standard, 2=clusters, 3=practice

const TABLE_THEMES = [ // cosmetic only
  {
    name: 'Classic',
    outerWood: '#462612',
    innerWood: '#2d1a0c',
    felt: '#16663a',
    pocket: '#0a0a0a',
  },
  {
    name: 'Pink/Gold',
    outerWood: '#8a6a1f',
    innerWood: '#6b4f12',
    felt: '#b24a72',
    pocket: '#0a0a0a',
  },
  {
    name: 'Burgundy/Mahogany',
    outerWood: '#5b2a2a',
    innerWood: '#3f1d1d',
    felt: '#5b0f1f',
    pocket: '#0a0a0a',
  },
];
let themeIndex = 0; // current theme

let aimAngle = 0;
let aimPower = 0.35;
let isAiming = false;
let dragPower = null;

let impactEffects = [];
let pocketEffects = [];
let confetti = [];

let gameOver = false;
let gameOverReason = '';

let ui = {
  resetRect: null,
  noticeResetRect: null,
};

let notice = {
  active: false,
  title: '',
  subtitle: '',
  framesLeft: 0,
};

let predictor = {
  enabled: true,
  maxBounces: 3,
};

let shotsTaken = 0;
let shotInProgress = false; // track current shot
let shotPottedThisShot = [];
let shotFoulThisShot = false;
let shotLog = [];

const UI_LAYOUT = {
  topBarH: 40,
  bottomBarH: 32,
  sidePad: 20,
  panelW: 240,
  panelH: 220,
  panelGap: 16,
};

// ---------- p5 lifecycle ----------
function setup() {
  createCanvas(1280, 720);
  angleMode(RADIANS);

  initPhysics();
  rebuildTableGeometry();
  buildTablePhysics();
  setMode(1);
}

function draw() {
  background(18);

  // rebuild if canvas size changed
  if (table == null || table._w !== width || table._h !== height) {
    rebuildTableGeometry();
    rebuildWorldForResize();
  }

  if (!gameOver) {
    stepPhysics();
    stepBalls();
    handlePotting();
    finalizeShotIfSettled();
  }

  drawTable();

  drawBalls();

  drawCueAndGuides();
  drawAnimations();
  drawHUD();
}

function keyPressed() {
  if (key === '1') setMode(1);
  if (key === '2') setMode(2);
  if (key === '3') setMode(3);

  if (key === 'c' || key === 'C') {
    themeIndex = (themeIndex + 1) % TABLE_THEMES.length;
  }

  if (key === 't' || key === 'T') {
    predictor.enabled = !predictor.enabled;
  }

  if (keyCode === ENTER || key === 'n' || key === 'N') {
    resetTable();
  }

  if (!gameOver && cueBall) {
    if (keyCode === 32) {
      tryShoot();
    }
  }
}

function mousePressed() {
  if (ui.noticeResetRect && pointInRect(mouseX, mouseY, ui.noticeResetRect)) {
    resetTable();
    return;
  }

  if (ui.resetRect && pointInRect(mouseX, mouseY, ui.resetRect)) {
    resetTable();
    return;
  }

  if (gameOver) {
    resetTable();
    return;
  }

  if (!cueBall) {
    // only place inside D
    if (pointInD(mouseX, mouseY)) {
      cueBall = createBall(mouseX, mouseY, table.ballR, '#f5f5f5', { isCue: true });
      notice.active = false;
      notice.framesLeft = 0;
    }
    return;
  }

  if (cueBall && isCueBallResting() && !areAnyBallsMoving()) {
    isAiming = true;
    dragPower = {
      start: { x: cueBall.body.position.x, y: cueBall.body.position.y },
      current: { x: mouseX, y: mouseY },
    };
  }
}

function mouseDragged() {
  if (gameOver) return;
  if (!cueBall) return;
  if (!isAiming || !dragPower) return;

  dragPower.current.x = mouseX;
  dragPower.current.y = mouseY;

  // drag distance = power
  const d = dist(dragPower.start.x, dragPower.start.y, dragPower.current.x, dragPower.current.y);
  const maxD = table.ballD * 10;
  aimPower = constrain(d / maxD, 0, 1);
}

function mouseReleased() {
  if (gameOver) return;

  if (isAiming) {
    isAiming = false;
    dragPower = null;
    tryShoot();
  }
}

// ---------- Physics init ----------
function initPhysics() {
  engine = Engine.create();
  world = engine.world;
  world.gravity.y = 0; // top-down view

  // Lets Matter auto-sleep slow balls (reduces endless tiny rolling)
  engine.enableSleeping = true;

  // Improve collision stability (helps reduce “tunneling” at higher speeds)
  engine.positionIterations = 10;
  engine.velocityIterations = 8;
  engine.constraintIterations = 2;
}

function rebuildWorldForResize() {
  Composite.clear(world, false);
  cushions = [];
  pockets = [];
  reds = [];
  colours = [];
  cueBall = null;

  buildTablePhysics();
  setMode(mode);
}

// ---------- Geometry / table ----------
function rebuildTableGeometry() {
  const reserveRight = UI_LAYOUT.panelW + UI_LAYOUT.panelGap + UI_LAYOUT.sidePad;
  const canReserveRight = width >= 980;

  const usableHeight = height - (UI_LAYOUT.topBarH + UI_LAYOUT.bottomBarH);
  const maxWidthFromHeight = usableHeight * 0.86;
  const lengthByHeight = maxWidthFromHeight * 2;

  const maxLengthFromWidth = canReserveRight
    ? (width - UI_LAYOUT.sidePad - reserveRight)
    : (width * 0.86);

  const tableLength = min(maxLengthFromWidth, lengthByHeight);
  const tableWidth = tableLength / 2; // snooker ratio

  const x = canReserveRight
    ? UI_LAYOUT.sidePad
    : (width - tableLength) / 2;
  const y = UI_LAYOUT.topBarH + (usableHeight - tableWidth) / 2;

  const ballD = tableWidth / 36;
  const ballR = ballD / 2;
  const pocketD = 1.5 * ballD;
  const pocketR = pocketD / 2;

  const rail = ballD * 1.6;

  const surface = {
    x: x + rail,
    y: y + rail,
    w: tableLength - 2 * rail,
    h: tableWidth - 2 * rail,
  };

  const baulkX = surface.x + surface.w * 0.207;
  const dRadius = surface.h * 0.165;
  const dCenter = { x: baulkX, y: surface.y + surface.h / 2 };

  const center = { x: surface.x + surface.w / 2, y: surface.y + surface.h / 2 };

  const blackX = surface.x + surface.w * 0.91;
  const blueX = center.x;
  const pinkX = surface.x + surface.w * 0.75;

  table = {
    _w: width,
    _h: height,
    x,
    y,
    w: tableLength,
    h: tableWidth,
    rail,
    surface,
    ballD,
    ballR,
    pocketR,
    baulkX,
    dRadius,
    dCenter,
    spots: {
      brown: { x: baulkX, y: center.y },
      green: { x: baulkX, y: center.y - dRadius },
      yellow: { x: baulkX, y: center.y + dRadius },
      blue: { x: blueX, y: center.y },
      pink: { x: pinkX, y: center.y },
      black: { x: blackX, y: center.y },
    },
  };

  pockets = buildPocketList();
}

function buildPocketList() {
  const s = table.surface;
  const r = table.pocketR;

  // Pocket centres slightly inset so the “hole” appears inside the cushion.
  const inset = r * 0.2;

  const tl = { x: s.x + inset, y: s.y + inset };
  const tm = { x: s.x + s.w / 2, y: s.y + inset };
  const tr = { x: s.x + s.w - inset, y: s.y + inset };
  const bl = { x: s.x + inset, y: s.y + s.h - inset };
  const bm = { x: s.x + s.w / 2, y: s.y + s.h - inset };
  const br = { x: s.x + s.w - inset, y: s.y + s.h - inset };

  return [
    { id: 'TL', ...tl },
    { id: 'TM', ...tm },
    { id: 'TR', ...tr },
    { id: 'BL', ...bl },
    { id: 'BM', ...bm },
    { id: 'BR', ...br },
  ];
}

function buildTablePhysics() {
  // Cushions are split segments so pockets are “open”.
  const s = table.surface;
  const r = table.pocketR;
  const thick = table.ballD * 1.05;

  const rest = 0.95; // cushions more bouncy than balls

  function addCushion(cx, cy, w, h) {
    const body = Bodies.rectangle(cx, cy, w, h, {
      isStatic: true,
      restitution: rest,
      friction: 0,
      frictionStatic: 0,
      frictionAir: 0,
    });
    cushions.push(body);
    World.add(world, body);
  }

  const leftX = s.x;
  const rightX = s.x + s.w;
  const topY = s.y;
  const bottomY = s.y + s.h;

  const cornerGap = r * 2.0;
  const middleGap = r * 2.1;
  addCushion(
    leftX + (s.w / 2 - middleGap / 2 - cornerGap / 2) / 2 + cornerGap / 2,
    topY - thick / 2,
    s.w / 2 - middleGap / 2 - cornerGap / 2,
    thick
  );
  addCushion(
    rightX - (s.w / 2 - middleGap / 2 - cornerGap / 2) / 2 - cornerGap / 2,
    topY - thick / 2,
    s.w / 2 - middleGap / 2 - cornerGap / 2,
    thick
  );

  addCushion(
    leftX + (s.w / 2 - middleGap / 2 - cornerGap / 2) / 2 + cornerGap / 2,
    bottomY + thick / 2,
    s.w / 2 - middleGap / 2 - cornerGap / 2,
    thick
  );
  addCushion(
    rightX - (s.w / 2 - middleGap / 2 - cornerGap / 2) / 2 - cornerGap / 2,
    bottomY + thick / 2,
    s.w / 2 - middleGap / 2 - cornerGap / 2,
    thick
  );

  addCushion(leftX - thick / 2, topY + cornerGap / 2 + (s.h - cornerGap) / 2, thick, s.h - cornerGap);
  addCushion(rightX + thick / 2, topY + cornerGap / 2 + (s.h - cornerGap) / 2, thick, s.h - cornerGap);
}

// ---------- Modes / balls ----------
function setMode(nextMode) {
  mode = nextMode;

  gameOver = false;
  gameOverReason = '';

  clearBallsOnly();
  colours = createColouredBalls();

  if (mode === 1) {
    reds = createRedsStandardTriangle();
  } else if (mode === 2) {
    reds = createRedsClusteredRandom();
  } else if (mode === 3) {
    reds = createRedsPracticeLayout();
  }

  cueBall = null;
  aimPower = 0.35;
  aimAngle = 0;

  impactEffects = [];
  pocketEffects = [];
  confetti = [];
  notice.active = false;
  notice.framesLeft = 0;

  shotsTaken = 0;
  shotInProgress = false;
  shotPottedThisShot = [];
  shotFoulThisShot = false;
  shotLog = [];
}

function clearBallsOnly() {
  const all = [...reds, ...colours];
  if (cueBall) all.push(cueBall);
  for (const b of all) {
    if (b && b.body) World.remove(world, b.body);
  }
  reds = [];
  colours = [];
  cueBall = null;
}

function createBall(x, y, r, colour, extra = {}) {
  const body = Bodies.circle(x, y, r, {
    restitution: 0.9,
    friction: 0.02,
    frictionStatic: 0.02,
    frictionAir: 0.011, // tuned for realistic roll
    slop: 0.02,
  });

  Body.setInertia(body, Infinity); // stops spinning weirdness
  body.sleepThreshold = 30;

  const ball = {
    id: extra.id || `ball_${floor(random(1e9))}`,
    colour,
    body,
    r,
    isCue: !!extra.isCue,
    isRed: !!extra.isRed,
    trail: [],
    potted: false,
  };

  World.add(world, body);
  return ball;
}

function createColouredBalls() {
  const r = table.ballR;
  const s = table.spots;
  return [
    createBall(s.yellow.x, s.yellow.y, r, '#f6e85d', { id: 'yellow' }),
    createBall(s.green.x, s.green.y, r, '#2ecc71', { id: 'green' }),
    createBall(s.brown.x, s.brown.y, r, '#8e5a2b', { id: 'brown' }),
    createBall(s.blue.x, s.blue.y, r, '#2e6cf6', { id: 'blue' }),
    createBall(s.pink.x, s.pink.y, r, '#f5a3c7', { id: 'pink' }),
    createBall(s.black.x, s.black.y, r, '#222222', { id: 'black' }),
  ];
}

function createRedsStandardTriangle() {
  const list = [];
  const r = table.ballR;
  const d = table.ballD;
  const s = table.surface;

  const apexX = table.spots.pink.x + d * 2.0;
  const centerY = s.y + s.h / 2;

  const rows = 5;
  const xStep = d * 0.98;
  const yStep = d * 1.05;

  for (let row = 0; row < rows; row++) { // build triangle
    for (let col = 0; col <= row; col++) {
      const x = apexX + row * xStep;
      const y = centerY + (col - row / 2) * yStep;
      list.push(createBall(x, y, r, '#c1121f', { isRed: true }));
    }
  }

  return list;
}

function createRedsClusteredRandom() {
  const list = [];
  const r = table.ballR;
  const s = table.surface;

  const clusterCount = 3;
  const clusters = [];
  for (let i = 0; i < clusterCount; i++) { // pick random cluster centers
    clusters.push({
      x: random(s.x + s.w * 0.55, s.x + s.w * 0.88),
      y: random(s.y + s.h * 0.20, s.y + s.h * 0.80),
      spread: random(table.ballD * 2.0, table.ballD * 4.0),
    });
  }

  for (let i = 0; i < 15; i++) {
    let placed = false;
    for (let attempt = 0; attempt < 300 && !placed; attempt++) {
      const c = clusters[floor(random(clusters.length))];
      const x = random(c.x - c.spread, c.x + c.spread);
      const y = random(c.y - c.spread, c.y + c.spread);

      if (!pointInSurface(x, y, r)) continue;
      if (!nonOverlapping(x, y, r, list, colours, cueBall)) continue;

      list.push(createBall(x, y, r, '#c1121f', { isRed: true }));
      placed = true;
    }

    if (!placed) {
      const fx = table.spots.pink.x + table.ballD * 2 + (i % 5) * table.ballD * 1.1;
      const fy = (table.surface.y + table.surface.h / 2) + (floor(i / 5) - 1) * table.ballD * 1.2;
      if (pointInSurface(fx, fy, r) && nonOverlapping(fx, fy, r, list, colours, cueBall)) {
        list.push(createBall(fx, fy, r, '#c1121f', { isRed: true }));
      }
    }
  }

  return list;
}

function createRedsPracticeLayout() {
  const list = [];
  const r = table.ballR;
  const s = table.surface;
  const d = table.ballD;

  const startX = s.x + s.w * 0.60;
  const startY = s.y + s.h * 0.22;

  const cols = 5;
  const rows = 3;

  for (let row = 0; row < rows; row++) {
    for (let col = 0; col < cols; col++) {
      const x = startX + col * d * 2.2;
      const y = startY + row * d * 2.2;
      if (pointInSurface(x, y, r) && nonOverlapping(x, y, r, list, colours, cueBall)) {
        list.push(createBall(x, y, r, '#c1121f', { isRed: true }));
      }
    }
  }

  return list;
}

// ------- Ball updates/drawing -----
function stepBalls() {
  const all = [...reds, ...colours];
  if (cueBall) all.push(cueBall);

  const s = table.surface;
  const r = table.ballR;

  for (const b of all) {
    if (!b || b.potted) continue;

    // failsafe if balls escape table
    const pos = b.body.position;
    const margin = r * 4;
    const outLeft = pos.x < s.x - margin;
    const outRight = pos.x > s.x + s.w + margin;
    const outTop = pos.y < s.y - margin;
    const outBottom = pos.y > s.y + s.h + margin;

    if (outLeft || outRight || outTop || outBottom) {
      const clampedX = constrain(pos.x, s.x + r, s.x + s.w - r);
      const clampedY = constrain(pos.y, s.y + r, s.y + s.h - r);
      Body.setPosition(b.body, { x: clampedX, y: clampedY });
      Body.setVelocity(b.body, { x: 0, y: 0 });
    }

    // cap speed to avoid tunneling
    const vel = b.body.velocity;
    const speed = Vector.magnitude(vel);
    const maxSpeed = table.ballD * 4.2;
    if (speed > maxSpeed) {
      const scale = maxSpeed / speed;
      Body.setVelocity(b.body, { x: vel.x * scale, y: vel.y * scale });
    }

    if (Vector.magnitude(b.body.velocity) > 0.15) {
      b.trail.push({
        x: b.body.position.x,
        y: b.body.position.y,
        a: 120, // more subtle
      });
    }

    for (const p of b.trail) p.a -= 18; // fade out
    b.trail = b.trail.filter((p) => p.a > 0).slice(-10); // shorter trail
  }
}

function drawBalls() {
  const all = [...reds, ...colours];
  if (cueBall) all.push(cueBall);

  for (const b of all) {
    if (!b || b.potted) continue;
    noStroke();
    fill(red(b.colour), green(b.colour), blue(b.colour), 0);

    for (let i = 0; i < b.trail.length; i++) {
      const p = b.trail[i];
      const a = p.a;
      fill(colorWithAlpha(b.colour, a * 0.6)); // more transparent
      circle(p.x, p.y, b.r * 0.8); // smaller
    }
  }

  for (const b of all) {
    if (!b || b.potted) continue;
    const pos = b.body.position;

    stroke(0, 50);
    strokeWeight(1);
    fill(b.colour);
    circle(pos.x, pos.y, b.r * 2);

    noStroke();
    fill(255, 70);
    circle(pos.x - b.r * 0.25, pos.y - b.r * 0.25, b.r * 0.55);
  }
}

// ---------- Potting ----------
function handlePotting() {
  const all = [...reds, ...colours];
  if (cueBall) all.push(cueBall);

  // forgiving pot radius
  const pr = table.pocketR * 1.18;

  for (const b of all) {
    if (!b || b.potted) continue;

    // failsafe: clamp if way out of bounds
    const pos = b.body.position;
    for (const p of pockets) {
      if (dist(pos.x, pos.y, p.x, p.y) < pr) {
        potBall(b, p);
        break;
      }
    }
  }
}

function potBall(ball, pocket) {
  ball.potted = true;
  World.remove(world, ball.body);

  pocketEffects.push({
    x: pocket.x,
    y: pocket.y,
    t: 0,
    duration: 18,
  });

  if (!ball.isCue) {
    spawnConfetti(pocket.x, pocket.y);
  }

  if (shotInProgress) {
    if (ball.isCue) {
      shotFoulThisShot = true;
    } else {
      shotPottedThisShot.push({ id: ball.id, colour: ball.colour });
    }
  }

  if (!ball.isCue && ball.id === 'black') {
    const redsCleared = reds.length > 0 && reds.every((r) => r && r.potted);
    if (redsCleared) { // frame ends when black potted after all reds
      gameOver = true;
      gameOverReason = 'Black potted (reds cleared)';
    }
  }

  if (ball.isCue) {
    cueBall = null;
    notice.active = true;
    notice.title = 'FOUL: CUE BALL POTTED';
    notice.subtitle = 'Click in the D to place the cue ball';
    notice.framesLeft = 180;
  }
}

// ---------- Cue ----------
function drawCueAndGuides() {
  if (gameOver) return;

  if (!cueBall) {
    drawCueBallPlacementGuide();
    return;
  }

  if (isCueBallResting() && !areAnyBallsMoving()) {
    const cb = cueBall.body.position;

    aimAngle = atan2(mouseY - cb.y, mouseX - cb.x);

    if (keyIsDown(65)) aimAngle -= 0.03;
    if (keyIsDown(68)) aimAngle += 0.03;
    if (keyIsDown(87)) aimPower = constrain(aimPower + 0.01, 0, 1);
    if (keyIsDown(83)) aimPower = constrain(aimPower - 0.01, 0, 1);

    // Extension: trajectory predictor (first collision + cushion bounces)
    if (predictor.enabled) {
      drawTrajectoryPredictor(cb.x, cb.y, aimAngle);
    } else {
      // Fallback simple aim line
      const lineLen = table.ballD * (6 + aimPower * 14);
      const ex = cb.x + cos(aimAngle) * lineLen;
      const ey = cb.y + sin(aimAngle) * lineLen;
      stroke(255, 70);
      strokeWeight(2);
      line(cb.x, cb.y, ex, ey);
    }

    const cueLen = table.ballD * 16;
    const cueGap = table.ballD * (1.3 + aimPower * 2.0);

    const sx = cb.x - cos(aimAngle) * cueGap;
    const sy = cb.y - sin(aimAngle) * cueGap;
    const tx = sx - cos(aimAngle) * cueLen;
    const ty = sy - sin(aimAngle) * cueLen;

    stroke(196, 160, 110, 240);
    strokeWeight(table.ballD * 0.35);
    line(tx, ty, sx, sy);

    stroke(40);
    strokeWeight(table.ballD * 0.22);
    line(sx, sy, sx + cos(aimAngle) * table.ballD * 0.8, sy + sin(aimAngle) * table.ballD * 0.8);

    if (dragPower) {
      stroke(255, 90);
      strokeWeight(1);
      line(cb.x, cb.y, dragPower.current.x, dragPower.current.y);
    }
  }
}

function tryShoot() {
  if (!cueBall) return;
  if (!isCueBallResting()) return;
  // wait for all balls to stop
  if (areAnyBallsMoving()) return;

  shotsTaken++;
  shotInProgress = true;
  shotPottedThisShot = [];
  shotFoulThisShot = false;

  const fMag = 0.012 * aimPower;
  const force = {
    x: cos(aimAngle) * fMag,
    y: sin(aimAngle) * fMag,
  };

  Body.applyForce(cueBall.body, cueBall.body.position, force);

  impactEffects.push({
    x: cueBall.body.position.x,
    y: cueBall.body.position.y,
    t: 0,
    duration: 14,
  });
}

function ballIsMoving(b) {
  if (!b || b.potted) return false;
  const v = b.body.velocity;
  return abs(v.x) > 0.08 || abs(v.y) > 0.08;
}

function areAnyBallsMoving() {
  const all = [...reds, ...colours];
  if (cueBall) all.push(cueBall);
  for (const b of all) {
    if (ballIsMoving(b)) return true;
  }
  return false;
}

function finalizeShotIfSettled() {
  if (!shotInProgress) return;
  if (areAnyBallsMoving()) return;

  const outcome = shotFoulThisShot
    ? 'Foul'
    : (shotPottedThisShot.length > 0 ? 'Potted' : 'Miss');

  shotLog.push({
    n: shotsTaken,
    outcome,
    potted: shotPottedThisShot.slice(0),
  });

  if (shotLog.length > 60) {
    shotLog = shotLog.slice(shotLog.length - 60);
  }

  shotInProgress = false;
  shotPottedThisShot = [];
  shotFoulThisShot = false;
}

function getPotStats() {
  const balls = [...reds, ...colours].filter((b) => b && !b.isCue);
  const potted = balls.reduce((acc, b) => acc + (b.potted ? 1 : 0), 0);
  const total = balls.length;
  return {
    potted,
    remaining: total - potted,
    total,
  };
}

function getDockedPanelPos(panelW, panelH, topBarH, bottomBarH, pad) {
  const gap = UI_LAYOUT.panelGap;
  const y0 = topBarH + 10;
  const maxY = height - bottomBarH - panelH - 8;
  const y = constrain(y0, topBarH + 8, maxY);

  function fits(x, y) {
    return (
      x >= pad &&
      y >= topBarH + 8 &&
      x + panelW <= width - pad &&
      y + panelH <= height - bottomBarH - 8
    );
  }

  // try right of table first
  const rightX = table.x + table.w + gap;
  if (fits(rightX, y)) return { x: rightX, y };

  const leftX = table.x - gap - panelW;
  if (fits(leftX, y)) return { x: leftX, y };

  const belowY = table.y + table.h + gap;
  const belowX = constrain(table.x + table.w / 2 - panelW / 2, pad, width - pad - panelW);
  if (fits(belowX, belowY)) return { x: belowX, y: belowY };

  return {
    x: constrain(width - pad - panelW, pad, width - pad - panelW),
    y: constrain(y0, topBarH + 8, maxY),
  };
}

function drawStatsAndLogPanel(topBarH, bottomBarH, sidePad) {
  const stats = getPotStats();

  const panelW = UI_LAYOUT.panelW;
  const canSideDock = (table.x + table.w + UI_LAYOUT.panelGap + panelW + sidePad) <= width;
  const maxTallH = height - topBarH - bottomBarH - 24;
  const panelH = canSideDock ? max(UI_LAYOUT.panelH, maxTallH) : UI_LAYOUT.panelH;
  const pos = getDockedPanelPos(panelW, panelH, topBarH, bottomBarH, sidePad);
  const x = pos.x;
  const y = pos.y;

  noStroke();
  fill(0, 0, 0, 150);
  rect(x, y, panelW, panelH, 10);
  stroke(255, 35);
  strokeWeight(1);
  noFill();
  rect(x, y, panelW, panelH, 10);

  const px = x + 12;
  let py = y + 10;

  noStroke();
  textAlign(LEFT, TOP);
  fill(230);
  textSize(12);
  textStyle(BOLD);
  text('STATS', px, py);
  textStyle(NORMAL);

  py += 22;
  fill(200);
  text(`Shots: ${shotsTaken}`, px, py);
  py += 18;
  text(`Potted: ${stats.potted} / ${stats.total}`, px, py);
  py += 18;
  text(`Remaining: ${stats.remaining}`, px, py);

  py += 16;
  stroke(255, 25);
  line(x + 10, py, x + panelW - 10, py);
  noStroke();
  py += 10;

  fill(230);
  textStyle(BOLD);
  text('LOG', px, py);
  textStyle(NORMAL);
  py += 20;

  const rowH = 22;
  const maxRows = max(0, floor((y + panelH - 12 - py) / rowH));
  const rows = shotLog.slice(-maxRows); // last N shots

  for (let i = 0; i < rows.length; i++) {
    const e = rows[i];
    const rowY = py + i * rowH;

    const label = `Shot ${e.n}: ${e.outcome}`;
    if (e.outcome === 'Potted') fill(220);
    else if (e.outcome === 'Foul') fill(255, 160);
    else fill(170);
    text(label, px, rowY);

    if (e.potted && e.potted.length) {
      const maxDots = 5;
      const dots = e.potted.slice(0, maxDots);
      const dotR = 5;
      let dx = x + panelW - 12 - dotR;
      const dy = rowY + 8;
      for (let j = dots.length - 1; j >= 0; j--) {
        const d = dots[j];
        noStroke();
        fill(d.colour);
        circle(dx, dy, dotR * 2);
        dx -= dotR * 2 + 6;
      }

      if (e.potted.length > maxDots) {
        fill(200);
        textAlign(RIGHT, TOP);
        text(`+${e.potted.length - maxDots}`, x + panelW - 10, rowY);
        textAlign(LEFT, TOP);
      }
    }
  }
}

function isCueBallResting() {
  if (!cueBall) return false;
  const v = cueBall.body.velocity;
  return abs(v.x) < 0.08 && abs(v.y) < 0.08;
}

function drawCueBallPlacementGuide() {
  const s = table.surface;

  noFill();
  stroke(235);
  strokeWeight(2);
  line(table.baulkX, s.y, table.baulkX, s.y + s.h);

  arc(table.dCenter.x, table.dCenter.y, table.dRadius * 2, table.dRadius * 2, HALF_PI, -HALF_PI);

  const ok = pointInD(mouseX, mouseY);
  fill(ok ? color(255, 255, 255, 90) : color(255, 80, 80, 90));
  noStroke();
  circle(mouseX, mouseY, table.ballD);
}

function pointInD(px, py) {
  const s = table.surface;
  if (!pointInSurface(px, py, table.ballR)) return false;
  if (px > table.baulkX) return false;

  return dist(px, py, table.dCenter.x, table.dCenter.y) <= table.dRadius;
}

function pointInSurface(px, py, marginR) {
  const s = table.surface;
  return (
    px >= s.x + marginR &&
    px <= s.x + s.w - marginR &&
    py >= s.y + marginR &&
    py <= s.y + s.h - marginR
  );
}

function nonOverlapping(x, y, r, listA, listB, cue) {
  const all = [...(listA || []), ...(listB || [])];
  if (cue) all.push(cue);
  const minDist = r * 2.05;

  for (const b of all) {
    if (!b || b.potted) continue;
    const p = b.body.position;
    if (dist(x, y, p.x, p.y) < minDist) return false;
  }
  return true;
}

// ---------- Rendering: table ----------
function drawTable() {
  const theme = TABLE_THEMES[themeIndex] || TABLE_THEMES[0];

  noStroke();
  fill(theme.outerWood);
  rect(table.x, table.y, table.w, table.h, table.ballD * 0.6);

  fill(theme.innerWood);
  rect(table.x + table.rail * 0.2, table.y + table.rail * 0.2, table.w - table.rail * 0.4, table.h - table.rail * 0.4, table.ballD * 0.5);

  fill(theme.felt);
  rect(table.surface.x, table.surface.y, table.surface.w, table.surface.h, table.ballD * 0.35);

  for (const p of pockets) {
    fill(theme.pocket);
    noStroke();
    circle(p.x, p.y, table.pocketR * 2.25);
  }

  drawLinesAndSpots();
}

function drawLinesAndSpots() {
  const s = table.surface;

  stroke(235);
  strokeWeight(2);
  noFill();

  line(table.baulkX, s.y, table.baulkX, s.y + s.h);
  arc(table.dCenter.x, table.dCenter.y, table.dRadius * 2, table.dRadius * 2, HALF_PI, -HALF_PI);

  strokeWeight(1);
  for (const k of Object.keys(table.spots)) {
    const p = table.spots[k];
    stroke(255, 130);
    point(p.x, p.y);
  }
}

// ---------- Animations ----------
function drawAnimations() {
  for (const e of impactEffects) {
    e.t++;
    const t01 = e.t / e.duration;
    const r = lerp(table.ballD * 0.2, table.ballD * 3.0, t01);
    const a = lerp(220, 0, t01);

    noFill();
    stroke(255, a);
    strokeWeight(2);
    circle(e.x, e.y, r);
  }
  impactEffects = impactEffects.filter((e) => e.t < e.duration); // remove finished

  for (const e of pocketEffects) {
    e.t++;
    const t01 = e.t / e.duration;
    const r = lerp(table.pocketR * 2.0, table.pocketR * 0.4, t01);
    const a = lerp(180, 0, t01);

    noFill();
    stroke(255, a);
    strokeWeight(2);
    circle(e.x, e.y, r);
  }
  pocketEffects = pocketEffects.filter((e) => e.t < e.duration);

  for (const c of confetti) {
    c.x += c.vx;
    c.y += c.vy;
    c.vy += 0.14;
    c.life -= 4;
    c.angle += 0.12;

    noStroke();
    fill(red(c.col), green(c.col), blue(c.col), constrain(c.life, 0, 255));
    push();
    translate(c.x, c.y);
    rotate(c.angle);
    rectMode(CENTER);
    rect(0, 0, c.size, c.size);
    pop();
  }
  confetti = confetti.filter((c) => c.life > 0);
}

function spawnConfetti(x, y) {
  for (let i = 0; i < 36; i++) {
    confetti.push({
      x,
      y,
      vx: random(-3.5, 3.5),
      vy: random(-6.0, -1.5),
      size: random(4, 8),
      col: color(random(255), random(255), random(255)),
      life: 255,
      angle: random(TWO_PI),
    });
  }
}

// ---------- HUD ----------
function drawHUD() {
  ui.resetRect = null;
  ui.noticeResetRect = null;

  const topBarH = UI_LAYOUT.topBarH;
  const bottomBarH = UI_LAYOUT.bottomBarH;
  const sidePad = UI_LAYOUT.sidePad;
  
  noStroke();
  fill(0, 0, 0, 180);
  rect(0, 0, width, topBarH);
  
  fill(255);
  textSize(16);
  textAlign(LEFT, CENTER);
  textStyle(BOLD);
  text(`SNOOKER SIMULATOR`, sidePad, topBarH / 2);
  
  textStyle(NORMAL);
  textSize(14);
  
  let modeName = "Standard";
  if (mode === 2) modeName = "Clusters";
  if (mode === 3) modeName = "Practice";
  
  textAlign(CENTER, CENTER);
  text(`MODE: ${modeName} (1-3)`, width / 2, topBarH / 2);

  textAlign(RIGHT, CENTER);
  fill(150);
  const themeName = (TABLE_THEMES[themeIndex] && TABLE_THEMES[themeIndex].name) ? TABLE_THEMES[themeIndex].name : 'Classic';
  text(`Theme: ${themeName} • C: Cycle • N/Enter: Reset`, width - sidePad, topBarH / 2);

  fill(0, 0, 0, 180);
  rect(0, height - bottomBarH, width, bottomBarH);
  
  const btnW = 86;
  const btnH = 20;
  const btnX = 14;
  const btnY = height - bottomBarH / 2 - btnH / 2;
  ui.resetRect = { x: btnX, y: btnY, w: btnW, h: btnH };
  const hot = pointInRect(mouseX, mouseY, ui.resetRect);
  fill(hot ? color(255, 255, 255, 28) : color(255, 255, 255, 18));
  stroke(255, 60);
  strokeWeight(1);
  rect(btnX, btnY, btnW, btnH, 6);
  noStroke();
  fill(230);
  textSize(12);
  textAlign(CENTER, CENTER);
  text('RESET', btnX + btnW / 2, btnY + btnH / 2);

  fill(180);
  textSize(12);
  textAlign(CENTER, CENTER);
  text(`CONTROLS: Place=Click D • Aim=Mouse/A,D • Power=W,S/Drag • Shoot=Space • T=Predictor • C=Theme • Reset=Enter/N`, width / 2, height - bottomBarH / 2);

  drawStatsAndLogPanel(topBarH, bottomBarH, sidePad);

  if (!gameOver && cueBall && isCueBallResting() && !areAnyBallsMoving()) {
    drawPowerMeter();
  }

  if (gameOver) {
    drawGameOverOverlay();
  }

  if (!gameOver) {
    drawNoticeOverlay();
  }

  const hoveringUI =
    (ui.resetRect && pointInRect(mouseX, mouseY, ui.resetRect)) ||
    (ui.noticeResetRect && pointInRect(mouseX, mouseY, ui.noticeResetRect));
  cursor(hoveringUI ? HAND : ARROW);
}

function drawTrajectoryPredictor(startX, startY, angle) {
  const s = table.surface;
  const r = table.ballR;

  // ray bounds (inside surface)
  const minX = s.x + r;
  const maxX = s.x + s.w - r;
  const minY = s.y + r;
  const maxY = s.y + s.h - r;

  let ox = constrain(startX, minX, maxX);
  let oy = constrain(startY, minY, maxY);
  let dx = cos(angle);
  let dy = sin(angle);
  const dMag = sqrt(dx * dx + dy * dy) || 1;
  dx /= dMag;
  dy /= dMag;

  const targets = [...reds, ...colours].filter((b) => b && !b.potted);

  stroke(255, 150);
  strokeWeight(2);
  noFill();

  const points = [{ x: ox, y: oy }];
  let hitBall = null;
  let hitPoint = null;

  for (let bounce = 0; bounce <= predictor.maxBounces; bounce++) {
    const wallHit = rayRectHit(ox, oy, dx, dy, minX, minY, maxX, maxY);

    let bestBallT = Infinity;
    let bestBall = null;
    for (const b of targets) {
      const t = rayCircleHit(ox, oy, dx, dy, b.body.position.x, b.body.position.y, r + b.r);
      if (t != null && t > 0 && t < bestBallT) {
        bestBallT = t;
        bestBall = b;
      }
    }

    const wallT = wallHit ? wallHit.t : Infinity;

    if (bestBall && bestBallT < wallT) {
      const px = ox + dx * bestBallT;
      const py = oy + dy * bestBallT;
      points.push({ x: px, y: py });
      hitBall = bestBall;
      hitPoint = { x: px, y: py };
      break;
    }

    if (!wallHit) {
      break;
    }

    const wx = wallHit.x;
    const wy = wallHit.y;
    points.push({ x: wx, y: wy });

    const n = wallHit.n;
    const dot = dx * n.x + dy * n.y;
    dx = dx - 2 * dot * n.x;
    dy = dy - 2 * dot * n.y;

    const eps = 0.5;
    ox = wx + dx * eps;
    oy = wy + dy * eps;
  }

  for (let i = 0; i < points.length - 1; i++) {
    const a = points[i];
    const b = points[i + 1];
    const alpha = map(i, 0, max(1, points.length - 2), 170, 90);
    stroke(255, alpha);
    line(a.x, a.y, b.x, b.y);
  }

  for (let i = 1; i < points.length - 1; i++) {
    const p = points[i];
    noFill();
    stroke(255, 120);
    circle(p.x, p.y, table.ballD * 0.35);
  }

  if (hitBall && hitPoint) {
    noFill();
    stroke(255, 220);
    circle(hitPoint.x, hitPoint.y, table.ballD * 0.55);

    stroke(255, 120);
    circle(hitBall.body.position.x, hitBall.body.position.y, (hitBall.r + table.ballR) * 2);
  }
}

function rayCircleHit(ox, oy, dx, dy, cx, cy, radius) {
  const fx = ox - cx;
  const fy = oy - cy;

  const a = dx * dx + dy * dy; // ~1
  const b = 2 * (fx * dx + fy * dy);
  const c = fx * fx + fy * fy - radius * radius;

  const disc = b * b - 4 * a * c;
  if (disc < 0) return null;

  const sdisc = sqrt(disc);
  const t1 = (-b - sdisc) / (2 * a);
  const t2 = (-b + sdisc) / (2 * a);

  if (t1 > 0.0001) return t1;
  if (t2 > 0.0001) return t2;
  return null;
}

function rayRectHit(ox, oy, dx, dy, minX, minY, maxX, maxY) {
  let bestT = Infinity;
  let best = null;

  if (abs(dx) > 1e-6) {
    const tx1 = (minX - ox) / dx;
    const y1 = oy + tx1 * dy;
    if (tx1 > 0.0001 && y1 >= minY && y1 <= maxY && tx1 < bestT) {
      bestT = tx1;
      best = { t: tx1, x: minX, y: y1, n: { x: -1, y: 0 } };
    }

    const tx2 = (maxX - ox) / dx;
    const y2 = oy + tx2 * dy;
    if (tx2 > 0.0001 && y2 >= minY && y2 <= maxY && tx2 < bestT) {
      bestT = tx2;
      best = { t: tx2, x: maxX, y: y2, n: { x: 1, y: 0 } };
    }
  }

  if (abs(dy) > 1e-6) {
    const ty1 = (minY - oy) / dy;
    const x1 = ox + ty1 * dx;
    if (ty1 > 0.0001 && x1 >= minX && x1 <= maxX && ty1 < bestT) {
      bestT = ty1;
      best = { t: ty1, x: x1, y: minY, n: { x: 0, y: -1 } };
    }

    const ty2 = (maxY - oy) / dy;
    const x2 = ox + ty2 * dx;
    if (ty2 > 0.0001 && x2 >= minX && x2 <= maxX && ty2 < bestT) {
      bestT = ty2;
      best = { t: ty2, x: x2, y: maxY, n: { x: 0, y: 1 } };
    }
  }

  return best;
}

function drawNoticeOverlay() {
  if (!notice.active) return;
  notice.framesLeft--;
  if (notice.framesLeft <= 0) {
    notice.active = false;
    return;
  }

  noStroke();
  fill(0, 160);
  rect(0, 0, width, height);

  const cardW = min(560, width * 0.90);
  const cardH = 160;
  const x = width / 2 - cardW / 2;
  const y = height / 2 - cardH / 2;
  fill(20, 20, 20, 230);
  stroke(255, 50);
  strokeWeight(1);
  rect(x, y, cardW, cardH, 12);

  noStroke();
  textAlign(CENTER, CENTER);
  textStyle(BOLD);
  textSize(22);
  fill(255);
  text(notice.title, width / 2, y + 52);

  textStyle(NORMAL);
  textSize(14);
  fill(210);
  text(notice.subtitle, width / 2, y + 92);

  const btnW = 140;
  const btnH = 28;
  const btnX = width / 2 - btnW / 2;
  const btnY = y + cardH - btnH - 16;
  ui.noticeResetRect = { x: btnX, y: btnY, w: btnW, h: btnH };

  const hot = pointInRect(mouseX, mouseY, ui.noticeResetRect);
  fill(hot ? color(255, 255, 255, 30) : color(255, 255, 255, 18));
  stroke(255, 70);
  strokeWeight(1);
  rect(btnX, btnY, btnW, btnH, 8);
  noStroke();
  fill(240);
  textAlign(CENTER, CENTER);
  textSize(12);
  textStyle(BOLD);
  text('START OVER', btnX + btnW / 2, btnY + btnH / 2);
  textStyle(NORMAL);
}

function drawGameOverOverlay() {
  noStroke();
  fill(0, 170);
  rect(0, 0, width, height);

  const cardW = min(520, width * 0.86);
  const cardH = 160;
  const x = width / 2 - cardW / 2;
  const y = height / 2 - cardH / 2;
  fill(20, 20, 20, 220);
  stroke(255, 50);
  strokeWeight(1);
  rect(x, y, cardW, cardH, 12);

  noStroke();
  fill(255);
  textAlign(CENTER, CENTER);
  textStyle(BOLD);
  textSize(28);
  text('FRAME OVER', width / 2, y + 50);

  textStyle(NORMAL);
  textSize(14);
  fill(210);
  const reason = gameOverReason ? `(${gameOverReason})` : '';
  text(`Click to reset, or press Enter/N ${reason}`, width / 2, y + 95);
}

function resetTable() {
  setMode(mode);
}

function drawPowerMeter() {
  const w = 200;
  const h = 10;
  const x = width / 2 - w / 2;
  const y = height - 60;
  
  fill(0, 100);
  stroke(255, 50);
  strokeWeight(1);
  rect(x, y, w, h, 5);
  
  noStroke();
  const c = lerpColor(color('#2ecc71'), color('#e74c3c'), aimPower);
  fill(c);
  rect(x, y, w * aimPower, h, 5);
  
  fill(255);
  textAlign(CENTER, BOTTOM);
  textSize(12);
  text(`POWER ${(aimPower * 100).toFixed(0)}%`, width / 2, y - 5);
}

// ---------- Utilities ----------
function stepPhysics() {
  // substep for stability
  const frameMs = clampDelta(deltaTime);
  const maxStepMs = 1000 / 60;
  let steps = ceil(frameMs / maxStepMs);
  steps = constrain(steps, 1, 5);
  const stepMs = frameMs / steps;

  for (let i = 0; i < steps; i++) {
    Engine.update(engine, stepMs);
  }
}

function clampDelta(ms) {
  return constrain(ms, 0, 1000 / 30);
}

function pointInRect(px, py, r) {
  return px >= r.x && px <= r.x + r.w && py >= r.y && py <= r.y + r.h;
}

function colorWithAlpha(hexOrCss, alpha) {
  const c = color(hexOrCss);
  return color(red(c), green(c), blue(c), alpha);
}
