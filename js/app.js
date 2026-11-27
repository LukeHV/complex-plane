/* Complex Plane Grapher – UI, analysis and rendering. */
(function () {
  'use strict';
  const { C, Cx, TAU, fmtNum, fmtComplex, fmtAngle, literal } = window.CX;
  const P = window.CPARSER;
  const M = window.MATH;

  const $ = (s) => document.querySelector(s);
  const esc = (s) => String(s).replace(/[&<>"]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));
  const finite = (v) => v && Number.isFinite(v.re) && Number.isFinite(v.im);

  const PALETTE = ['#e0464e', '#3b6fd8', '#2f9e66', '#8a55d6', '#f08c2e', '#0b7285', '#d6438f', '#14a3b8', '#9a6b2f', '#5c7cfa', '#2b8a3e', '#c2255c'];
  const STORE_KEY = 'complex-plane-grapher-v1';

  // ------------------------------------------------------------------ state
  const state = {
    items: [],
    view: { cx: 0, cy: 0, scale: 60 },
    settings: { grid: 'cartesian', numbers: true, vectors: false, labels: true, rings: true },
    colorIdx: 0,
  };
  let nextId = 1;
  function newItem(text = '', extra = {}) {
    if (extra.slider) { extra = Object.assign({}, extra, { ranges: { val: extra.slider } }); delete extra.slider; }
    return Object.assign({
      id: nextId++, text, color: PALETTE[state.colorIdx++ % PALETTE.length], hidden: false,
      tmin: '0', tmax: '2π', ranges: {}, play: {}, anim: {}, lastEdit: 0,
    }, extra, { ranges: Object.assign({}, extra.ranges || {}) });
  }

  // ------------------------------------------------------------------ analysis
  let analysis = { infos: new Map(), ctx: P.createContext(), version: 0, names: [], funcs: [] };
  const ENV0 = { z: C(0, 0), t: 0, loc: null };
  // Fixed sample points used to decide if an expression is real-valued.
  const SAMPLES = [];
  for (let k = 0; k < 40; k++) {
    const r = 0.3 + 6 * ((k * 0.6180339887) % 1), a = k * 2.399963;
    SAMPLES.push(C(r * Math.cos(a) + 0.137, r * Math.sin(a) - 0.071));
  }

  function errInfo(e) {
    return { kind: 'error', msg: e.message || String(e), incomplete: !!e.incomplete, undefinedName: e.undefinedName || null };
  }

  function analyze() {
    const ctx = P.createContext();
    const infos = new Map();
    const defItems = new Map();
    for (const it of state.items) {
      const text = it.text.trim();
      if (!text || text.startsWith('#') || text.startsWith('//')) continue;
      const d = P.matchDefinition(text);
      if (!d) continue;
      if (ctx.defs[d.name]) { infos.set(it.id, { kind: 'error', msg: `"${d.name}" is already defined on another line` }); continue; }
      ctx.defs[d.name] = { name: d.name, param: d.param, node: null, itemId: it.id };
      defItems.set(it.id, d);
    }
    const names = Object.keys(ctx.defs).filter((n) => !ctx.defs[n].param);
    const funcs = Object.keys(ctx.defs).filter((n) => ctx.defs[n].param);
    const nodes = new Map();
    for (const it of state.items) {
      if (infos.has(it.id)) continue;
      const text = it.text.trim();
      if (!text) { infos.set(it.id, { kind: 'empty' }); continue; }
      if (text.startsWith('#') || text.startsWith('//')) { infos.set(it.id, { kind: 'note' }); continue; }
      const d = defItems.get(it.id);
      try {
        if (d) {
          if (!d.rhs.trim()) throw new P.GraphError(`Write something after "${d.param ? `${d.name}(${d.param})` : d.name} ="`, { incomplete: true });
          const node = P.parse(d.rhs, d.param ? [...names, d.param] : names, funcs);
          ctx.defs[d.name].node = node;
          nodes.set(it.id, node);
        } else {
          nodes.set(it.id, P.parse(text, names, funcs));
        }
      } catch (e) { infos.set(it.id, errInfo(e)); }
    }
    for (const it of state.items) {
      if (infos.has(it.id)) continue;
      try {
        const info = classify(it, nodes.get(it.id), defItems.get(it.id), ctx);
        infos.set(it.id, info);
      } catch (e) { infos.set(it.id, errInfo(e)); }
    }
    analysis = { infos, ctx, version: analysis.version + 1, names, funcs };
  }

  function evalRange(text, ctx) {
    const node = P.parse(text, Object.keys(ctx.defs).filter((n) => !ctx.defs[n].param), []);
    if (P.depsOf(node, ctx).size) throw new P.GraphError('must be a number');
    const v = P.compile(node, ctx)(ENV0);
    if (!Number.isFinite(v.re) || Math.abs(v.im) > 1e-9) throw new P.GraphError('must be a real number');
    return v.re;
  }

  function paramInfo(fn, it, ctx, label) {
    const info = { kind: 'param', fn, label };
    try { info.tmin = evalRange(it.tmin || '0', ctx); } catch (e) { info.rangeErr = 'min'; }
    try { info.tmax = evalRange(it.tmax || '2π', ctx); } catch (e) { info.rangeErr = info.rangeErr ? 'both' : 'max'; }
    return info;
  }

  function classify(it, node, d, ctx) {
    if (d) {
      if (d.param) {
        P.depsOf(node, ctx, new Set([d.param]));
        P.compileDef(d.name, ctx);
        return { kind: 'func', name: d.name, param: d.param };
      }
      const deps = P.depsOf(node, ctx);
      const fn = P.compileDef(d.name, ctx);
      if (deps.has('z') && deps.has('t')) throw new P.GraphError('Use either z or t in a definition, not both');
      if (deps.size === 0) {
        const v = fn(ENV0);
        if (P.isRealLiteral(node)) return { kind: 'slider', name: d.name, value: v.re };
        if (!finite(v)) return { kind: 'error', msg: `${d.name} is undefined (division by zero?)` };
        const form = pointForm(node, ctx);
        if (form || Math.abs(v.im) > 1e-12 * Math.max(1, Math.abs(v.re))) {
          return { kind: 'point', value: v, name: d.name, draggable: !!form, form };
        }
        return { kind: 'value', name: d.name, value: v };
      }
      if (deps.has('t')) return paramInfo(fn, it, ctx, d.name);
      return { kind: 'zdef', name: d.name };
    }

    if (node.type === 'rel' || node.type === 'and' || node.type === 'or') return classifyRelation(node, ctx, it);

    const deps = P.depsOf(node, ctx);
    const fn = P.compile(node, ctx);
    if (deps.has('z') && deps.has('t')) throw new P.GraphError('Use z for loci or t for curves – not both in one expression');
    if (deps.size === 0) {
      const v = fn(ENV0);
      if (!finite(v)) return { kind: 'error', msg: 'This value is undefined (division by zero?)' };
      const form = pointForm(node, ctx);
      return { kind: 'point', value: v, name: null, draggable: !!form, form };
    }
    if (deps.has('t')) return paramInfo(fn, it, ctx, null);
    // A real-valued expression such as |z - 1| is almost always a locus being typed: prompt, don't colour.
    if (isRealValued(fn, () => C(0, 0))) return { kind: 'hint' };
    return { kind: 'domain', fn };
  }

  // 'cart' for a + bi literals, 'polar' for r·e^(iθ) / r·cis(θ) with constant r and θ.
  function pointForm(node, ctx) {
    if (P.isComplexLiteral(node)) return 'cart';
    const pp = P.polarParts(node);
    if (pp) {
      const e = P.compile(pp.e, ctx)(ENV0);
      if (pp.cis ? Math.abs(e.im) < 1e-12 : Math.abs(e.re) < 1e-12) return 'polar';
    }
    return null;
  }

  function isRealValued(L, R) {
    const env = { z: null, t: 0, loc: null };
    let any = false;
    for (const s of SAMPLES) {
      env.z = s;
      const a = L(env), b = R(env);
      if (!finite(a) || !finite(b)) continue;
      any = true;
      const tol = 1e-9 * (1 + Math.abs(a.re) + Math.abs(b.re));
      if (Math.abs(a.im) > tol || Math.abs(b.im) > tol) return false;
    }
    return any || true;
  }

  function classifyRelation(node, ctx, it) {
    const isZ = (n) => n.type === 'name' && n.name === 'z';
    if (node.type === 'rel' && node.op === 'eq') {
      for (const [side, other] of [[node.a, node.b], [node.b, node.a]]) {
        if (isZ(side)) {
          const od = P.depsOf(other, ctx);
          if (od.has('t') && !od.has('z')) return paramInfo(P.compile(other, ctx), it, ctx, null);
        }
      }
    }
    const deps = P.depsOf(node, ctx);
    if (deps.has('t')) throw new P.GraphError('t is for parametric curves, e.g.  z = 2e^(it)');

    if (node.type === 'rel' && node.op === 'eq' && deps.has('z')) {
      const L = P.compile(node.a, ctx), R = P.compile(node.b, ctx);
      if (!isRealValued(L, R)) {
        const prev = analysis.infos.get(it.id);
        const roots = prev && prev.kind === 'roots' ? prev.roots : [];
        return { kind: 'roots', g: (env) => Cx.sub(L(env), R(env)), roots, rootsKey: '' };
      }
    }

    const atoms = [];
    const build = (n) => {
      if (n.type === 'and' || n.type === 'or') return { type: n.type, a: build(n.a), b: build(n.b) };
      if (n.type !== 'rel') throw new P.GraphError('Each part joined by "and" / "or" needs =, <, >, ≤ or ≥');
      const L = P.compile(n.a, ctx), R = P.compile(n.b, ctx);
      if (!isRealValued(L, R)) {
        throw new P.GraphError(n.op === 'eq'
          ? 'Inside "and"/"or", compare real quantities such as |z|, Re(z), Im(z) or arg(z)'
          : 'Inequalities compare real numbers – use |z|, Re(z), Im(z) or arg(z)');
      }
      const wrap = n.op === 'eq' && P.isAngleExpr(n.a, ctx) && P.isAngleExpr(n.b, ctx);
      atoms.push({ L, R, op: n.op, wrap, node: n });
      return { type: 'atom', i: atoms.length - 1 };
    };
    const tree = build(node);

    if (!deps.has('z')) {
      const val = evalTree(tree, atoms, 0, 0, null, true);
      return { kind: 'truth', value: val };
    }
    // Two equations joined by "and": their intersection points.
    if (tree.type === 'and' && tree.a.type === 'atom' && tree.b.type === 'atom' &&
        atoms[0].op === 'eq' && atoms[1].op === 'eq' && deps.has('z')) {
      const [a1, a2] = atoms;
      const prev = analysis.infos.get(it.id);
      return {
        kind: 'roots', intersect: true, roots: prev && prev.kind === 'roots' ? prev.roots : [], rootsKey: '',
        g: (env) => { const x = env.z.re, y = env.z.im; return C(atomVal(a1, x, y), atomVal(a2, x, y)); },
        curves: { atoms, tree: { type: 'or', a: tree.a, b: tree.b }, hasFill: false },
      };
    }
    const hasOr = (t) => t.type === 'or' || (t.type === 'and' && (hasOr(t.a) || hasOr(t.b)));
    const hasEq = atoms.some((a) => a.op === 'eq');
    // With only "and", an equation restricts everything to a curve, so nothing is shaded.
    const hasFill = atoms.some((a) => a.op !== 'eq') && (!hasEq || hasOr(tree));
    const info = { kind: 'locus', atoms, tree, hasFill };
    info.desc = describe(node, ctx, info);
    return info;
  }

  const tmpEnv = { z: { re: 0, im: 0 }, t: 0, loc: null };
  function atomVal(at, x, y) {
    tmpEnv.z = { re: x, im: y };
    let d = at.L(tmpEnv).re - at.R(tmpEnv).re;
    if (at.wrap) d -= TAU * Math.round(d / TAU);
    return d;
  }
  // Evaluate an and/or tree at a point. ov = {i, v} forces one atom's truth value.
  // constMode evaluates equalities too (used when nothing depends on z).
  function evalTree(tr, atoms, x, y, ov, constMode) {
    switch (tr.type) {
      case 'and': return evalTree(tr.a, atoms, x, y, ov, constMode) && evalTree(tr.b, atoms, x, y, ov, constMode);
      case 'or': return evalTree(tr.a, atoms, x, y, ov, constMode) || evalTree(tr.b, atoms, x, y, ov, constMode);
      default: {
        if (ov && ov.i === tr.i) return ov.v;
        const at = atoms[tr.i];
        if (at.op === 'eq' && !constMode) return false;
        const d = atomVal(at, x, y);
        if (d !== d) return false;
        switch (at.op) {
          case 'lt': return d < 0; case 'le': return d <= 0;
          case 'gt': return d > 0; case 'ge': return d >= 0;
          case 'eq': return Math.abs(d) < 1e-9;
        }
      }
    }
    return false;
  }

  // ------------------------------------------------------------------ describing loci
  function describe(node, ctx, info) {
    const isConst = (n) => { try { return P.depsOf(n, ctx).size === 0; } catch (e) { return false; } };
    const val = (n) => P.compile(n, ctx)(ENV0);
    const isZ = (n) => n.type === 'name' && n.name === 'z';
    // Returns c if n is (z - c), else null.
    const zMinus = (n) => {
      if (isZ(n)) return C(0, 0);
      if (n.type === 'bin' && (n.op === '-' || n.op === '+')) {
        if (isConst(n.b)) {
          const inner = zMinus(n.a);
          if (inner) return n.op === '-' ? Cx.add(inner, val(n.b)) : Cx.sub(inner, val(n.b));
        }
        if (n.op === '+' && isZ(n.b) && isConst(n.a)) return Cx.neg(val(n.a));
      }
      return null;
    };
    const absC = (n) => {
      if (n.type === 'call' && (n.fn === 'abs' || n.fn === 'mod')) {
        const a = n.args[0];
        const c = zMinus(a);
        if (c) return c;
        if (a.type === 'bin' && a.op === '-' && isZ(a.b) && isConst(a.a)) return val(a.a);
      }
      return null;
    };
    // |αz + β| = |α|·|z − c| with c = −β/α: returns { c, m: |α| } when the inside is affine in z.
    const absAff = (n) => {
      const c0 = absC(n);
      if (c0) return { c: c0, m: 1 };
      if (n.type !== 'call' || (n.fn !== 'abs' && n.fn !== 'mod')) return null;
      let fz;
      try {
        const d = P.depsOf(n.args[0], ctx);
        if (d.size !== 1 || !d.has('z')) return null;
        fz = P.compile(n.args[0], ctx);
      } catch (e) { return null; }
      const at = (z) => fz({ z, t: 0, loc: null });
      const beta = at(C(0, 0)), alpha = Cx.sub(at(C(1, 0)), beta);
      if (!finite(beta) || !finite(alpha) || Cx.abs(alpha) < 1e-12) return null;
      for (const z of [C(0, 1), C(-1.7, 0.6), C(2.3, -3.1)]) {
        const want = Cx.add(Cx.mul(alpha, z), beta), got = at(z);
        if (!finite(got) || Cx.abs(Cx.sub(got, want)) > 1e-9 * (1 + Cx.abs(want))) return null;
      }
      const c = Cx.div(Cx.neg(beta), alpha);
      return { c: C(Math.abs(c.re) < 1e-12 ? 0 : c.re, Math.abs(c.im) < 1e-12 ? 0 : c.im), m: Cx.abs(alpha) };
    };
    const argC = (n) => (n.type === 'call' && n.fn === 'arg') ? zMinus(n.args[0]) : null;
    const realConst = (n) => {
      if (!isConst(n)) return null;
      const v = val(n);
      return Math.abs(v.im) < 1e-12 && Number.isFinite(v.re) ? v.re : null;
    };
    // Inline in a 12.5 px status line: the small maths size used by point statuses.
    const sm = (h) => `<span class="math sm">${h}</span>`;
    const F = (c) => sm(M.complex(c));
    const N = (x) => sm(M.real(x));
    const ANG = (a) => sm(M.angle(a));
    const reIm = (n) => n.type === 'call' && (n.fn === 're' || n.fn === 'im') && isZ(n.args[0]) ? n.fn
      : (n.type === 'name' && (n.name === 'x' || n.name === 'y')) ? (n.name === 'x' ? 're' : 'im') : null;

    if (node.type === 'and' && node.chain && node.a.type === 'rel' && node.b.type === 'rel' && node.a.b === node.b.a) {
      // r1 < |z − c| < r2 (any mix of < and ≤): an annulus
      const mid = absAff(node.a.b), r1 = realConst(node.a.a), r2 = realConst(node.b.b);
      const up = (o) => o === 'lt' || o === 'le';
      if (mid && r1 !== null && r2 !== null && up(node.a.op) && up(node.b.op) && r2 / mid.m > Math.max(0, r1 / mid.m)) {
        const inc = (o) => (o === 'le' ? 'included' : 'not included');
        const a1 = r1 / mid.m, a2 = r2 / mid.m;
        if (a1 < 0 || (a1 === 0 && node.a.op === 'le')) {
          return { kind: 'Region', text: `inside the circle centre ${F(mid.c)}, radius ${N(a2)} (edge ${inc(node.b.op)})` };
        }
        if (a1 === 0) return { kind: 'Region', text: `inside the circle centre ${F(mid.c)}, radius ${N(a2)} (edge ${inc(node.b.op)}), except the centre itself` };
        return { kind: 'Region', text: `between the circles centre ${F(mid.c)}, radii ${N(a1)} and ${N(a2)} (inner edge ${inc(node.a.op)}, outer edge ${inc(node.b.op)})` };
      }
    }
    if (node.type === 'and' || node.type === 'or') {
      if (info.hasFill) return { kind: 'Region', text: 'shaded where the conditions hold' };
      return { kind: 'Curve', text: 'the part of the curve where the other conditions hold' };
    }
    const op = node.op;
    // put the z-side on the left
    let A = node.a, B = node.b, o = op;
    if (isConst(A) && !isConst(B)) {
      [A, B] = [B, A];
      o = { lt: 'gt', gt: 'lt', le: 'ge', ge: 'le', eq: 'eq' }[op];
    }
    const inside = o === 'lt' || o === 'le';
    const incl = (o === 'le' || o === 'ge') ? ' (edge included)' : ' (edge not included)';

    let c, r, aff;
    if ((aff = absAff(A)) && (r = realConst(B)) !== null) {
      c = aff.c; r /= aff.m;
      if (o === 'eq') {
        if (r > 0) return { kind: 'Circle', text: `centre ${F(c)}, radius ${N(r)}` };
        if (r === 0) { info.extraPoint = c; return { kind: 'Point', text: `just the point ${F(c)}` }; }
        return { kind: 'Empty', text: 'no points – a distance can’t be negative' };
      }
      return { kind: 'Region', text: `${inside ? 'inside' : 'outside'} the circle centre ${F(c)}, radius ${N(r)}${incl}` };
    }
    let c2;
    if ((c = absC(A)) && (c2 = absC(B))) {
      if (o === 'eq') {
        if (Cx.abs(Cx.sub(c, c2)) < 1e-12) return { kind: 'Everywhere', text: 'both distances are always equal' };
        return { kind: 'Line', text: `perpendicular bisector of ${F(c)} and ${F(c2)}` };
      }
      return { kind: 'Region', text: `points nearer to ${inside ? F(c) : F(c2)} than to ${inside ? F(c2) : F(c)}${incl}` };
    }
    if (o === 'eq' && (c = absC(A)) && B.type === 'bin' && B.op === '*') {
      let kNode = null, other = null;
      if (absC(B.b) && realConst(B.a) !== null) { kNode = B.a; other = B.b; }
      else if (absC(B.a) && realConst(B.b) !== null) { kNode = B.b; other = B.a; }
      if (kNode) {
        const k = realConst(kNode); c2 = absC(other);
        const same = Cx.abs(Cx.sub(c, c2)) < 1e-12;
        // k = 0 leaves |z − c| = 0; k < 0 asks a distance to equal a negative number (only 0 = 0 works).
        if (Math.abs(k) < 1e-12 || (k < 0 && same)) { info.extraPoint = c; return { kind: 'Point', text: `just the point ${F(c)}` }; }
        if (k < 0) return { kind: 'Empty', text: 'no points – a distance can’t be negative' };
        if (same) {
          if (Math.abs(k - 1) <= 1e-12) return { kind: 'Everywhere', text: 'both distances are always equal' };
          info.extraPoint = c; return { kind: 'Point', text: `just the point ${F(c)}` };
        }
        if (k > 0 && Math.abs(k - 1) > 1e-12) {
          // |z-c| = k|z-c2|  ->  circle with centre (c - k^2 c2)/(1 - k^2), radius k|c-c2|/|1-k^2|
          const k2 = k * k;
          const centre = Cx.div(Cx.sub(c, Cx.mul(C(k2, 0), c2)), C(1 - k2, 0));
          const rad = k * Cx.abs(Cx.sub(c, c2)) / Math.abs(1 - k2);
          return { kind: 'Circle', text: `centre ${F(centre)}, radius ${N(rad)} (circle of Apollonius)` };
        }
        if (Math.abs(k - 1) <= 1e-12) return { kind: 'Line', text: `perpendicular bisector of ${F(c)} and ${F(c2)}` };
      }
    }
    // arg gives the principal value, −π < arg ≤ π: outside that range an equation has no points.
    const outOfRange = (th) => th > Math.PI + 1e-12 || th <= -Math.PI + 1e-12;
    const noArg = (th) => {
      info.empty = true;
      const p = th - TAU * Math.round(th / TAU), same = Math.abs(p + Math.PI) < 1e-12 ? Math.PI : p;
      return { kind: 'Empty', text: `no points – arg takes values with −π &lt; arg ≤ π. Did you mean ${ANG(same)}?` };
    };
    if ((c = argC(A)) && (r = realConst(B)) !== null) {
      if (o === 'eq') {
        if (outOfRange(r)) return noArg(r);
        info.openPoint = c;
        return { kind: 'Half-line', text: `from ${F(c)} at angle ${ANG(r)}; the end point ${F(c)} is not included` };
      }
      return { kind: 'Region', text: `points whose angle from ${F(c)} is ${{ lt: '&lt;', le: '≤', gt: '&gt;', ge: '≥' }[o]} ${ANG(r)}` };
    }
    if (A.type === 'bin' && A.op === '+' && (c = absC(A.a)) && (c2 = absC(A.b)) && (r = realConst(B)) !== null) {
      const dist = Cx.abs(Cx.sub(c, c2));
      if (o === 'eq') {
        if (r > dist + 1e-12) return { kind: 'Ellipse', text: `foci ${F(c)} and ${F(c2)}, total distance ${N(r)}` };
        if (Math.abs(r - dist) <= 1e-12) { info.extraSegment = [c, c2]; return { kind: 'Segment', text: `the line segment from ${F(c)} to ${F(c2)}` }; }
        return { kind: 'Empty', text: `no points – the total distance must be at least ${N(dist)}` };
      }
      return { kind: 'Region', text: `${inside ? 'inside' : 'outside'} the ellipse with foci ${F(c)} and ${F(c2)}` };
    }
    // arg((z − a)/(z − b)) = θ, or arg(z − a) − arg(z − b) = θ: an arc of a circle through a and b
    let ab = null;
    if (A.type === 'bin' && A.op === '-' && (c = argC(A.a)) && (c2 = argC(A.b))) ab = [c, c2];
    else if (A.type === 'call' && A.fn === 'arg' && A.args[0].type === 'bin' && A.args[0].op === '/' &&
      (c = zMinus(A.args[0].a)) && (c2 = zMinus(A.args[0].b))) ab = [c, c2];
    if (ab && (r = realConst(B)) !== null && o === 'eq' && Cx.abs(Cx.sub(ab[0], ab[1])) > 1e-12) {
      if (A.type === 'call' && outOfRange(r)) return noArg(r);
      const [a, b] = ab;
      const th = r - TAU * Math.round(r / TAU); // principal value, in (−π, π]
      info.openPoints = [a, b];
      const ends = `${F(a)} and ${F(b)}`;
      if (Math.abs(th) < 1e-12) return { kind: 'Line', text: `the line through ${ends}, except the segment between them` };
      if (Math.abs(Math.abs(th) - Math.PI) < 1e-12) return { kind: 'Segment', text: `between ${ends}; the end points are not included` };
      // centre = (a − b·e^{2iθ}) / (1 − e^{2iθ})
      const e2 = C(Math.cos(2 * th), Math.sin(2 * th));
      const centre = Cx.div(Cx.sub(a, Cx.mul(b, e2)), Cx.sub(C(1, 0), e2));
      const tidy = (v) => C(Math.abs(v.re) < 1e-12 ? 0 : v.re, Math.abs(v.im) < 1e-12 ? 0 : v.im);
      return {
        kind: 'Arc',
        text: `${Math.abs(Math.abs(th) - Math.PI / 2) < 1e-12 ? 'half' : Math.abs(th) > Math.PI / 2 ? 'minor arc' : 'major arc'} of the circle centre ${F(tidy(centre))}, radius ${N(Cx.abs(Cx.sub(a, centre)))}, from ${F(b)} to ${F(a)}; the end points are not included`,
      };
    }
    const ri = reIm(A);
    if (ri && (r = realConst(B)) !== null) {
      const ax = ri === 're' ? 'Re(z)' : 'Im(z)';
      if (o === 'eq') return { kind: 'Line', text: `${ri === 're' ? 'vertical' : 'horizontal'} line ${ax} = ${N(r)}` };
      return { kind: 'Region', text: `half-plane ${ax} ${{ lt: '&lt;', le: '≤', gt: '&gt;', ge: '≥' }[o]} ${N(r)}${incl}` };
    }
    return o === 'eq' ? { kind: 'Curve', text: 'all z satisfying the equation' } : { kind: 'Region', text: 'shaded where the inequality holds' + incl };
  }

  // ------------------------------------------------------------------ canvas + view
  const canvas = $('#plot');
  const g = canvas.getContext('2d');
  const stage = $('#stage');
  let W = 0, H = 0, DPR = 1, pendingHome = false;
  const view = state.view;
  const toSX = (x) => W / 2 + (x - view.cx) * view.scale;
  const toSY = (y) => H / 2 - (y - view.cy) * view.scale;
  const toWX = (sx) => view.cx + (sx - W / 2) / view.scale;
  const toWY = (sy) => view.cy - (sy - H / 2) / view.scale;

  function resize() {
    const r = stage.getBoundingClientRect();
    W = r.width; H = r.height; DPR = window.devicePixelRatio || 1;
    canvas.width = Math.max(1, Math.round(W * DPR));
    canvas.height = Math.max(1, Math.round(H * DPR));
    if (pendingHome && W > 0 && H > 0) { pendingHome = false; homeView(); }
    fitAllMath();
    // Setting canvas.width clears it; draw now so no blank frame flashes before the next rAF.
    render(false);
  }

  let homeHalfWidth = 0;
  function homeView() {
    view.cx = 0; view.cy = 0;
    view.scale = homeHalfWidth ? Math.min(W, H) / (2 * homeHalfWidth) : Math.max(20, Math.min(W, H) / 11);
    homeHalfWidth = 0;
  }

  function niceStep(raw) {
    const p = Math.pow(10, Math.floor(Math.log10(raw)));
    const m = raw / p;
    return (m < 1.5 ? 1 : m < 3.5 ? 2 : m < 7.5 ? 5 : 10) * p;
  }

  let renderQueued = false, fastPending = false, idleTimer = 0;
  function requestRender(fast) {
    if (fast) {
      fastPending = true;
      clearTimeout(idleTimer);
      idleTimer = setTimeout(() => { fastPending = false; requestRender(false); }, 160);
    }
    if (renderQueued) return;
    renderQueued = true;
    requestAnimationFrame(() => { renderQueued = false; render(fastPending); });
  }

  let pointHits = [];
  let labelBoxes = [];
  let offCanvas = document.createElement('canvas');
  let offCtx = offCanvas.getContext('2d');

  function render(fast) {
    if (!W || !H) return;
    g.setTransform(DPR, 0, 0, DPR, 0, 0);
    g.fillStyle = '#fff';
    g.fillRect(0, 0, W, H);
    pointHits = [];
    labelBoxes = [];
    const visible = state.items.filter((it) => !it.hidden && analysis.infos.get(it.id));
    const byKind = (k) => visible.filter((it) => analysis.infos.get(it.id).kind === k);
    const safe = (f) => { try { f(); } catch (e) { console.warn(e); } };

    const typingDomain = (it) => it.id === focusedId && Date.now() - it.lastEdit < 1200;
    const domains = byKind('domain').filter((it) => !typingDomain(it));
    if (byKind('domain').some(typingDomain)) { clearTimeout(domainTimer); domainTimer = setTimeout(() => requestRender(false), 1250); }
    domains.forEach((it) => safe(() => drawDomain(analysis.infos.get(it.id), fast)));
    g.save();
    if (domains.length) g.globalAlpha = 0.35;
    drawGrid();
    g.restore();
    const hlId = highlightId();
    const hl = hlId && visible.some((it) => it.id === hlId && analysis.infos.get(it.id).kind !== 'domain') ? hlId : null;
    const emph = (it, f) => {
      g.save();
      if (hl && hl !== it.id) g.globalAlpha = 0.28;
      lineBoost = hl === it.id ? 1.45 : 1;
      safe(f);
      lineBoost = 1;
      g.restore();
    };
    byKind('locus').forEach((it) => emph(it, () => drawLocusFill(analysis.infos.get(it.id), it.color, fast)));
    byKind('locus').forEach((it) => emph(it, () => drawLocusLines(analysis.infos.get(it.id), it.color, fast)));
    byKind('param').forEach((it) => emph(it, () => drawParam(analysis.infos.get(it.id), it.color, fast)));
    byKind('roots').forEach((it) => emph(it, () => drawRoots(analysis.infos.get(it.id), it, fast)));
    byKind('locus').forEach((it) => emph(it, () => {
      const info = analysis.infos.get(it.id);
      if (info.extraPoint) drawDot(info.extraPoint.re, info.extraPoint.im, it.color, null, false);
      if (info.atoms.length === 1) {
        if (info.openPoint) drawOpenCircle(info.openPoint, it.color);
        if (info.openPoints) info.openPoints.forEach((p) => drawOpenCircle(p, it.color));
      }
    }));
    // points last, so a defined point is never hidden under a curve's end marker
    byKind('point').forEach((it) => emph(it, () => drawPointItem(analysis.infos.get(it.id), it)));
    if (hoverPt) drawHoverRing(hoverPt);
  }

  // ---------- grid ----------
  function drawGrid() {
    const s = state.settings;
    const major = niceStep(85 / view.scale);
    const mant = Math.round(major / Math.pow(10, Math.floor(Math.log10(major) + 1e-9)));
    const minor = major / (mant === 2 ? 4 : 5);
    const x0 = toWX(0), x1 = toWX(W), y0 = toWY(H), y1 = toWY(0);
    const ox = toSX(0), oy = toSY(0);
    g.lineWidth = 1;

    if (s.grid === 'cartesian') {
      const lines = (step, color) => {
        g.strokeStyle = color;
        g.beginPath();
        for (let k = Math.ceil(x0 / step); k * step <= x1; k++) { const X = Math.round(toSX(k * step)) + 0.5; g.moveTo(X, 0); g.lineTo(X, H); }
        for (let k = Math.ceil(y0 / step); k * step <= y1; k++) { const Y = Math.round(toSY(k * step)) + 0.5; g.moveTo(0, Y); g.lineTo(W, Y); }
        g.stroke();
      };
      lines(minor, '#f0f2f6');
      lines(major, '#dde1e8');
    } else if (s.grid === 'polar') {
      const corners = [[x0, y0], [x0, y1], [x1, y0], [x1, y1]];
      const rmax = Math.max(...corners.map(([a, b]) => Math.hypot(a, b)));
      const inView = ox >= 0 && ox <= W && oy >= 0 && oy <= H;
      const rmin = inView ? 0 : Math.min(
        Math.hypot(Math.max(x0, Math.min(0, x1)), Math.max(y0, Math.min(0, y1))));
      g.strokeStyle = '#dde1e8';
      g.beginPath();
      for (let k = Math.max(1, Math.floor(rmin / major)); k * major <= rmax && k < 2000; k++) {
        g.moveTo(ox + k * major * view.scale, oy);
        g.arc(ox, oy, k * major * view.scale, 0, TAU);
      }
      g.stroke();
      const R = rmax * view.scale + 10;
      for (let k = 0; k < 24; k++) {
        const a = k * Math.PI / 12;
        g.strokeStyle = k % 2 === 0 ? '#dde1e8' : '#f0f2f6';
        g.beginPath(); g.moveTo(ox, oy); g.lineTo(ox + R * Math.cos(a), oy - R * Math.sin(a)); g.stroke();
      }
    }

    // axes
    g.strokeStyle = '#8a92a3';
    g.lineWidth = 1.25;
    g.beginPath();
    if (oy >= 0 && oy <= H) { g.moveTo(0, Math.round(oy) + 0.5); g.lineTo(W, Math.round(oy) + 0.5); }
    if (ox >= 0 && ox <= W) { g.moveTo(Math.round(ox) + 0.5, 0); g.lineTo(Math.round(ox) + 0.5, H); }
    g.stroke();

    // axis names
    g.font = 'italic 13px Georgia, "Times New Roman", serif';
    g.fillStyle = '#6b7385';
    if (oy >= 14 && oy <= H - 4) { g.textAlign = 'right'; g.textBaseline = 'bottom'; haloText('Re', W - 56, oy - 4); }
    if (ox >= 4 && ox <= W - 30) { g.textAlign = 'left'; g.textBaseline = 'top'; haloText('Im', ox + 6, 8); }

    if (!s.numbers) return;
    g.font = '12px -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif';
    g.fillStyle = '#5d6577';
    const dec = Math.max(0, -Math.floor(Math.log10(major) + 1e-9));
    const fmtT = (v) => {
      let t = Math.abs(v) < major / 1e6 ? '0' : v.toFixed(dec);
      return t.replace('-', '−');
    };
    // real axis labels (stick to the edge if the axis is off screen)
    const ly = Math.min(Math.max(oy + 4, 4), H - 18);
    g.textAlign = 'center'; g.textBaseline = 'top';
    for (let k = Math.ceil(x0 / major); k * major <= x1; k++) {
      if (k === 0) continue;
      const X = toSX(k * major);
      if (X < 12 || X > W - 12) continue;
      haloText(fmtT(k * major), X, ly);
    }
    // imaginary axis labels
    const lx = Math.min(Math.max(ox - 6, 30), W - 6);
    g.textAlign = 'right'; g.textBaseline = 'middle';
    for (let k = Math.ceil(y0 / major); k * major <= y1; k++) {
      if (k === 0) continue;
      const Y = toSY(k * major);
      if (Y < 10 || Y > H - 10) continue;
      let t = fmtT(k * major);
      t = t === '1' ? 'i' : t === '−1' ? '−i' : t + 'i';
      haloText(t, lx, Y);
    }
    if (ox > 0 && ox < W && oy > 0 && oy < H) { g.textAlign = 'right'; g.textBaseline = 'top'; haloText('0', ox - 5, oy + 4); }
  }

  function haloText(t, x, y, haloColor = 'rgba(255,255,255,0.9)') {
    g.save();
    g.strokeStyle = haloColor; g.lineWidth = 3.5; g.lineJoin = 'round';
    g.strokeText(t, x, y);
    g.restore();
    g.fillText(t, x, y);
  }

  // ---------- raster layers (regions, domain colouring) ----------
  function rasterLayer(step, fillPixel) {
    const cols = Math.ceil(W / step), rows = Math.ceil(H / step);
    if (offCanvas.width !== cols || offCanvas.height !== rows) { offCanvas.width = cols; offCanvas.height = rows; }
    const img = offCtx.createImageData(cols, rows);
    const data = img.data;
    for (let j = 0; j < rows; j++) {
      const y = toWY((j + 0.5) * step);
      for (let i = 0; i < cols; i++) {
        fillPixel(toWX((i + 0.5) * step), y, data, (j * cols + i) * 4);
      }
    }
    offCtx.putImageData(img, 0, 0);
    g.save();
    g.imageSmoothingEnabled = step > 1;
    g.drawImage(offCanvas, 0, 0, cols * step, rows * step);
    g.restore();
  }

  function hexRgb(hex) {
    const n = parseInt(hex.slice(1), 16);
    return [(n >> 16) & 255, (n >> 8) & 255, n & 255];
  }

  function drawLocusFill(info, color, fast) {
    if (!info.hasFill) return;
    const [r, gg, b] = hexRgb(color);
    const { tree, atoms } = info;
    const inside = (sx, sy) => evalTree(tree, atoms, toWX(sx), toWY(sy), null, false);
    // Adaptive raster: test 6px blocks at corners + centre; only blocks on an edge are
    // resolved pixel by pixel, so edges are crisp at full resolution for little cost.
    const B = 6, px = fast ? 2 : 1;
    const cols = Math.ceil(W), rows = Math.ceil(H);
    if (offCanvas.width !== cols || offCanvas.height !== rows) { offCanvas.width = cols; offCanvas.height = rows; }
    const img = offCtx.createImageData(cols, rows);
    const d = img.data;
    const set = (x0, y0, x1, y1) => {
      for (let y = y0; y < y1; y++) for (let x = x0; x < x1; x++) {
        const o = (y * cols + x) * 4; d[o] = r; d[o + 1] = gg; d[o + 2] = b; d[o + 3] = 64;
      }
    };
    const nbx = Math.ceil(cols / B), nby = Math.ceil(rows / B);
    const corner = new Uint8Array((nbx + 1) * (nby + 1));
    for (let j = 0; j <= nby; j++) for (let i = 0; i <= nbx; i++) corner[j * (nbx + 1) + i] = inside(i * B, j * B) ? 1 : 0;
    for (let j = 0; j < nby; j++) {
      for (let i = 0; i < nbx; i++) {
        const c = corner[j * (nbx + 1) + i];
        const x0 = i * B, y0 = j * B, x1 = Math.min(cols, x0 + B), y1 = Math.min(rows, y0 + B);
        const same = c === corner[j * (nbx + 1) + i + 1] && c === corner[(j + 1) * (nbx + 1) + i] &&
          c === corner[(j + 1) * (nbx + 1) + i + 1] && c === (inside(x0 + B / 2, y0 + B / 2) ? 1 : 0);
        if (same) { if (c) set(x0, y0, x1, y1); continue; }
        for (let y = y0; y < y1; y += px) for (let x = x0; x < x1; x += px) {
          if (inside(x + px / 2, y + px / 2)) set(x, y, Math.min(x1, x + px), Math.min(y1, y + px));
        }
      }
    }
    offCtx.putImageData(img, 0, 0);
    g.save();
    g.imageSmoothingEnabled = true;
    g.drawImage(offCanvas, 0, 0, cols, rows);
    g.restore();
  }

  function drawDomain(info, fast) {
    const fn = info.fn;
    const env = { z: null, t: 0, loc: null };
    const rings = state.settings.rings;
    rasterLayer(fast ? 6 : 2, (x, y, d, o) => {
      env.z = { re: x, im: y };
      const v = fn(env);
      const m = Math.sqrt(v.re * v.re + v.im * v.im);
      if (!Number.isFinite(m)) { d[o] = d[o + 1] = d[o + 2] = 255; d[o + 3] = 255; return; }
      const h = ((Math.atan2(v.im, v.re) / TAU) + 1) % 1;
      // lightness: 0 at zeros, 0.5 where |f| = 1, -> 1 at poles
      let L = (2 / Math.PI) * Math.atan(Math.pow(m, 0.35));
      L = 0.12 + 0.76 * L;
      if (rings && m > 0) {
        const f = Math.log2(m) - Math.floor(Math.log2(m));
        L *= 0.86 + 0.14 * Math.pow(f, 0.6); // gentle ramps marking |f| = 2^k
      }
      hslInto(h, 0.82, L, d, o);
      d[o + 3] = 255;
    });
  }

  function hslInto(h, s, l, d, o) {
    const v = l + s * Math.min(l, 1 - l);
    const sv = v === 0 ? 0 : 2 * (1 - l / v);
    hsvInto(h, sv, v, d, o);
  }
  function hsvInto(h, s, v, d, o) {
    const i = Math.floor(h * 6), f = h * 6 - i;
    const p = v * (1 - s), q = v * (1 - f * s), t = v * (1 - (1 - f) * s);
    let r, gg, b;
    switch (i % 6) {
      case 0: r = v; gg = t; b = p; break; case 1: r = q; gg = v; b = p; break;
      case 2: r = p; gg = v; b = t; break; case 3: r = p; gg = q; b = v; break;
      case 4: r = t; gg = p; b = v; break; default: r = v; gg = p; b = q;
    }
    d[o] = r * 255; d[o + 1] = gg * 255; d[o + 2] = b * 255;
  }

  // ---------- contours (marching squares with root refinement) ----------
  // jumps: also keep sign changes that are jumps, not roots. An inequality's truth flips there
  // (e.g. arg(z) < π/4 along the negative real axis), so that is a real edge of the region.
  // levels > 0: also look inside same-sign cells near the curve on a finer quadtree, so two
  // branches closer together than one cell (the vertex of a wide parabola) are not lost.
  function contourLines(f, cell, jumps, levels = 0) {
    const nx = Math.ceil(W / cell) + 2, ny = Math.ceil(H / cell) + 2;
    const wx0 = toWX(-cell), wy0 = toWY(-cell), dw = cell / view.scale;
    const vals = new Float64Array(nx * ny);
    for (let j = 0; j < ny; j++) for (let i = 0; i < nx; i++) vals[j * nx + i] = f(wx0 + i * dw, wy0 - j * dw);
    const pts = new Map();
    const edgePt = (key, i1, j1, i2, j2) => {
      if (pts.has(key)) return pts.get(key);
      const fa = vals[j1 * nx + i1], fb = vals[j2 * nx + i2];
      const ax = wx0 + i1 * dw, ay = wy0 - j1 * dw, bx = wx0 + i2 * dw, by = wy0 - j2 * dw;
      let lo = 0, hi = 1, flo = fa, ok = true;
      for (let k = 0; k < 14; k++) {
        const m = (lo + hi) / 2;
        const fm = f(ax + (bx - ax) * m, ay + (by - ay) * m);
        if (fm !== fm) { ok = false; break; }
        if ((fm > 0) === (flo > 0)) { lo = m; flo = fm; } else hi = m;
      }
      let res = null;
      if (ok) {
        const m = (lo + hi) / 2;
        const fm = f(ax + (bx - ax) * m, ay + (by - ay) * m);
        // A real root has |f| tiny here; a jump (e.g. arg's branch cut) does not.
        if (jumps || Math.abs(fm) <= 0.02 * (Math.abs(fa) + Math.abs(fb)) + 1e-12) {
          res = [(i1 + (i2 - i1) * m - 1) * cell, (j1 + (j2 - j1) * m - 1) * cell];
        }
      }
      pts.set(key, res);
      return res;
    };
    const segA = [], segB = [];
    const addSeg = (k1, k2) => { if (pts.get(k1) && pts.get(k2)) { segA.push(k1); segB.push(k2); } };
    for (let j = 0; j < ny - 1; j++) {
      for (let i = 0; i < nx - 1; i++) {
        const v00 = vals[j * nx + i], v10 = vals[j * nx + i + 1], v01 = vals[(j + 1) * nx + i], v11 = vals[(j + 1) * nx + i + 1];
        if (v00 !== v00 || v10 !== v10 || v01 !== v01 || v11 !== v11) continue;
        const s00 = v00 > 0, s10 = v10 > 0, s01 = v01 > 0, s11 = v11 > 0;
        if (s00 === s10 && s10 === s01 && s01 === s11) continue;
        const e = [];
        if (s00 !== s10) { const k = (j * nx + i) * 2; edgePt(k, i, j, i + 1, j); e.push(k); } else e.push(-1);
        if (s10 !== s11) { const k = (j * nx + i + 1) * 2 + 1; edgePt(k, i + 1, j, i + 1, j + 1); e.push(k); } else e.push(-1);
        if (s01 !== s11) { const k = ((j + 1) * nx + i) * 2; edgePt(k, i, j + 1, i + 1, j + 1); e.push(k); } else e.push(-1);
        if (s00 !== s01) { const k = (j * nx + i) * 2 + 1; edgePt(k, i, j, i, j + 1); e.push(k); } else e.push(-1);
        const c = e.filter((k) => k >= 0);
        if (c.length === 2) addSeg(c[0], c[1]);
        else if (c.length === 4) {
          const fc = f(wx0 + (i + 0.5) * dw, wy0 - (j + 0.5) * dw);
          if ((fc > 0) === s00) { addSeg(e[0], e[1]); addSeg(e[2], e[3]); } else { addSeg(e[0], e[3]); addSeg(e[1], e[2]); }
        }
      }
    }
    if (levels > 0) {
      // Quadtree below the grid: level L has cells of cell / 2^L px. Values are cached on the finest grid.
      const FS = 1 << levels, fd = dw / FS, fnx = (nx - 1) * FS + 1;
      const fcache = new Map();
      const fvF = (FI, FJ) => {
        if (FI % FS === 0 && FJ % FS === 0) return vals[(FJ / FS) * nx + FI / FS];
        const key = FJ * fnx + FI;
        let v = fcache.get(key);
        if (v === undefined) { v = f(wx0 + FI * fd, wy0 - FJ * fd); fcache.set(key, v); }
        return v;
      };
      const fEdge = (key, I1, J1, I2, J2) => {
        if (pts.has(key)) return;
        const fa = fvF(I1, J1), fb = fvF(I2, J2);
        const ax = wx0 + I1 * fd, ay = wy0 - J1 * fd, bx = wx0 + I2 * fd, by = wy0 - J2 * fd;
        let lo = 0, hi = 1, flo = fa, ok = true;
        for (let k = 0; k < 12; k++) {
          const m = (lo + hi) / 2;
          const fm = f(ax + (bx - ax) * m, ay + (by - ay) * m);
          if (fm !== fm) { ok = false; break; }
          if ((fm > 0) === (flo > 0)) { lo = m; flo = fm; } else hi = m;
        }
        let res = null;
        if (ok) {
          const m = (lo + hi) / 2;
          const fm = f(ax + (bx - ax) * m, ay + (by - ay) * m);
          if (jumps || Math.abs(fm) <= 0.02 * (Math.abs(fa) + Math.abs(fb)) + 1e-12) {
            const fc = cell / FS;
            res = [(I1 + (I2 - I1) * m) * fc - cell, (J1 + (J2 - J1) * m) * fc - cell];
          }
        }
        pts.set(key, res);
      };
      let cellBudget = 30000;
      // A same-sign cell can only hide a zero if f bends enough to dip below its smallest |f|
      // (a straight f can't reach 0 between same-sign corners; a quadratic with second difference
      // `bend` per cell dips at most bend/8). `bend` shrinks 4× per level. Such cells are split,
      // down to `levels` times; 4·m < bend leaves a 2× margin.
      const subCell = (fi, fj, L, bend) => {
        if (cellBudget-- <= 0) return;
        const u = 1 << (levels - L), I = fi * u, J = fj * u;
        const w00 = fvF(I, J), w10 = fvF(I + u, J), w01 = fvF(I, J + u), w11 = fvF(I + u, J + u);
        if (w00 !== w00 || w10 !== w10 || w01 !== w01 || w11 !== w11) return;
        const t00 = w00 > 0, t10 = w10 > 0, t01 = w01 > 0, t11 = w11 > 0;
        if (t00 === t10 && t10 === t01 && t01 === t11) {
          const m = Math.min(Math.abs(w00), Math.abs(w10), Math.abs(w01), Math.abs(w11));
          const b2 = Math.max(bend, Math.abs(w00 - w10 - w01 + w11));
          if (L < levels && 4 * m < b2) for (let b = 0; b < 2; b++) for (let a = 0; a < 2; a++) subCell(fi * 2 + a, fj * 2 + b, L + 1, b2 / 4);
          return;
        }
        const K = (x, y, h) => 'f' + ((y * fnx + x) * 2 + h);
        const e = [];
        if (t00 !== t10) { const k = K(I, J, 0) + ':' + u; fEdge(k, I, J, I + u, J); e.push(k); } else e.push(null);
        if (t10 !== t11) { const k = K(I + u, J, 1) + ':' + u; fEdge(k, I + u, J, I + u, J + u); e.push(k); } else e.push(null);
        if (t01 !== t11) { const k = K(I, J + u, 0) + ':' + u; fEdge(k, I, J + u, I + u, J + u); e.push(k); } else e.push(null);
        if (t00 !== t01) { const k = K(I, J, 1) + ':' + u; fEdge(k, I, J, I, J + u); e.push(k); } else e.push(null);
        const c = e.filter((k) => k);
        if (c.length === 2) addSeg(c[0], c[1]);
        else if (c.length === 4) {
          const fcen = f(wx0 + (I + u / 2) * fd, wy0 - (J + u / 2) * fd);
          if ((fcen > 0) === t00) { addSeg(e[0], e[1]); addSeg(e[2], e[3]); } else { addSeg(e[0], e[3]); addSeg(e[1], e[2]); }
        }
      };
      // Largest second difference of f at each grid node (x and y directions).
      const b2 = new Float64Array(nx * ny);
      for (let j = 1; j < ny - 1; j++) {
        for (let i = 1, k = j * nx + 1; i < nx - 1; i++, k++) {
          const c = 2 * vals[k];
          b2[k] = Math.max(Math.abs(vals[k - 1] - c + vals[k + 1]), Math.abs(vals[k - nx] - c + vals[k + nx]));
        }
      }
      for (let j = 1; j < ny - 2; j++) {
        for (let i = 1, k = j * nx + 1; i < nx - 2; i++, k++) {
          const v00 = vals[k], v10 = vals[k + 1], v01 = vals[k + nx], v11 = vals[k + nx + 1];
          if (v00 > 0 ? !(v10 > 0 && v01 > 0 && v11 > 0) : !(v10 <= 0 && v01 <= 0 && v11 <= 0)) continue; // NaN fails too
          const m = Math.min(Math.abs(v00), Math.abs(v10), Math.abs(v01), Math.abs(v11));
          const bend = Math.max(Math.abs(v00 - v10 - v01 + v11), b2[k], b2[k + 1], b2[k + nx], b2[k + nx + 1]);
          if (!(4 * m < bend)) continue;
          for (let b = 0; b < 2; b++) for (let a = 0; a < 2; a++) subCell(i * 2 + a, j * 2 + b, 1, bend / 4);
        }
      }
    }
    // link segments into polylines
    const adj = new Map();
    const link = (k, s) => { const a = adj.get(k); if (a) a.push(s); else adj.set(k, [s]); };
    for (let s = 0; s < segA.length; s++) { link(segA[s], s); link(segB[s], s); }
    const used = new Uint8Array(segA.length);
    const lines = [];
    const walk = (s, key) => {
      const line = [pts.get(key)];
      while (s !== -1 && !used[s]) {
        used[s] = 1;
        const other = segA[s] === key ? segB[s] : segA[s];
        line.push(pts.get(other));
        key = other;
        s = -1;
        for (const t of adj.get(key)) if (!used[t]) { s = t; break; }
      }
      lines.push(line);
    };
    adj.forEach((list, key) => { if (list.length === 1 && !used[list[0]]) walk(list[0], key); });
    for (let s = 0; s < segA.length; s++) if (!used[s]) walk(s, segA[s]);
    return lines;
  }

  // Keep only the parts of polylines where keep(screenPt) is true, cutting exactly at the boundary.
  function clipLines(lines, keep) {
    const out = [];
    const cut = (p, q, pk) => {
      let lo = 0, hi = 1;
      for (let k = 0; k < 12; k++) {
        const m = (lo + hi) / 2;
        const pt = [p[0] + (q[0] - p[0]) * m, p[1] + (q[1] - p[1]) * m];
        if (keep(pt) === pk) lo = m; else hi = m;
      }
      const m = (lo + hi) / 2;
      return [p[0] + (q[0] - p[0]) * m, p[1] + (q[1] - p[1]) * m];
    };
    for (const line of lines) {
      let p = line[0], pk = keep(p), cur = pk ? [p] : null;
      for (let k = 1; k < line.length; k++) {
        const q = line[k], qk = keep(q);
        if (pk && qk) cur.push(q);
        else if (pk !== qk) {
          const m = cut(p, q, pk);
          if (pk) { cur.push(m); out.push(cur); cur = null; } else cur = [m, q];
        }
        p = q; pk = qk;
      }
      if (cur && cur.length > 1) out.push(cur);
    }
    return out;
  }

  let lineBoost = 1;
  let domainTimer = 0;
  function strokeLines(lines, color, width, dashed) {
    width *= lineBoost;
    g.save();
    g.strokeStyle = color; g.lineWidth = width; g.lineJoin = 'round'; g.lineCap = 'round';
    if (dashed) g.setLineDash([8, 6]);
    g.beginPath();
    for (const line of lines) {
      if (line.length < 2) continue;
      g.moveTo(line[0][0], line[0][1]);
      for (let k = 1; k < line.length; k++) g.lineTo(line[k][0], line[k][1]);
      // close loops neatly
      const a = line[0], b = line[line.length - 1];
      if (line.length > 3 && Math.abs(a[0] - b[0]) < 1e-6 && Math.abs(a[1] - b[1]) < 1e-6) g.closePath();
    }
    g.stroke();
    g.restore();
  }

  // Pull polylines onto the true curve: each segment's midpoint is projected onto f = 0 with
  // Newton steps and the segment split until it deviates by < 0.2px. Curves stay smooth at any zoom.
  function refineLines(lines, f) {
    const h = 0.02 / view.scale; // 0.02px, in world units
    const proj = (sx, sy) => {
      let x = toWX(sx), y = toWY(sy);
      for (let k = 0; k < 4; k++) {
        const v = f(x, y);
        if (v !== v) return null;
        const gx = (f(x + h, y) - v) / h, gy = (f(x, y + h) - v) / h;
        const g2 = gx * gx + gy * gy;
        if (!(g2 > 0) || !Number.isFinite(g2)) return null;
        x -= v * gx / g2; y -= v * gy / g2;
        if (Math.abs(v) * Math.sqrt(1 / g2) * view.scale < 0.02) break;
      }
      return [toSX(x), toSY(y)];
    };
    let budget = 60000;
    const split = (p, q, depth, out) => {
      const len = Math.hypot(q[0] - p[0], q[1] - p[1]);
      if (depth < 8 && len > 1.2 && budget-- > 0) {
        const mx = (p[0] + q[0]) / 2, my = (p[1] + q[1]) / 2;
        const m = proj(mx, my);
        if (m) {
          const d = Math.hypot(m[0] - mx, m[1] - my);
          if (d > 0.2 && d < 0.75 * len) {
            split(p, m, depth + 1, out);
            out.push(m);
            split(m, q, depth + 1, out);
            return;
          }
        }
      }
    };
    return lines.map((line) => {
      const out = [line[0]];
      for (let k = 1; k < line.length; k++) { split(line[k - 1], line[k], 0, out); out.push(line[k]); }
      return out;
    });
  }

  function drawLocusLines(info, color, fast) {
    if (info.empty) return;
    const cell = fast ? 6 : 3;
    const { atoms, tree } = info;
    const single = tree.type === 'atom';
    atoms.forEach((at, i) => {
      const f = (x, y) => atomVal(at, x, y);
      let lines = refineLines(contourLines(f, cell, at.op !== 'eq', fast ? 4 : 3), f);
      if (!single) {
        const keep = at.op === 'eq'
          ? (p) => evalTree(tree, atoms, toWX(p[0]), toWY(p[1]), { i, v: true }, false)
          : (p) => {
            const x = toWX(p[0]), y = toWY(p[1]);
            return evalTree(tree, atoms, x, y, { i, v: true }, false) !== evalTree(tree, atoms, x, y, { i, v: false }, false);
          };
        lines = clipLines(lines, keep);
      }
      const strict = at.op === 'lt' || at.op === 'gt';
      strokeLines(lines, color, at.op === 'eq' ? 2.75 : 2, strict);
    });
    if (info.extraSegment) {
      const [a, b] = info.extraSegment;
      strokeLines([[[toSX(a.re), toSY(a.im)], [toSX(b.re), toSY(b.im)]]], color, 2.75, false);
    }
  }

  // ---------- parametric curves ----------
  // Adaptive sampling in t: subdivide wherever the curve bends away from its chord by > 0.25px.
  function sampleParam(info, fast) {
    const env = { z: C(0, 0), t: 0, loc: null };
    const lim = 4 * (W + H);
    // Samples keep their true screen position even far off-screen, so that at high zoom an
    // interval whose ends are both outside the view can still be subdivided into the visible piece.
    const at = (t) => {
      env.t = t;
      const v = info.fn(env);
      const sx = toSX(v.re), sy = toSY(v.im);
      return Number.isFinite(sx) && Number.isFinite(sy) ? [sx, sy, t] : null;
    };
    const N = fast ? 240 : 600;
    const jump = (W + H) / 2;
    let budget = fast ? 8000 : 40000;
    const out = [];
    // Could the curve between these samples reach the view? (box of the three samples, grown by the chord)
    const near = (pa, pm, pb, len) => {
      const pad = len + 4;
      return Math.max(pa[0], pm[0], pb[0]) > -pad && Math.min(pa[0], pm[0], pb[0]) < W + pad
        && Math.max(pa[1], pm[1], pb[1]) > -pad && Math.min(pa[1], pm[1], pb[1]) < H + pad;
    };
    const sub = (ta, pa, tb, pb, depth) => {
      if (!pa || !pb || depth > 40 || budget-- <= 0) return;
      const tm = (ta + tb) / 2, pm = at(tm);
      if (!pm) return;
      const len = Math.hypot(pb[0] - pa[0], pb[1] - pa[1]);
      if (!near(pa, pm, pb, len)) return;
      const dev = Math.hypot(pm[0] - (pa[0] + pb[0]) / 2, pm[1] - (pa[1] + pb[1]) / 2);
      if (dev > 0.25 || len > 6) {
        sub(ta, pa, tm, pm, depth + 1);
        out.push(pm);
        sub(tm, pm, tb, pb, depth + 1);
      }
    };
    let prev = at(info.tmin);
    out.push(prev);
    for (let k = 1; k <= N; k++) {
      const t0 = info.tmin + (info.tmax - info.tmin) * (k - 1) / N;
      const t1 = info.tmin + (info.tmax - info.tmin) * k / N;
      const cur = at(t1);
      sub(t0, prev, t1, cur, 0);
      out.push(cur);
      prev = cur;
    }
    // Clip each segment to a box around the view (huge canvas coordinates draw badly), and
    // break where the curve is undefined or jumps across the screen (e.g. through a pole).
    const clip = (p, q) => {
      let u0 = 0, u1 = 1;
      const dx = q[0] - p[0], dy = q[1] - p[1];
      const edges = [[-dx, p[0] + lim], [dx, lim - p[0]], [-dy, p[1] + lim], [dy, lim - p[1]]];
      for (const [pp, qq] of edges) {
        if (pp === 0) { if (qq < 0) return null; continue; }
        const r = qq / pp;
        if (pp < 0) { if (r > u1) return null; if (r > u0) u0 = r; } else { if (r < u0) return null; if (r < u1) u1 = r; }
      }
      const P = (u) => [p[0] + u * dx, p[1] + u * dy, p[2] + u * (q[2] - p[2])];
      return [u0 === 0 ? p : P(u0), u1 === 1 ? q : P(u1)];
    };
    const lines = [];
    let line = [];
    const flush = () => { if (line.length > 1) lines.push(line); line = []; };
    for (let k = 1; k < out.length; k++) {
      const p = out[k - 1], q = out[k];
      const seg = p && q ? clip(p, q) : null;
      if (!seg || Math.hypot(seg[1][0] - seg[0][0], seg[1][1] - seg[0][1]) > jump) { flush(); continue; }
      const last = line[line.length - 1];
      if (!last || last[0] !== seg[0][0] || last[1] !== seg[0][1]) { flush(); line.push(seg[0]); }
      line.push(seg[1]);
    }
    flush();
    const f = out[0];
    return { lines, first: f && Math.abs(f[0]) < lim && Math.abs(f[1]) < lim ? f : null };
  }

  function drawParam(info, color, fast) {
    if (info.rangeErr || !(info.tmax > info.tmin) && !(info.tmax < info.tmin)) return;
    const { lines, first } = sampleParam(info, fast);
    strokeLines(lines, color, 2.75, false);
    // direction arrow at the middle value of t
    const tMid = (info.tmin + info.tmax) / 2;
    g.save();
    for (const line of lines) {
      const k = line.findIndex((q) => (info.tmax > info.tmin ? q[2] >= tMid : q[2] <= tMid));
      if (k > 0) {
        let j = k;
        while (j < line.length - 1 && Math.hypot(line[j][0] - line[k - 1][0], line[j][1] - line[k - 1][1]) < 6) j++;
        const a = line[k - 1], b = line[j];
        if (Math.hypot(b[0] - a[0], b[1] - a[1]) > 0.5) arrowHead(a[0], a[1], Math.atan2(b[1] - a[1], b[0] - a[0]), color, 10);
        break;
      }
    }
    if (first) { g.fillStyle = color; g.beginPath(); g.arc(first[0], first[1], 3.5, 0, TAU); g.fill(); }
    g.restore();
  }

  function arrowHead(x, y, ang, color, size) {
    g.save();
    g.translate(x, y); g.rotate(ang);
    g.fillStyle = color;
    g.beginPath(); g.moveTo(size * 0.6, 0); g.lineTo(-size * 0.6, size * 0.55); g.lineTo(-size * 0.6, -size * 0.55); g.closePath(); g.fill();
    g.restore();
  }

  // ---------- points ----------
  function drawDot(x, y, color, label, draggable, itemId, hollow) {
    const sx = toSX(x), sy = toSY(y);
    if (!Number.isFinite(sx) || !Number.isFinite(sy)) return;
    if (sx < -50 || sx > W + 50 || sy < -50 || sy > H + 50) return;
    if (state.settings.vectors && !hollow && (Math.abs(x) > 1e-12 || Math.abs(y) > 1e-12)) {
      const ox = toSX(0), oy = toSY(0);
      const ang = Math.atan2(sy - oy, sx - ox);
      const len = Math.hypot(sx - ox, sy - oy);
      if (len > 12) {
        g.save();
        g.strokeStyle = color; g.globalAlpha = 0.65; g.lineWidth = 1.75;
        g.beginPath(); g.moveTo(ox, oy); g.lineTo(sx - Math.cos(ang) * 7, sy - Math.sin(ang) * 7); g.stroke();
        arrowHead(sx - Math.cos(ang) * 9, sy - Math.sin(ang) * 9, ang, color, 9);
        g.restore();
      }
    }
    g.save();
    g.beginPath(); g.arc(sx, sy, draggable ? 6 : 5, 0, TAU);
    g.fillStyle = hollow ? '#fff' : color; g.fill();
    g.lineWidth = hollow ? 2.5 : 2; g.strokeStyle = hollow ? color : '#fff'; g.stroke();
    if (draggable) { g.beginPath(); g.arc(sx, sy, 10, 0, TAU); g.globalAlpha = 0.18; g.fillStyle = color; g.fill(); }
    g.restore();
    if (label && state.settings.labels) {
      g.font = '600 13px -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif';
      const w = g.measureText(label).width, h = 15;
      // try a few spots around the dot; skip the label if all of them collide
      const spots = [[9, -6 - h], [9, 6], [-9 - w, -6 - h], [-9 - w, 6]];
      for (const [dx, dy] of spots) {
        const box = [sx + dx, sy + dy, w, h];
        if (labelBoxes.some((b) => box[0] < b[0] + b[2] && b[0] < box[0] + box[2] && box[1] < b[1] + b[3] && b[1] < box[1] + box[3])) continue;
        labelBoxes.push(box);
        g.fillStyle = color;
        g.textAlign = 'left'; g.textBaseline = 'top';
        haloText(label, box[0], box[1] + 1);
        break;
      }
    }
    pointHits.push({ sx, sy, x, y, itemId, draggable, color, label });
  }

  function drawPointItem(info, it) {
    const v = info.value;
    const label = info.name ? M.plainName(info.name) : fmtComplex(v, 3);
    drawDot(v.re, v.im, it.color, label, info.draggable, it.id, false);
  }

  function solveRoots(gfn) {
    const env = { z: null, t: 0, loc: null };
    const G = (x, y) => { env.z = { re: x, im: y }; return gfn(env); };
    const x0 = toWX(0), x1 = toWX(W), y0 = toWY(H), y1 = toWY(0);
    const w = x1 - x0, h = y1 - y0;
    const roots = [];
    const NX = 16, NY = 12;
    for (let a = 0; a < NX; a++) {
      for (let b = 0; b < NY; b++) {
        let x = x0 - 0.1 * w + 1.2 * w * (a + 0.37) / NX, y = y0 - 0.1 * h + 1.2 * h * (b + 0.61) / NY;
        let v = G(x, y), ok = false, jn = 1;
        for (let k = 0; k < 80; k++) {
          if (!finite(v)) break;
          if (Math.abs(v.re) + Math.abs(v.im) < 1e-14) { ok = true; break; }
          const hh = 1e-7 * Math.max(1, Math.abs(x), Math.abs(y));
          const A = G(x + hh, y), B = G(x, y + hh);
          const j00 = (A.re - v.re) / hh, j01 = (B.re - v.re) / hh, j10 = (A.im - v.im) / hh, j11 = (B.im - v.im) / hh;
          const det = j00 * j11 - j01 * j10;
          if (!det || !Number.isFinite(det)) break;
          jn = Math.abs(j00) + Math.abs(j01) + Math.abs(j10) + Math.abs(j11);
          let dx = -(j11 * v.re - j01 * v.im) / det, dy = -(-j10 * v.re + j00 * v.im) / det;
          const st = Math.hypot(dx, dy), maxSt = 0.5 * (w + h);
          if (st > maxSt) { dx *= maxSt / st; dy *= maxSt / st; }
          x += dx; y += dy;
          v = G(x, y);
          if (st < 1e-15 * (1 + Math.abs(x) + Math.abs(y))) { ok = true; break; }
        }
        if (!finite(v)) continue;
        const res = Math.hypot(v.re, v.im);
        if (!(res < 1e-9 * (1 + jn * (1 + Math.hypot(x, y))))) continue;
        if (x < x0 - w || x > x1 + w || y < y0 - h || y > y1 + h) continue;
        const tol = Math.max(1e-6 * (1 + Math.hypot(x, y)), 0.5 / view.scale);
        if (roots.some((r) => Math.hypot(r.re - x, r.im - y) < tol)) continue;
        roots.push(C(Math.abs(x) < 1e-11 ? 0 : x, Math.abs(y) < 1e-11 ? 0 : y));
        if (roots.length >= 200) return roots;
      }
    }
    const ang = (p) => { const a = Cx.arg(p); return a !== a ? -1 : (a + TAU + 1e-9) % TAU; };
    roots.sort((p, q) => ang(p) - ang(q) || Cx.abs(p) - Cx.abs(q));
    return roots;
  }

  function drawRoots(info, it, fast) {
    const key = [view.cx, view.cy, view.scale, W, H, analysis.version].join(',');
    if (info.rootsKey !== key) {
      info.roots = solveRoots(info.g);
      info.rootsKey = key;
      queueStatusRefresh();
    }
    if (info.curves) {
      g.save(); g.globalAlpha *= 0.35;
      drawLocusLines(info.curves, it.color, fast);
      g.restore();
    }
    const many = info.roots.length > 12;
    for (const r of info.roots) drawDot(r.re, r.im, it.color, many ? null : fmtComplex(r, 3), false, it.id, false);
  }

  // Hollow circle marking an excluded end point (textbook convention).
  function drawOpenCircle(p, color) {
    const sx = toSX(p.re), sy = toSY(p.im);
    if (sx < -10 || sx > W + 10 || sy < -10 || sy > H + 10) return;
    g.save();
    g.beginPath(); g.arc(sx, sy, 4.5, 0, TAU);
    g.fillStyle = '#fff'; g.fill();
    g.lineWidth = 2.25; g.strokeStyle = color; g.stroke();
    g.restore();
  }

  function drawHoverRing(h) {
    g.save();
    g.beginPath(); g.arc(h.sx, h.sy, 12, 0, TAU);
    g.strokeStyle = h.color; g.lineWidth = 2; g.globalAlpha = 0.5; g.stroke();
    g.restore();
  }

  // ------------------------------------------------------------------ panel UI
  const listEl = $('#list');
  let focusedId = null;
  let editingTimer = 0;
  const panelEl = $('#panel');
  let hoverRowId = null;
  const highlightId = () => hoverRowId || focusedId;
  let lastFocusedInput = null;

  function rowEl(id) { return listEl.querySelector(`.row[data-id="${id}"]`); }
  function itemById(id) { return state.items.find((it) => it.id === id); }

  function buildList() {
    listEl.innerHTML = '';
    state.items.forEach((it) => listEl.appendChild(makeRow(it)));
    refreshAll();
  }

  function placeholderFor(it) {
    return state.items[0] === it ? 'Type here, e.g.  |z − 1| = 2  or  3 + 4i' : 'Add a number, locus or region…';
  }

  function makeRow(it) {
    const row = document.createElement('div');
    row.className = 'row';
    row.dataset.id = it.id;
    row.setAttribute('role', 'listitem');
    row.innerHTML = `
      <button class="swatch" title="Show / hide, or change colour" aria-label="Colour and visibility"></button>
      <div class="row-main">
        <div class="math-view math" tabindex="0" role="button" title="Click to edit"></div>
        <input class="expr" type="text" spellcheck="false" autocomplete="off" autocapitalize="off" autocorrect="off" aria-label="Expression">
        <div class="math-preview math" aria-hidden="true"></div>
        <div class="status" aria-live="polite"></div>
        <div class="extra"></div>
      </div>
      <button class="del" title="Delete line" aria-label="Delete line">×</button>`;
    const input = row.querySelector('.expr');
    input.value = it.text;
    input.placeholder = placeholderFor(it);
    input.addEventListener('input', () => onInput(it, input));
    input.addEventListener('keydown', (e) => onKey(e, it, input));
    input.addEventListener('focus', () => {
      focusedId = it.id; lastFocusedInput = input;
      clearTimeout(editingTimer);
      panelEl.classList.add('editing');
      requestRender(false);
      listEl.querySelectorAll('.row.focused').forEach((r) => r.classList.remove('focused'));
      row.classList.add('focused');
    });
    input.addEventListener('blur', () => {
      setTimeout(() => {
        if (document.activeElement !== input) {
          if (focusedId === it.id) { focusedId = null; requestRender(false); }
          clearTimeout(editingTimer);
          editingTimer = setTimeout(() => {
            if (!document.activeElement || !document.activeElement.classList.contains('expr')) panelEl.classList.remove('editing');
          }, 250);
          row.classList.remove('focused'); refreshStatus(it);
        }
      }, 0);
    });
    const mv = row.querySelector('.math-view');
    mv.addEventListener('mousedown', (e) => { e.preventDefault(); focusItem(it, true); });
    mv.addEventListener('focus', () => focusItem(it, true));
    row.addEventListener('mouseenter', () => { hoverRowId = it.id; requestRender(false); });
    row.addEventListener('mouseleave', () => { if (hoverRowId === it.id) { hoverRowId = null; requestRender(false); } });
    row.querySelector('.swatch').addEventListener('click', (e) => openSwatch(it, e.currentTarget));
    row.querySelector('.del').addEventListener('click', () => deleteItem(it, true));
    return row;
  }

  function autoReplace(input) {
    const v = input.value, pos = input.selectionStart;
    const marked = v.slice(0, pos) + '\u0001' + v.slice(pos);
    const rep = marked
      .replace(/<=/g, '≤').replace(/>=/g, '≥')
      .replace(/(^|[^A-Za-z])pi(?![A-Za-z])/g, '$1π')
      .replace(/(^|[^A-Za-z])theta(?![A-Za-z])/g, '$1θ');
    if (rep !== marked) {
      const p = rep.indexOf('\u0001');
      input.value = rep.replace('\u0001', '');
      input.setSelectionRange(p, p);
    }
  }

  function onInput(it, input) {
    autoReplace(input);
    it.text = input.value;
    it.lastEdit = Date.now();
    changed();
    ensureTrailingEmpty();
    setTimeout(() => refreshStatus(it), 900);
  }

  function changed(fast) {
    analyze();
    refreshAll();
    requestRender(!!fast);
    save();
  }

  function ensureTrailingEmpty() {
    const last = state.items[state.items.length - 1];
    if (!last || last.text.trim()) {
      const it = newItem('');
      state.items.push(it);
      listEl.appendChild(makeRow(it));
      analyze();
      refreshStatus(it);
    }
  }

  function onKey(e, it, input) {
    const idx = state.items.indexOf(it);
    if (e.key === 'Enter') {
      e.preventDefault();
      const nextIt = state.items[idx + 1];
      if (nextIt && !nextIt.text.trim()) { focusItem(nextIt); return; }
      const n = newItem('');
      state.items.splice(idx + 1, 0, n);
      const row = makeRow(n);
      rowEl(it.id).after(row);
      changed();
      focusItem(n);
    } else if (e.key === 'Backspace' && input.value === '' && state.items.length > 1 && idx > 0) {
      e.preventDefault();
      const prev = state.items[idx - 1];
      deleteItem(it, false);
      focusItem(prev, true);
    } else if (e.key === 'ArrowUp' && idx > 0) {
      e.preventDefault(); focusItem(state.items[idx - 1], true);
    } else if (e.key === 'ArrowDown' && idx < state.items.length - 1) {
      e.preventDefault(); focusItem(state.items[idx + 1], true);
    } else if (e.key === 'Escape') {
      input.blur();
    }
  }

  function focusItem(it, toEnd) {
    const row = rowEl(it.id);
    if (!row) return;
    const input = row.querySelector('.expr');
    row.classList.add('focused'); // reveals the text box (hidden behind the typeset view)
    input.focus();
    if (toEnd) { const n = input.value.length; input.setSelectionRange(n, n); }
  }

  function deleteItem(it, withUndo) {
    const idx = state.items.indexOf(it);
    if (idx < 0) return;
    const snap = snapshot();
    state.items.splice(idx, 1);
    stopPlaying(it);
    const row = rowEl(it.id);
    if (row) row.remove();
    if (!state.items.length) { state.items.push(newItem('')); buildList(); }
    ensureTrailingEmpty();
    changed();
    if (withUndo && it.text.trim()) toast('Line deleted', 'Undo', () => restore(snap));
  }

  // ---------- statuses ----------
  let statusQueued = false;
  function queueStatusRefresh() {
    if (statusQueued) return;
    statusQueued = true;
    setTimeout(() => { statusQueued = false; refreshAll(); }, 0);
  }

  function refreshAll() { state.items.forEach(refreshStatus); }

  function refreshStatus(it) {
    const row = rowEl(it.id);
    if (!row) return;
    const info = analysis.infos.get(it.id) || { kind: 'empty' };
    const sw = row.querySelector('.swatch');
    row.style.setProperty('--c', it.color);
    const drawable = ['point', 'locus', 'param', 'roots', 'domain'].includes(info.kind);
    sw.classList.toggle('off', it.hidden);
    sw.classList.toggle('none', !drawable && info.kind !== 'slider');
    row.querySelector('.expr').style.fontStyle = info.kind === 'note' ? 'italic' : '';

    // typeset maths (shown when the line isn't being edited)
    const text = it.text.trim();
    const key = it.text + '\u0000' + analysis.names.join(',') + '\u0000' + analysis.funcs.join(',');
    const mv = row.querySelector('.math-view'), pv = row.querySelector('.math-preview');
    if (mv._key !== key) {
      mv._key = key;
      const mh = text ? M.renderLine(text, analysis.names, analysis.funcs) : null;
      mv.innerHTML = mh || `<span class="mraw">${esc(text)}</span>`;
      mv.setAttribute('aria-label', text ? `${text} (press to edit)` : 'Empty line');
      // live preview while typing, when typesetting changes how it looks
      const worth = mh && /[\/^√_]|sqrt|conj|exp|°/.test(text);
      pv.innerHTML = worth ? mh : '';
      row.classList.toggle('has-preview', !!worth);
    }
    row.classList.toggle('has-math', !!text);
    fitMath(row.classList.contains('focused') ? pv : mv);

    const st = row.querySelector('.status');
    const editing = focusedId === it.id && (info.incomplete || Date.now() - it.lastEdit < 850);
    let html = '';
    st.classList.toggle('err', info.kind === 'error');
    if (info.kind === 'error') {
      if (!editing) {
        html = `<span class="kind">Check</span>${esc(info.msg)}`;
        if (info.undefinedName) {
          const n = esc(info.undefinedName);
          html += `<button class="fix" data-name="${n}" data-val="1">add slider ${n}</button><button class="fix" data-name="${n}" data-val="1 + i">add complex ${n}</button>`;
        }
      }
    } else {
      html = statusHTML(info, it);
    }
    if (st._html !== html) {
      st._html = html;
      st.innerHTML = html;
      st.querySelectorAll('.fix').forEach((fix) => fix.addEventListener('mousedown', (e) => {
        e.preventDefault(); addSliderFor(fix.dataset.name, it, fix.dataset.val);
      }));
    }
    refreshExtra(it, info, row);
  }

  // Shrink long typeset lines to fit the panel (down to a readable minimum); fade the edge if still too wide.
  function fitMath(el) {
    if (!el.offsetParent || !el.firstChild) return;
    const w = el.clientWidth - 16;
    el.style.fontSize = '';
    el.classList.remove('overflowing');
    if (w <= 0 || el.scrollWidth - 16 <= w) return;
    const base = parseFloat(getComputedStyle(el).fontSize);
    const content = el.scrollWidth - 16;
    el.style.fontSize = Math.max(13, Math.floor(base * w / content * 0.98)) + 'px';
    if (el.scrollWidth > el.clientWidth + 1) el.classList.add('overflowing');
  }
  function fitAllMath() {
    listEl.querySelectorAll('.row').forEach((row) => fitMath(row.classList.contains('focused') ? row.querySelector('.math-preview') : row.querySelector('.math-view')));
  }

  function statusHTML(info, it) {
    const k = (t) => `<span class="kind">${t}</span>`;
    const V = (t) => `<span class="val">${esc(t)}</span>`;
    const MV = (h) => `<span class="math sm">${h}</span>`;
    const SEP = '<span class="sep">·</span>';
    switch (info.kind) {
      case 'point': {
        const v = info.value;
        const grp = (h) => `<span class="grp">${SEP}${h}</span>`;
        const nmH = M.name(info.name || 'z');
        return k('Point') + MV(M.complex(v)) + (info.draggable ? '<span class="hint-sm">drag it on the graph</span>' : '') +
          '<span class="polar">' + MV(`<span class="abs"><span class="vh">|</span>${nmH}<span class="vh">|</span></span><span class="mrel">=</span>${M.realApprox(Cx.abs(v))}`) +
          '<span class="gap"></span>' +
          MV(`<span class="mf">arg</span><span class="thin"><span class="vh"> </span></span>${nmH}<span class="mrel">=</span>${M.angle(Cx.arg(v))}`) + '</span>';
      }
      case 'value': return k('Value') + MV(`${M.name(info.name)}<span class="mrel">=</span>${M.complex(info.value)}`) +
        (Math.abs(info.value.im) < 1e-12 && M.exactParts(info.value.re) ? `<span class="approx"> ≈ ${esc(fmtNum(info.value.re))}</span>` : '');
      case 'slider': return '';
      case 'func': return k('Function') + `use it like ${V(`|${info.name}(z)| = 1`)}`;
      case 'zdef': return k('Expression') + `depends on z – use it like ${V(`|${info.name}| = 1`)}`;
      case 'param': {
        if (info.rangeErr) return k('Curve') + '<span style="color:var(--error)">check the t range below</span>';
        return k('Curve') + `parametric curve, dot marks t = ${V(fmtNum(info.tmin))}`;
      }
      case 'locus': return k(esc(info.desc.kind)) + info.desc.text;
      case 'roots': {
        const n = info.roots.length;
        if (!info.rootsKey) return k('Solutions') + 'solving…';
        if (info.intersect) {
          if (!n) return k('Intersection') + 'the curves don\'t meet in view';
          return k(n === 1 ? '1 intersection' : `${n} intersections`) + info.roots.slice(0, 12).map((r) => MV(M.complexExact(r))).join(', ');
        }
        if (!n) return k('Solutions') + 'none found in view – try zooming out';
        const list = info.roots.slice(0, 12).map((r) => MV(M.complexExact(r))).join(', ');
        return k(n === 1 ? '1 solution' : `${n} solutions`) + list + (n > 12 ? ', …' : '') + (n > 1 ? ' <i>(in view)</i>' : '');
      }
      case 'hint': return k('Almost') + 'add <b>= 2</b> or <b>&lt; 2</b> (any value) to draw a locus or region';
      case 'domain': return k('Colouring') + 'colour = arg, brightness rings = modulus of the expression';
      case 'truth': return k(info.value ? 'True' : 'False') + (info.value ? 'this statement is true' : 'this statement is false');
      default: return '';
    }
  }

  // ---------- sliders (real, Re/Im, modulus/argument) and t-range ----------
  function sliderDefaults(v) {
    if (Math.abs(v) <= 10) return { min: Math.min(-10, Math.floor(v)), max: Math.max(10, Math.ceil(v)) };
    const m = niceStep(Math.abs(v)) * 2;
    return { min: -m * Math.ceil(Math.abs(v) / m) * 2, max: m * Math.ceil(Math.abs(v) / m) * 2 };
  }
  function sliderStep(s) { return niceStep((s.max - s.min) / 400); }
  function decimalsFor(step) { return Math.max(0, Math.ceil(-Math.log10(step) - 1e-9)); }

  const PARTS = {
    val: { label: '', aria: 'value', get: (info) => info.value },
    re: { label: 'Re', aria: 'real part', get: (info) => info.value.re },
    im: { label: 'Im', aria: 'imaginary part', get: (info) => info.value.im },
    mod: { label: '|·|', aria: 'modulus', get: (info) => Cx.abs(info.value) },
    arg: { label: 'arg', aria: 'argument', get: (info) => Cx.arg(info.value) || 0 },
  };
  function partsFor(info) {
    if (info.kind === 'slider') return ['val'];
    if (info.kind === 'point' && info.form === 'cart') return ['re', 'im'];
    if (info.kind === 'point' && info.form === 'polar') return ['mod', 'arg'];
    return null;
  }
  function rangeFor(it, part, info) {
    if (!it.ranges[part]) {
      const v = PARTS[part].get(info);
      it.ranges[part] = part === 'arg' ? { min: -Math.PI, max: Math.PI }
        : part === 'mod' ? { min: 0, max: Math.max(5, Math.ceil(2 * v)) }
        : sliderDefaults(v);
    }
    const r = it.ranges[part], v = PARTS[part].get(info);
    if (part !== 'arg') { if (v < r.min) r.min = v; if (v > r.max) r.max = v; }
    return r;
  }
  const stepFor = (it, part, info) => (part === 'arg' ? Math.PI / 180 : sliderStep(rangeFor(it, part, info)));

  // ---- writing numbers back into the text ----
  // Plain decimal text (never "1e-16", which would read as Euler's e). Float residue becomes 0.
  const exactish = (v) => {
    if (!Number.isFinite(v) || Math.abs(v) < 1e-9) return '0';
    let t = String(+v.toPrecision(10));
    if (/e/i.test(t)) t = v.toFixed(12).replace(/0+$/, '').replace(/\.$/, '');
    return t === '-0' ? '0' : t;
  };
  const fixed = (v, dec) => { let t = v.toFixed(dec); if (t.includes('.')) t = t.replace(/0+$/, '').replace(/\.$/, ''); return t === '-0' ? '0' : t; };
  // Always keeps the imaginary part, so a point never silently turns into a real slider.
  function cartText(re, im, reStr, imStr) {
    reStr = reStr || exactish(re); imStr = imStr || exactish(Math.abs(im));
    const neg = im < 0 && imStr !== '0';
    const iPart = (imStr === '1' ? '' : imStr) + 'i';
    if (reStr === '0' && imStr !== '0') return (neg ? '-' : '') + iPart;
    return `${reStr} ${neg ? '-' : '+'} ${iPart}`;
  }
  // θ as an exact multiple of π when possible: "πi/4", "-3πi/4", "37πi/180".
  function angleText(th) {
    if (Math.abs(th) < 1e-12) return '0i';
    for (let d = 1; d <= 360; d++) {
      const k = th / Math.PI * d, rk = Math.round(k);
      if (Math.abs(k - rk) < 1e-9 && rk !== 0) {
        const g = gcd(Math.abs(rk), d), n = rk / g, dd = d / g;
        const top = (n < 0 ? '-' : '') + (Math.abs(n) === 1 ? '' : Math.abs(n)) + 'πi';
        return dd === 1 ? top : `${top}/${dd}`;
      }
    }
    return precise(th, 1) + 'i';
  }
  function gcd(a, b) { while (b) [a, b] = [b, a % b]; return a; }
  function polarText(r, th, rStr) {
    rStr = rStr || exactish(r);
    const e = `e^(${angleText(th)})`;
    return rStr === '1' ? e : `${rStr}${e}`;
  }
  function writeRhs(it, info, rhs) {
    const txt = info.name ? `${info.name} = ${rhs}` : rhs;
    if (txt === it.text) return;
    it.text = txt;
    const row = rowEl(it.id);
    if (row) row.querySelector('.expr').value = txt;
    changed(true);
  }

  function setPart(it, part, v) {
    const info = analysis.infos.get(it.id);
    if (!info || !(partsFor(info) || []).includes(part)) return;
    const step = stepFor(it, part, info);
    v = Math.round(v / step) * step;
    const dec = decimalsFor(step);
    if (part === 'val') return writeRhs(it, info, fixed(v, dec));
    if (part === 're' || part === 'im') {
      const re = part === 're' ? v : info.value.re, im = part === 'im' ? v : info.value.im;
      const sc = Math.hypot(re, im);
      return writeRhs(it, info, cartText(re, im, part === 're' ? fixed(v, dec) : precise(re, sc), part === 'im' ? fixed(Math.abs(v), dec) : precise(Math.abs(im), sc)));
    }
    const r = part === 'mod' ? Math.max(0, v) : Cx.abs(info.value);
    const th = part === 'arg' ? v : (Cx.arg(info.value) || 0);
    writeRhs(it, info, polarText(r, th, part === 'mod' ? fixed(r, dec) : modText(r)));
  }

  // Precise decimal text for a form switch: 12 s.f., so the point doesn't move; never e-notation.
  const precise = (v, scale) => {
    const tol = 1e-11 * Math.max(1, scale);
    if (!Number.isFinite(v) || Math.abs(v) < tol) return '0';
    // Prefer the shortest decimal (up to 12 s.f.) that is within float residue of v.
    let t = String(+v.toPrecision(12));
    for (let p = 1; p < 12; p++) { const c = +v.toPrecision(p); if (Math.abs(c - v) < tol) { t = String(c); break; } }
    if (/e/i.test(t)) t = v.toFixed(14).replace(/0+$/, '').replace(/\.$/, '');
    return t === '-0' ? '0' : t;
  };
  // Modulus as written on paper: an integer, √k or n√k when it is one, else a precise decimal.
  function modText(r) {
    const e = M.exactParts(r);
    if (e && !e.pi && e.d === 1) return e.k === 1 ? String(e.n) : `${e.n === 1 ? '' : e.n}sqrt(${e.k})`;
    return precise(r, r);
  }
  function switchForm(it, form) {
    const info = analysis.infos.get(it.id);
    if (!info || info.kind !== 'point' || info.form === form) return;
    stopPlaying(it);
    const v = info.value, scale = Cx.abs(v);
    const rhsNow = info.name ? it.text.replace(/^[^=]*=\s*/, '') : it.text;
    const memo = it.formMemo;
    // Toggling back to a form we came from, with the point unmoved: restore the text the user had.
    if (memo && memo.form === form && Math.abs(memo.re - v.re) + Math.abs(memo.im - v.im) < 1e-9 * Math.max(1, scale)) {
      writeRhs(it, info, memo.rhs);
    } else if (form === 'polar') {
      writeRhs(it, info, polarText(scale, Cx.arg(v) || 0, modText(scale)));
    } else {
      const re = precise(v.re, scale), im = precise(v.im, scale);
      writeRhs(it, info, cartText(+re, +im, re, im.replace('-', '')));
    }
    it.formMemo = { form: info.form, rhs: rhsNow, re: v.re, im: v.im };
    changed();
  }

  function makeComplex(it) {
    const info = analysis.infos.get(it.id);
    if (!info || info.kind !== 'slider') return;
    stopPlaying(it);
    writeRhs(it, info, cartText(info.value, 0, exactish(info.value), '0'));
    changed();
  }

  const fmtPlain = (v) => String(+v.toPrecision(6)).replace('-', '−');
  const fmtLimit = (part, v) => (part === 'arg' && window.CX.piFraction(v)) || fmtPlain(v);

  function refreshExtra(it, info, row) {
    const ex = row.querySelector('.extra');
    const parts = partsFor(info);
    const sig = parts ? parts.join(',') + (info.kind === 'point' ? ':pt' : '') : info.kind === 'param' ? 'param' : '';
    if (ex.dataset.sig !== sig) {
      ex.dataset.sig = sig;
      ex.innerHTML = '';
      if (parts) buildSliders(it, ex, parts, info);
      if (sig === 'param') buildRange(it, ex);
    }
    if (parts) {
      for (const part of parts) {
        const rowP = ex.querySelector(`.slider-row[data-part="${part}"]`);
        const rg = rangeFor(it, part, info), v = PARTS[part].get(info);
        const r = rowP.querySelector('input[type=range]');
        r.min = rg.min; r.max = rg.max; r.step = 'any';
        if (document.activeElement !== r) r.value = v;
        const [lo, hi] = rowP.querySelectorAll('.lim');
        if (document.activeElement !== lo) lo.value = fmtLimit(part, rg.min);
        if (document.activeElement !== hi) hi.value = fmtLimit(part, rg.max);
        const pb = rowP.querySelector('.play');
        pb.classList.toggle('on', !!it.play[part]);
        pb.innerHTML = it.play[part] ? PAUSE_ICON : PLAY_ICON;
        pb.setAttribute('aria-label', (it.play[part] ? 'Pause ' : 'Animate ') + PARTS[part].aria);
      }
      const seg = ex.querySelector('.form-seg');
      if (seg) seg.querySelectorAll('button').forEach((b) => b.classList.toggle('on', b.dataset.form === info.form));
    }
    if (sig === 'param') {
      const [a, b] = ex.querySelectorAll('input');
      if (document.activeElement !== a) a.value = it.tmin;
      if (document.activeElement !== b) b.value = it.tmax;
      a.classList.toggle('bad', info.rangeErr === 'min' || info.rangeErr === 'both');
      b.classList.toggle('bad', info.rangeErr === 'max' || info.rangeErr === 'both');
    }
  }

  const PLAY_ICON = '<svg viewBox="0 0 12 12" aria-hidden="true"><path d="M3 1.8v8.4L10 6z"/></svg>';
  const PAUSE_ICON = '<svg viewBox="0 0 12 12" aria-hidden="true"><path d="M2.6 1.8h2.4v8.4H2.6zM7 1.8h2.4v8.4H7z"/></svg>';

  function buildSliders(it, ex, parts, info) {
    const nm = info.name ? M.plainName(info.name) : 'z';
    let html = '';
    if (info.kind === 'point') {
      html += `<div class="form-row"><span class="form-label">Sliders for</span><div class="form-seg" role="group" aria-label="Number form">
        <button data-form="cart" title="Real and imaginary parts">x + yi</button>
        <button data-form="polar" title="Modulus and argument">r e<sup>iθ</sup></button></div></div>`;
    }
    for (const part of parts) {
      const lab = part === 'mod' ? `|${esc(nm)}|` : PARTS[part].label;
      html += `<div class="slider-row" data-part="${part}">
        ${lab ? `<span class="part-label" aria-hidden="true">${lab}</span>` : ''}
        <button class="play">${PLAY_ICON}</button>
        <div class="track">
          <input type="range" aria-label="${esc(PARTS[part].aria)} of ${esc(nm)}">
          <input class="lim lo" title="Minimum (click to change)" aria-label="Minimum ${PARTS[part].aria} of ${esc(nm)}">
          <input class="lim hi" title="Maximum (click to change)" aria-label="Maximum ${PARTS[part].aria} of ${esc(nm)}">
        </div>
        ${part === 'val' ? '<button class="to-complex" title="Give it an imaginary part (two sliders: Re and Im)">+ i</button>' : ''}
      </div>`;
    }
    ex.innerHTML = html;
    ex.querySelectorAll('.form-seg button').forEach((b) => b.addEventListener('click', () => switchForm(it, b.dataset.form)));
    const tc = ex.querySelector('.to-complex');
    if (tc) tc.addEventListener('click', () => makeComplex(it));
    for (const part of parts) {
      const rowP = ex.querySelector(`.slider-row[data-part="${part}"]`);
      const r = rowP.querySelector('input[type=range]');
      r.addEventListener('input', () => { it.anim[part] = undefined; setPart(it, part, parseFloat(r.value)); });
      r.addEventListener('change', () => requestRender(false));
      const [lo, hi] = rowP.querySelectorAll('.lim');
      const lim = (el, key) => el.addEventListener('change', () => {
        const rg = it.ranges[part];
        try {
          const v = evalRange(el.value, analysis.ctx);
          rg[key] = v;
          if (rg.min >= rg.max) rg[key === 'min' ? 'max' : 'min'] = v + (key === 'min' ? 1 : -1);
          changed();
        } catch (e) { el.value = fmtLimit(part, rg[key]); }
      });
      lim(lo, 'min'); lim(hi, 'max');
      rowP.querySelector('.play').addEventListener('click', () => {
        it.play[part] = it.play[part] ? 0 : 1;
        it.anim[part] = undefined;
        if (it.play[part]) startAnimation();
        refreshStatus(it);
      });
    }
  }

  let animating = false, lastT = 0;
  function startAnimation() {
    if (animating) return;
    animating = true; lastT = performance.now();
    requestAnimationFrame(tick);
  }
  function tick(now) {
    const dt = Math.min(0.1, (now - lastT) / 1000); lastT = now;
    let any = false;
    for (const it of state.items) {
      for (const part of Object.keys(it.play)) {
        if (!it.play[part]) continue;
        const info = analysis.infos.get(it.id);
        if (!info || !(partsFor(info) || []).includes(part)) { it.play[part] = 0; continue; }
        any = true;
        const rg = rangeFor(it, part, info), span = rg.max - rg.min;
        let v = (it.anim[part] !== undefined ? it.anim[part] : PARTS[part].get(info)) + it.play[part] * span / 6 * dt;
        if (part === 'arg' && rg.min <= -Math.PI + 1e-9 && rg.max >= Math.PI - 1e-9) {
          if (v > Math.PI) v -= TAU; // the argument goes round and round
        } else {
          if (v >= rg.max) { v = rg.max; it.play[part] = -1; }
          if (v <= rg.min) { v = rg.min; it.play[part] = 1; }
        }
        it.anim[part] = v;
        setPart(it, part, v);
      }
    }
    if (!any) { animating = false; requestRender(false); state.items.forEach((it) => refreshStatus(it)); return; }
    requestAnimationFrame(tick);
  }
  function stopPlaying(it) { it.play = {}; it.anim = {}; }

  function buildRange(it, ex) {
    ex.innerHTML = `<div class="range-row">t from <input aria-label="t minimum"> to <input aria-label="t maximum"></div>`;
    const [a, b] = ex.querySelectorAll('input');
    const on = (el, key) => el.addEventListener('input', () => {
      autoReplace(el);
      it[key] = el.value; changed();
    });
    on(a, 'tmin'); on(b, 'tmax');
  }

  function addSliderFor(name, beforeIt, val = '1') {
    const idx = state.items.indexOf(beforeIt);
    const n = newItem(`${name} = ${val}`);
    state.items.splice(Math.max(0, idx), 0, n);
    buildList();
    changed();
  }

  // ---------- swatch popover ----------
  const pop = $('#swatchPop');
  function openSwatch(it, anchor) {
    const r = anchor.getBoundingClientRect();
    const eye = it.hidden
      ? '<svg viewBox="0 0 20 20" aria-hidden="true"><path d="M1.5 10S5 4 10 4s8.5 6 8.5 6-3.5 6-8.5 6-8.5-6-8.5-6Z"/><circle cx="10" cy="10" r="2.6"/></svg>'
      : '<svg viewBox="0 0 20 20" aria-hidden="true"><path d="M1.5 10S5 4 10 4s8.5 6 8.5 6-3.5 6-8.5 6-8.5-6-8.5-6Z"/><circle cx="10" cy="10" r="2.6"/><path d="M3 17 17 3"/></svg>';
    pop.innerHTML = `<button class="pop-btn" data-act="toggle">${eye}${it.hidden ? 'Show on graph' : 'Hide from graph'}</button>
      <div class="chips">${PALETTE.map((c) => `<button class="chip${c === it.color ? ' on' : ''}" style="background:${c}" data-c="${c}" aria-label="colour ${c}"></button>`).join('')}</div>`;
    pop.hidden = false;
    pop.style.left = Math.min(r.left, window.innerWidth - 210) + 'px';
    pop.style.top = Math.min(r.bottom + 6, window.innerHeight - pop.offsetHeight - 8) + 'px';
    pop.onclick = (e) => {
      const b = e.target.closest('button');
      if (!b) return;
      if (b.dataset.act === 'toggle') it.hidden = !it.hidden;
      if (b.dataset.c) { it.color = b.dataset.c; if (it.hidden) it.hidden = false; }
      pop.hidden = true;
      refreshStatus(it);
      requestRender(false); save();
    };
  }
  document.addEventListener('mousedown', (e) => {
    if (!pop.hidden && !pop.contains(e.target) && !e.target.classList.contains('swatch')) pop.hidden = true;
    document.querySelectorAll('.dropdown').forEach((d) => {
      if (!d.hidden && !d.parentElement.contains(e.target)) d.hidden = true;
    });
  });

  // ---------- keypad ----------
  const KEYS = [
    ['z', 'z'], ['i', 'i'], ['π', 'π'], ['t', 't'], ['|□|', '|', '|'], ['arg', 'arg(', ')'], ['Re', 'Re(', ')'], ['Im', 'Im(', ')'],
    ['conj', 'conj(', ')'], ['√', 'sqrt(', ')'], ['eˣ', 'e^(', ')'], ['xʸ', '^'], ['≤', ' ≤ '], ['≥', ' ≥ '], ['°', '°'], ['and', ' and '],
  ];
  function buildKeypad() {
    const kp = $('#keypad');
    KEYS.forEach(([label, before, after = '']) => {
      const b = document.createElement('button');
      b.textContent = label;
      b.title = `Insert ${before}${after}`;
      const spoken = { '|□|': 'modulus bars', 'eˣ': 'e to the power', 'xʸ': 'power', '√': 'square root', '°': 'degrees' }[label];
      b.setAttribute('aria-label', 'Insert ' + (spoken || label));
      b.addEventListener('mousedown', (e) => e.preventDefault()); // keep focus in the input
      b.addEventListener('pointerdown', (e) => e.preventDefault());
      b.addEventListener('click', () => insertText(before, after));
      kp.appendChild(b);
    });
  }
  function insertText(before, after) {
    let input = document.activeElement && document.activeElement.classList.contains('expr') ? document.activeElement : lastFocusedInput;
    if (!input || !document.body.contains(input)) {
      const last = state.items[state.items.length - 1];
      input = rowEl(last.id).querySelector('.expr');
    }
    input.focus();
    const s = input.selectionStart ?? input.value.length, e = input.selectionEnd ?? s;
    const sel = input.value.slice(s, e);
    input.value = input.value.slice(0, s) + before + sel + after + input.value.slice(e);
    const p = s + before.length + sel.length;
    input.setSelectionRange(p, p);
    input.dispatchEvent(new Event('input'));
  }

  // ------------------------------------------------------------------ canvas interaction
  const readout = $('#readout');
  const hint = $('#hint');
  const pointers = new Map();
  let mode = null; // {type:'pan'|'drag'|'pinch', ...}
  let hoverPt = null;

  function evtPos(e) { const r = canvas.getBoundingClientRect(); return [e.clientX - r.left, e.clientY - r.top]; }
  function hitTest(x, y) {
    let best = null, bd = 14;
    for (const h of pointHits) {
      const d = Math.hypot(h.sx - x, h.sy - y);
      if (d < bd || (best && d <= bd && h.draggable && !best.draggable)) { bd = d; best = h; }
    }
    return best;
  }

  canvas.addEventListener('keydown', (e) => {
    const stepPx = e.shiftKey ? 200 : 60;
    const pan = { ArrowLeft: [-1, 0], ArrowRight: [1, 0], ArrowUp: [0, 1], ArrowDown: [0, -1] }[e.key];
    if (pan) { view.cx += pan[0] * stepPx / view.scale; view.cy += pan[1] * stepPx / view.scale; requestRender(true); saveSoon(); }
    else if (e.key === '+' || e.key === '=') zoomAt(W / 2, H / 2, 1.4, false);
    else if (e.key === '-' || e.key === '_') zoomAt(W / 2, H / 2, 1 / 1.4, false);
    else if (e.key === '0') { homeView(); requestRender(false); saveSoon(); }
    else return;
    e.preventDefault();
    hideHint();
  });

  canvas.addEventListener('pointerdown', (e) => {
    canvas.setPointerCapture(e.pointerId);
    const [x, y] = evtPos(e);
    pointers.set(e.pointerId, { x, y });
    hideHint();
    if (pointers.size === 1) {
      const h = hitTest(x, y);
      if (h && h.draggable) {
        mode = { type: 'drag', itemId: h.itemId, dx: h.sx - x, dy: h.sy - y, snap: snapshot() };
      } else {
        mode = { type: 'pan', sx: x, sy: y, cx: view.cx, cy: view.cy };
        canvas.classList.add('panning');
      }
    } else if (pointers.size === 2) {
      const [a, b] = [...pointers.values()];
      const mx = (a.x + b.x) / 2, my = (a.y + b.y) / 2;
      mode = { type: 'pinch', d0: Math.hypot(a.x - b.x, a.y - b.y), s0: view.scale, wx: toWX(mx), wy: toWY(my) };
    }
  });

  canvas.addEventListener('pointermove', (e) => {
    const [x, y] = evtPos(e);
    if (pointers.has(e.pointerId)) pointers.set(e.pointerId, { x, y });
    if (mode && mode.type === 'pan') {
      view.cx = mode.cx - (x - mode.sx) / view.scale;
      view.cy = mode.cy + (y - mode.sy) / view.scale;
      requestRender(true);
    } else if (mode && mode.type === 'drag') {
      dragTo(mode.itemId, x + mode.dx, y + mode.dy);
    } else if (mode && mode.type === 'pinch' && pointers.size >= 2) {
      const [a, b] = [...pointers.values()];
      const d = Math.hypot(a.x - b.x, a.y - b.y);
      const mx = (a.x + b.x) / 2, my = (a.y + b.y) / 2;
      view.scale = clampScale(mode.s0 * d / Math.max(1, mode.d0));
      view.cx = mode.wx - (mx - W / 2) / view.scale;
      view.cy = mode.wy + (my - H / 2) / view.scale;
      requestRender(true);
    }
    updateHover(x, y);
  });

  const endPointer = (e) => {
    pointers.delete(e.pointerId);
    if (mode && mode.type === 'drag') {
      const it = itemById(mode.itemId);
      if (it) save();
    }
    if (pointers.size === 0) { mode = null; canvas.classList.remove('panning'); requestRender(false); save(); }
    else if (pointers.size === 1 && mode && mode.type === 'pinch') {
      const [p] = [...pointers.values()];
      mode = { type: 'pan', sx: p.x, sy: p.y, cx: view.cx, cy: view.cy };
    }
  };
  canvas.addEventListener('pointerup', endPointer);
  canvas.addEventListener('pointercancel', endPointer);
  canvas.addEventListener('pointerleave', () => { if (!mode) { readout.hidden = true; if (hoverPt) { hoverPt = null; requestRender(false); } } });

  canvas.addEventListener('wheel', (e) => {
    e.preventDefault();
    hideHint();
    const [x, y] = evtPos(e);
    let dy = e.deltaY * (e.deltaMode === 1 ? 30 : e.deltaMode === 2 ? 300 : 1);
    const factor = Math.exp(-dy * (e.ctrlKey ? 0.01 : 0.0018));
    zoomAt(x, y, factor, true);
    updateHover(x, y); // the world point under the cursor changed, so the readout must too
  }, { passive: false });

  // Safari sends trackpad pinches as gesture events, not ctrl+wheel. Without this the whole
  // page zooms (blurry, jumping layout) instead of the graph.
  let gestureScale = 1;
  canvas.addEventListener('gesturestart', (e) => { e.preventDefault(); gestureScale = 1; });
  canvas.addEventListener('gesturechange', (e) => {
    e.preventDefault();
    const [x, y] = evtPos(e);
    zoomAt(x, y, e.scale / gestureScale, true);
    gestureScale = e.scale;
    updateHover(x, y);
  });
  canvas.addEventListener('gestureend', (e) => { e.preventDefault(); requestRender(false); });

  canvas.addEventListener('dblclick', (e) => {
    const [x, y] = evtPos(e);
    if (hitTest(x, y)) return;
    addPointAt(toWX(x), toWY(y));
  });

  function clampScale(s) { return Math.min(5e6, Math.max(0.05, s)); }
  function zoomAt(x, y, factor, fast) {
    const wx = toWX(x), wy = toWY(y);
    view.scale = clampScale(view.scale * factor);
    view.cx = wx - (x - W / 2) / view.scale;
    view.cy = wy + (y - H / 2) / view.scale;
    requestRender(fast);
    saveSoon();
  }

  function snapStep() { return niceStep(85 / view.scale) / 10; }
  function snapped(x, y) {
    const s = snapStep(), dec = decimalsFor(s);
    return [Math.round(x / s) * s, Math.round(y / s) * s, dec];
  }

  function dragTo(itemId, sx, sy) {
    const it = itemById(itemId);
    const info = analysis.infos.get(itemId);
    if (!it || !info) return;
    stopPlaying(it);
    const wx = toWX(sx), wy = toWY(sy);
    if (info.form === 'polar') {
      const s = snapStep(), dec = decimalsFor(s);
      const r = Math.round(Math.hypot(wx, wy) / s) * s;
      const th = Math.round(Math.atan2(wy, wx) / (Math.PI / 180)) * Math.PI / 180;
      writeRhs(it, info, polarText(r, th, fixed(r, dec)));
    } else {
      const [x, y, dec] = snapped(wx, wy);
      writeRhs(it, info, cartText(x, y, fixed(x, dec), fixed(Math.abs(y), dec)));
    }
  }

  function addPointAt(wx, wy) {
    const [x, y, dec] = snapped(wx, wy);
    const used = new Set(Object.keys(analysis.ctx.defs));
    let name = null;
    for (const c of 'abcdefghjklmnpqrsuvw') if (!used.has(c)) { name = c; break; }
    if (!name) for (let k = 1; ; k++) if (!used.has('p' + k)) { name = 'p' + k; break; }
    const txt = `${name} = ${cartText(x, y, fixed(x, dec), fixed(Math.abs(y), dec))}`;
    const last = state.items[state.items.length - 1];
    if (last && !last.text.trim()) { last.text = txt; } else state.items.push(newItem(txt));
    buildList();
    changed();
    ensureTrailingEmpty();
    toast(`Added point ${name} – drag it to move`);
  }

  function updateHover(x, y) {
    const h = hitTest(x, y);
    canvas.classList.toggle('can-drag', !!(h && h.draggable) && !(mode && mode.type === 'pan'));
    const prev = hoverPt;
    hoverPt = h && (!mode || mode.type === 'drag') ? h : null;
    if ((prev && prev.itemId) !== (hoverPt && hoverPt.itemId) || (prev && hoverPt && (prev.sx !== hoverPt.sx || prev.sy !== hoverPt.sy))) requestRender(!!mode);
    let wx, wy, label;
    if (hoverPt) { wx = hoverPt.x; wy = hoverPt.y; label = hoverPt.label && !/[0-9]/.test(hoverPt.label[0]) ? hoverPt.label : null; }
    else { wx = toWX(x); wy = toWY(y); }
    const dec = Math.max(0, Math.min(10, Math.ceil(Math.log10(view.scale)) + (hoverPt ? 2 : 0)));
    const fx = (v) => {
      let s = hoverPt ? fmtNum(v, 6) : (Math.abs(v) < 0.5 * Math.pow(10, -dec) ? '0' : v.toFixed(dec).replace('-', '−'));
      return s;
    };
    const im = wy;
    const zs = `${fx(wx)} ${im < 0 ? '−' : '+'} ${fx(Math.abs(im))}i`;
    const z = C(wx, wy);
    readout.innerHTML = `<b>${label ? esc(label) : 'z'}</b> = ${esc(zs)} &nbsp; |z| = ${esc(fmtNum(Cx.abs(z)))} &nbsp; arg = ${esc(fmtAngle(Cx.arg(z)))}`;
    readout.hidden = false;
  }

  function hideHint() {
    if (hint.style.opacity === '0') return;
    hint.style.opacity = '0';
  }

  $('#zoomIn').addEventListener('click', () => zoomAt(W / 2, H / 2, 1.5, false));
  $('#zoomOut').addEventListener('click', () => zoomAt(W / 2, H / 2, 1 / 1.5, false));
  $('#zoomHome').addEventListener('click', () => { homeView(); requestRender(false); saveSoon(); });

  // ------------------------------------------------------------------ menus, help, share, export
  const EXAMPLES = [
    { title: 'Points & arithmetic', items: ['a = 2 + i', 'b = -1 + 2i', 'a + b', 'a b', 'conj(a)'], vectors: true },
    { title: 'Circle', items: ['c = 1 + i', 'r = 2', '|z - c| = r'] },
    { title: 'Perpendicular bisector', items: ['p = 2', 'q = 2i', '|z - p| = |z - q|'] },
    { title: 'Half-lines with arg', items: ['arg(z - 1) = π/4', 'arg(z + 1) = 3π/4', 'arg(z) = -π/2'] },
    { title: 'Sector region', items: ['|z| ≤ 3 and 0 ≤ arg(z) ≤ π/3'] },
    { title: 'Annulus region', items: ['1 < |z - i| ≤ 2'] },
    { title: 'Closer to one point', items: ['|z - 2| < |z + 1 - i|'] },
    { title: 'Ellipse', items: ['|z - 2| + |z + 2| = 6'] },
    { title: 'Arc from arg', items: ['arg(z - 2) - arg(z + 2) = π/4'] },
    { title: 'Semicircle', items: ['|z| = 2 and Re(z) ≥ 0'] },
    { title: 'Roots of unity', items: ['z^6 = 1', '|z| = 1'], halfWidth: 2.2 },
    { title: 'Solving a quadratic', items: ['z^2 - 2z + 5 = 0'] },
    { title: 'Where two loci meet', items: ['|z - 1| = 2', 'arg(z) = π/4', '|z - 1| = 2 and arg(z) = π/4'] },
    { title: 'Complex sliders (Re/Im and r, θ)', items: ['c = 1 + i', 'w = 2e^(πi/4)', '|z - c| = |w|', 'arg(z - c) = arg(w)'] },
    { title: 'Apollonius circle (animate k)', items: [{ text: 'k = 2', slider: { min: 0.2, max: 4 } }, '|z - 1| = k|z + 1|'] },
    { title: 'Parametric spiral', items: [{ text: 'z = e^((0.15 + i)t)', tmin: '0', tmax: '6π' }] },
    { title: 'Function & its locus', items: ['f(z) = z^2 + 1', '|f(z)| = 2', '|f(z)| < 1'] },
    { title: 'Domain colouring', items: ['(z^2 - 1)/(z^2 + 1)'], halfWidth: 2.5 },
    { title: 'Cartesian (x = Re z, y = Im z)', items: ['y = x^2 - 2', 'x^2 + y^2 = 9'] },
  ];

  function buildExamples() {
    const menu = $('#examplesMenu');
    EXAMPLES.forEach((ex) => {
      const b = document.createElement('button');
      b.className = 'ex';
      const preview = ex.items.map((x) => typeof x === 'string' ? x : x.text).join('   ');
      b.innerHTML = `<b>${esc(ex.title)}</b><span>${esc(preview)}</span>`;
      b.addEventListener('click', () => { menu.hidden = true; loadExample(ex); });
      menu.appendChild(b);
    });
  }

  function loadExample(ex) {
    const snap = snapshot();
    state.items.forEach(stopPlaying);
    state.colorIdx = 0;
    state.items = ex.items.map((x) => typeof x === 'string' ? newItem(x) : newItem(x.text, Object.assign({}, x)));

    state.settings.vectors = !!ex.vectors; syncSettingsUI();
    homeHalfWidth = ex.halfWidth || 0;
    if (W > 0) homeView(); else pendingHome = true;
    buildList();
    ensureTrailingEmpty();
    changed();
    toast(`Loaded “${ex.title}”`, 'Undo', () => restore(snap));
  }

  const toggleMenu = (btn, menu) => $(btn).addEventListener('click', () => {
    const open = $(menu).hidden;
    document.querySelectorAll('.dropdown').forEach((d) => { d.hidden = true; });
    $(menu).hidden = !open;
  });
  toggleMenu('#examplesBtn', '#examplesMenu');
  toggleMenu('#settingsBtn', '#settingsMenu');

  function syncSettingsUI() {
    const s = state.settings;
    document.querySelectorAll('#gridSeg button').forEach((b) => b.classList.toggle('on', b.dataset.grid === s.grid));
    $('#optNumbers').checked = s.numbers;
    $('#optVectors').checked = s.vectors;
    $('#optLabels').checked = s.labels;
    $('#optRings').checked = s.rings;
  }
  document.querySelectorAll('#gridSeg button').forEach((b) => b.addEventListener('click', () => {
    state.settings.grid = b.dataset.grid; syncSettingsUI(); requestRender(false); save();
  }));
  [['#optNumbers', 'numbers'], ['#optVectors', 'vectors'], ['#optLabels', 'labels'], ['#optRings', 'rings']].forEach(([id, key]) => {
    $(id).addEventListener('change', (e) => { state.settings[key] = e.target.checked; requestRender(false); save(); });
  });

  // Inside claude.ai (a sandboxed frame) downloads and #g= links don't work, so offer alternatives.
  const FRAMED = (() => { try { return window.self !== window.top; } catch (e) { return true; } })();

  // In a claude.ai artifact, real downloads go through the platform's confirmed save.
  let downloadsApi = null;
  try {
    if (window.claude && typeof window.claude.use === 'function') {
      window.claude.use('downloads').then((d) => { downloadsApi = d; }).catch(() => {});
    }
  } catch (e) { /* not in claude.ai */ }

  const helpModal = $('#helpModal'), shareModal = $('#shareModal'), imageModal = $('#imageModal');
  let modalReturn = null, openModalEl = null;
  function openModal(el, focusEl) {
    if (openModalEl) closeModal(false);
    modalReturn = document.activeElement;
    el.hidden = false;
    openModalEl = el;
    (focusEl || el.querySelector('.modal-close')).focus();
  }
  function closeModal(restoreFocus = true) {
    const el = openModalEl;
    if (!el) return;
    el.hidden = true;
    openModalEl = null;
    if (restoreFocus && modalReturn && document.body.contains(modalReturn)) modalReturn.focus();
  }
  document.querySelectorAll('.modal-backdrop').forEach((el) => {
    el.addEventListener('mousedown', (e) => { if (e.target === el) closeModal(); });
    el.querySelectorAll('.modal-close').forEach((b) => b.addEventListener('click', () => closeModal()));
    el.addEventListener('keydown', (e) => {
      if (e.key !== 'Tab') return;
      const f = [...el.querySelectorAll('button, a[href], input, code.try')].filter((x) => !x.hidden && x.offsetParent);
      const i = f.indexOf(document.activeElement);
      if (e.shiftKey && i <= 0) { e.preventDefault(); f[f.length - 1].focus(); }
      else if (!e.shiftKey && i === f.length - 1) { e.preventDefault(); f[0].focus(); }
    });
  });
  const closeHelp = (restoreFocus = true) => { if (openModalEl === helpModal) closeModal(restoreFocus); };
  $('#helpBtn').addEventListener('click', () => openModal(helpModal));
  helpModal.querySelectorAll('code.try').forEach((c) => {
    c.tabIndex = 0;
    c.setAttribute('role', 'button');
    c.addEventListener('keydown', (e) => { if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); c.click(); } });
  });
  document.addEventListener('keydown', (e) => {
    if (e.key === 'Escape') { closeModal(); pop.hidden = true; document.querySelectorAll('.dropdown').forEach((d) => { d.hidden = true; }); }
  });
  helpModal.querySelectorAll('code.try').forEach((c) => {
    c.title = 'Click to add to your graph';
    c.addEventListener('click', () => {
      const txt = c.textContent;
      const last = state.items[state.items.length - 1];
      if (last && !last.text.trim()) last.text = txt; else state.items.push(newItem(txt));
      buildList(); changed(); ensureTrailingEmpty();
      closeHelp(false);
      toast(`Added  ${txt}`);
    });
  });

  // ---------- toast ----------
  let toastTimer = 0;
  function toast(text, actionLabel, action) {
    const t = $('#toast'), btn = $('#toastAction');
    $('#toastText').textContent = text;
    btn.hidden = !actionLabel;
    btn.textContent = actionLabel || '';
    btn.onclick = () => { t.hidden = true; if (action) action(); };
    t.hidden = false;
    clearTimeout(toastTimer);
    toastTimer = setTimeout(() => { t.hidden = true; }, actionLabel ? 6000 : 2600);
  }

  // ---------- snapshots / persistence ----------
  function serial() {
    return {
      v: 1,
      items: state.items.filter((it) => it.text.trim()).map((it) => {
        const o = { text: it.text, color: it.color };
        if (it.hidden) o.hidden = true;
        if (it.tmin !== '0') o.tmin = it.tmin;
        if (it.tmax !== '2π') o.tmax = it.tmax;
        if (Object.keys(it.ranges).length) o.ranges = it.ranges;
        return o;
      }),
      view: { cx: view.cx, cy: view.cy, scale: view.scale },
      settings: state.settings,
    };
  }
  function snapshot() { return JSON.parse(JSON.stringify(serial())); }
  function load(data) {
    state.items.forEach(stopPlaying);
    state.items = (data.items || []).map((o) => newItem(o.text, {
      color: o.color || PALETTE[0], hidden: !!o.hidden, tmin: o.tmin || '0', tmax: o.tmax || '2π',
      ranges: JSON.parse(JSON.stringify(o.ranges || (o.slider ? { val: o.slider } : {}))),
    }));
    state.colorIdx = state.items.length;
    if (data.view && data.view.scale > 0) Object.assign(view, data.view);
    if (data.settings) Object.assign(state.settings, data.settings);
    syncSettingsUI();
  }
  function restore(snap) {
    load(snap);
    buildList();
    ensureTrailingEmpty();
    changed();
  }

  let saveTimer = 0;
  function save() { clearTimeout(saveTimer); saveTimer = setTimeout(saveNow, 300); }
  const saveSoon = save;
  function saveNow() {
    try { localStorage.setItem(STORE_KEY, JSON.stringify(serial())); } catch (e) { /* storage may be unavailable */ }
  }

  const b64enc = (s) => btoa(unescape(encodeURIComponent(s))).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
  const b64dec = (s) => decodeURIComponent(escape(atob(s.replace(/-/g, '+').replace(/_/g, '/'))));

  async function copyField(input, msg) {
    try { await navigator.clipboard.writeText(input.value); toast(msg); }
    catch (e) { input.focus(); input.select(); toast('Selected – press ⌘C (or Ctrl+C) to copy'); }
  }
  $('#shareBtn').addEventListener('click', () => {
    const code = b64enc(JSON.stringify(serial()));
    $('#shareCode').value = code;
    $('#shareLinkBlock').hidden = FRAMED;
    if (!FRAMED) $('#shareLink').value = location.href.split('#')[0] + '#g=' + code;
    $('#openCode').value = '';
    $('#openErr').hidden = true;
    openModal(shareModal, FRAMED ? $('#copyCode') : $('#copyLink'));
  });
  $('#copyLink').addEventListener('click', () => copyField($('#shareLink'), 'Link copied – anyone who opens it sees this graph'));
  $('#copyCode').addEventListener('click', () => copyField($('#shareCode'), 'Graph code copied'));
  function openCode() {
    const raw = $('#openCode').value.trim();
    const m = /g=([\w-]+)/.exec(raw);
    const code = m ? m[1] : raw.replace(/\s+/g, '');
    try {
      const data = JSON.parse(b64dec(code));
      if (!data || !Array.isArray(data.items)) throw new Error('not a graph');
      const snap = snapshot();
      closeModal(false);
      restore(data);
      toast('Graph opened', 'Undo', () => restore(snap));
    } catch (e) {
      const err = $('#openErr');
      err.textContent = raw ? 'That isn’t a graph code – copy it again from Share.' : 'Paste a graph code first.';
      err.hidden = false;
    }
  }
  $('#openCodeBtn').addEventListener('click', openCode);
  $('#openCode').addEventListener('keydown', (e) => { if (e.key === 'Enter') { e.preventDefault(); openCode(); } });

  // ---- save image dialog
  $('#exportBtn').addEventListener('click', () => {
    hoverPt = null;
    render(false);
    const url = canvas.toDataURL('image/png');
    $('#exportImg').src = url;
    const dl = $('#downloadImg');
    dl.href = url;
    const canSave = !FRAMED || !!downloadsApi;
    dl.hidden = !canSave;
    $('#imgHint').textContent = canSave
      ? 'You can also right-click the image to copy or save it.'
      : 'To save it, right-click the image (press and hold on a phone) and choose Save Image.';
    openModal(imageModal, canSave ? dl : $('#copyImg'));
  });
  $('#downloadImg').addEventListener('click', (e) => {
    if (!FRAMED) return; // a normal page: the <a download> link does the work
    e.preventDefault();
    if (!downloadsApi) return;
    const b64 = $('#exportImg').src.split(',')[1];
    const bin = atob(b64), bytes = new Uint8Array(bin.length);
    for (let k = 0; k < bin.length; k++) bytes[k] = bin.charCodeAt(k);
    downloadsApi.save({ filename: 'complex-plane.png', data: bytes })
      .then(() => toast('Image saved'))
      .catch((err) => {
        const code = err && err.code;
        if (code === 'declined') return;
        if (code === 'rate_limited') toast('A save is already waiting – try again in a moment');
        else if (code === 'host_unavailable') toast('This app can’t save files – open the grapher in a browser');
        else { downloadsApi = null; $('#downloadImg').hidden = true; toast('Saving isn’t available here – right-click the image instead'); }
      });
  });
  $('#copyImg').addEventListener('click', async () => {
    try {
      const blob = new Promise((res) => canvas.toBlob(res, 'image/png'));
      await navigator.clipboard.write([new ClipboardItem({ 'image/png': blob })]);
      toast('Image copied – paste it into a document or message');
    } catch (e) {
      toast('Your browser blocked copying – right-click the image instead');
    }
  });

  // ------------------------------------------------------------------ init
  const DEFAULT = ['a = 2 + i', '|z - a| = 1.5', 'arg(z + 1) = π/4', '|z| ≤ 1'];

  function init() {
    buildKeypad();
    buildExamples();
    const r = stage.getBoundingClientRect();
    W = r.width; H = r.height;
    let loaded = false;
    const m = /#g=([\w-]+)/.exec(location.hash);
    if (m) {
      try { load(JSON.parse(b64dec(m[1]))); loaded = true; } catch (e) { console.warn('bad link', e); }
      // Drop the hash so later reloads show the user's own edits (saved locally), not the original link.
      try { history.replaceState(null, '', location.href.split('#')[0]); } catch (e) { /* sandboxed */ }
    }
    if (!loaded) {
      try {
        const saved = localStorage.getItem(STORE_KEY);
        if (saved) { load(JSON.parse(saved)); loaded = true; }
      } catch (e) { /* ignore */ }
    }
    if (!loaded || !state.items.length) {
      if (!loaded) pendingHome = true;
      state.items = DEFAULT.map((t) => newItem(t));
    }
    syncSettingsUI();
    analyze();
    buildList();
    ensureTrailingEmpty();
    new ResizeObserver(resize).observe(stage);
    resize();
    if (!m && window.matchMedia('(pointer: fine)').matches) {
      const last = state.items[state.items.length - 1];
      if (last && !last.text.trim()) focusItem(last);
    }
    setTimeout(hideHint, 9000);
  }

  window.addEventListener('beforeunload', saveNow);
  init();
  // exposed for debugging/tests
  window.__grapher = {
    state, analyze: () => analysis, render, solveRoots,
    setItems: (texts) => restore({ items: texts.map((t, k) => ({ text: t, color: PALETTE[k % PALETTE.length] })) }),
    statuses: () => [...document.querySelectorAll('.row')].map((r) => r.querySelector('.expr').value + '  →  ' + r.querySelector('.status').textContent),
  };
})();
