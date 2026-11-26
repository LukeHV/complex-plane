/* Expression language for the grapher.
 *  - tokenize()  : text -> tokens (splits "itz" into i·t·z, "2pi" into 2·π, ...)
 *  - parse()     : tokens -> AST (relations, and/or, |abs|, implicit multiplication)
 *  - depsOf()    : which of z / t an expression depends on
 *  - compile()   : AST -> fast closure (env) => complex
 */
(function (G) {
  'use strict';
  const { C, Cx } = G.CX;

  const FUNCS = ['re', 'im', 'abs', 'mod', 'arg', 'conj', 'sqrt', 'exp', 'ln', 'log',
    'sin', 'cos', 'tan', 'sinh', 'cosh', 'tanh', 'cis'];
  const FUNC_SET = new Set(FUNCS);
  const CONSTS = new Set(['i', 'e', 'pi', 'π']);
  // Names with a built-in meaning: z (the variable), x = Re z, y = Im z, t/θ (curve parameter).
  const RESERVED = new Set(['z', 't', 'x', 'y', 'θ', 'theta']);
  const KEYWORDS = new Set(['and', 'or']);

  class GraphError extends Error {
    constructor(msg, extra) { super(msg); Object.assign(this, extra || {}); }
  }

  const LETTER = /[A-Za-zͰ-Ͽ_]/;
  const WORDCH = /[A-Za-z0-9Ͱ-Ͽ_]/;

  function isReservedName(name) {
    const l = name.toLowerCase();
    return RESERVED.has(name) || CONSTS.has(name) || FUNC_SET.has(l) || KEYWORDS.has(l);
  }

  function normalize(src) {
    return src
      .replace(/[−–—]/g, '-')
      .replace(/[×·∙⋅]/g, '*')
      .replace(/÷/g, '/')
      .replace(/\*\*/g, '^')
      .replace(/≦/g, '≤').replace(/≧/g, '≥');
  }

  // ---------------- tokenizer ----------------
  function tokenize(src, userNames, userFuncs) {
    src = normalize(src);
    const toks = [];
    let i = 0, group = 0;
    const known = [...FUNCS, ...CONSTS, ...RESERVED, ...userNames, ...userFuncs]
      .sort((a, b) => b.length - a.length);
    const push = (t, v, pos, g) => toks.push({ t, v, pos, g: g === undefined ? ++group : g });

    while (i < src.length) {
      const c = src[i];
      if (/\s/.test(c)) { i++; continue; }
      if (/[0-9.]/.test(c)) {
        const m = /^(\d+\.?\d*|\.\d+)/.exec(src.slice(i));
        if (!m) throw new GraphError(`Unexpected "${c}"`, { pos: i });
        push('num', parseFloat(m[0]), i);
        i += m[0].length;
        continue;
      }
      if (LETTER.test(c)) {
        let j = i;
        while (j < src.length && WORDCH.test(src[j])) j++;
        const word = src.slice(i, j);
        const g = ++group;
        splitWord(word, i, g, known, userNames, userFuncs).forEach((tk) => toks.push(tk));
        i = j;
        continue;
      }
      const two = src.slice(i, i + 2);
      if (two === '<=') { push('rel', 'le', i); i += 2; continue; }
      if (two === '>=') { push('rel', 'ge', i); i += 2; continue; }
      if (two === '==') { push('rel', 'eq', i); i += 2; continue; }
      if (two === '&&') { push('and', null, i); i += 2; continue; }
      if (two === '!=') throw new GraphError('"≠" isn\'t supported — try a region with < or > instead', { pos: i });
      switch (c) {
        case '+': case '-': case '*': case '/': case '^': case '(': case ')': case '|': case ',':
          push(c, null, i); break;
        case '[': push('(', null, i); break;
        case ']': push(')', null, i); break;
        case '<': push('rel', 'lt', i); break;
        case '>': push('rel', 'gt', i); break;
        case '≤': push('rel', 'le', i); break;
        case '≥': push('rel', 'ge', i); break;
        case '=': push('rel', 'eq', i); break;
        case '&': case '∧': push('and', null, i); break;
        case '∨': push('or', null, i); break;
        case '°': push('deg', null, i); break;
        case '√': push('id', 'sqrt', i); break;
        case '≠': throw new GraphError('"≠" isn\'t supported — try a region with < or > instead', { pos: i });
        default: throw new GraphError(`I don't understand the symbol "${c}"`, { pos: i });
      }
      i++;
    }
    return toks;
  }

  // Split a run of letters into known names: "itz" -> i, t, z ; "Re" -> re ; "sinz" -> sin, z.
  function splitWord(word, pos, g, known, userNames, userFuncs) {
    const lower = word.toLowerCase();
    if (KEYWORDS.has(lower)) return [{ t: lower, v: null, pos, g }];
    const exact = (w) => userNames.includes(w) || userFuncs.includes(w) || RESERVED.has(w) || CONSTS.has(w);
    if (exact(word)) return [{ t: 'id', v: canon(word), pos, g }];
    if (FUNC_SET.has(lower)) return [{ t: 'id', v: lower, pos, g }];
    if (/[0-9_]/.test(word)) return [{ t: 'id', v: word, pos, g }]; // e.g. z1 – undefined name
    const out = [];
    let p = 0;
    while (p < word.length) {
      let match = null;
      for (const k of known) {
        const piece = word.substr(p, k.length);
        if (piece === k || (FUNC_SET.has(k) && piece.toLowerCase() === k)) { match = k; break; }
      }
      if (!match) match = word[p]; // unknown single letter – reported as undefined later
      out.push({ t: 'id', v: canon(match), pos: pos + p, g });
      p += match.length;
    }
    return out;
  }
  function canon(name) {
    if (name === 'pi') return 'π';
    if (name === 'theta') return 'θ';
    return name;
  }

  // ---------------- parser ----------------
  // Node types: num, name, neg, bin(op), call(fn,args), ucall(fn,args), rel(op), and, or
  function parse(src, userNames = [], userFuncs = []) {
    const toks = tokenize(src, userNames, userFuncs);
    let p = 0, absDepth = 0;
    const peek = () => toks[p];
    const at = (t) => toks[p] && toks[p].t === t;
    const next = () => toks[p++];
    const describe = (tk) => tk ? (tk.t === 'num' ? String(tk.v) : tk.t === 'id' ? tk.v : tk.t === 'rel' ? relSym(tk.v) : tk.t) : 'end';
    function expect(t, msg) {
      if (!at(t)) throw new GraphError(msg || `Expected "${t}"`, { pos: peek() ? peek().pos : src.length });
      return next();
    }

    function parseOr() {
      let a = parseAnd();
      while (at('or')) { next(); a = { type: 'or', a, b: parseAnd() }; }
      return a;
    }
    function parseAnd() {
      let a = parseRel();
      while (at('and') || at(',')) { next(); a = { type: 'and', a, b: parseRel() }; }
      return a;
    }
    function parseRel() {
      const first = parseExpr();
      if (!at('rel')) return first;
      let left = first, node = null;
      while (at('rel')) {
        const op = next().v;
        if (!peek()) throw new GraphError(`Add something after "${relSym(op)}"`, { pos: src.length, incomplete: true });
        const right = parseExpr();
        const r = { type: 'rel', op, a: left, b: right };
        node = node ? { type: 'and', a: node, b: r, chain: true } : r;
        left = right;
      }
      return node;
    }
    function parseExpr() {
      let a = parseTerm();
      while (at('+') || at('-')) {
        const op = next().t;
        if (!peek()) throw new GraphError(`Add something after "${op}"`, { pos: src.length, incomplete: true });
        a = { type: 'bin', op, a, b: parseTerm() };
      }
      return a;
    }
    function startsOperand(tk) {
      if (!tk) return false;
      if (tk.t === 'num' || tk.t === 'id' || tk.t === '(') return true;
      if (tk.t === '|') return absDepth === 0;
      return false;
    }
    function parseTerm() {
      let a = parseUnary();
      for (;;) {
        if (at('*') || at('/')) {
          const op = next().t;
          if (!peek()) throw new GraphError(`Add something after "${op}"`, { pos: src.length, incomplete: true });
          a = { type: 'bin', op, a, b: parseUnary() };
        } else if (startsOperand(peek())) {
          a = { type: 'bin', op: '*', a, b: parsePower() };
        } else break;
      }
      return a;
    }
    function parseUnary() {
      if (at('-')) { next(); return { type: 'neg', a: parseUnary() }; }
      if (at('+')) { next(); return parseUnary(); }
      return parsePower();
    }
    function parsePower() {
      const base = parsePostfix();
      if (at('^')) {
        next();
        return { type: 'bin', op: '^', a: base, b: parseExponent() };
      }
      return base;
    }
    // Exponents: e^it is read as e^(it) when the letters are written together.
    function parseExponent() {
      if (at('-')) { next(); return { type: 'neg', a: parseExponent() }; }
      if (at('+')) { next(); return parseExponent(); }
      const first = peek();
      if (!first) throw new GraphError('Add an exponent after "^"', { pos: src.length, incomplete: true });
      let e = parsePower();
      if (first.t === 'id') {
        while (at('id') && peek().g === first.g && !FUNC_SET.has(peek().v)) {
          e = { type: 'bin', op: '*', a: e, b: parsePower() };
        }
      }
      return e;
    }
    function parsePostfix() {
      let a = parsePrimary();
      while (at('deg')) { next(); a = { type: 'deg', a }; }
      return a;
    }
    function parsePrimary() {
      const tk = peek();
      if (!tk) throw new GraphError('This looks unfinished', { pos: src.length, incomplete: true });
      if (tk.t === 'num') { next(); return { type: 'num', v: tk.v }; }
      if (tk.t === 'id') {
        next();
        const name = tk.v;
        const isBuiltin = FUNC_SET.has(name);
        const isUser = userFuncs.includes(name);
        if (isBuiltin || isUser) {
          let args;
          if (at('(')) {
            next();
            args = [];
            if (at(')')) throw new GraphError(`${name}( ) needs something inside the brackets`, { pos: peek().pos });
            args.push(parseExpr());
            while (at(',')) { next(); args.push(parseExpr()); }
            if (!peek()) throw new GraphError('Missing a closing bracket ")"', { pos: src.length, incomplete: true });
            expect(')', 'Missing a closing bracket ")"');
          } else {
            if (!peek()) throw new GraphError(`${name} needs something to act on, e.g. ${name}(z)`, { pos: src.length, incomplete: true });
            args = [parsePower()];
          }
          if (args.length !== 1) throw new GraphError(`${name}( ) takes one input`, { pos: tk.pos });
          return { type: isBuiltin ? 'call' : 'ucall', fn: name, args };
        }
        return { type: 'name', name, pos: tk.pos };
      }
      if (tk.t === '(') {
        next();
        if (at(')')) throw new GraphError('Empty brackets', { pos: peek().pos });
        const e = parseExpr();
        if (!peek()) throw new GraphError('Missing a closing bracket ")"', { pos: src.length, incomplete: true });
        expect(')', 'Missing a closing bracket ")"');
        return e;
      }
      if (tk.t === '|') {
        next();
        absDepth++;
        const e = parseExpr();
        absDepth--;
        if (!peek()) throw new GraphError('Missing a closing "|"', { pos: src.length, incomplete: true });
        expect('|', 'Missing a closing "|"');
        return { type: 'call', fn: 'abs', args: [e] };
      }
      if (tk.t === ')') throw new GraphError('There is an extra ")"', { pos: tk.pos });
      if (tk.t === 'rel') throw new GraphError(`Something is missing before "${relSym(tk.v)}"`, { pos: tk.pos });
      throw new GraphError(`Unexpected "${describe(tk)}"`, { pos: tk.pos });
    }

    if (!toks.length) throw new GraphError('Empty', { pos: 0, incomplete: true });
    const node = parseOr();
    if (p < toks.length) {
      const tk = peek();
      if (tk.t === ')') throw new GraphError('There is an extra ")"', { pos: tk.pos });
      if (tk.t === '|') throw new GraphError('Unmatched "|"', { pos: tk.pos });
      throw new GraphError(`Unexpected "${describe(tk)}"`, { pos: tk.pos });
    }
    return node;
  }

  function relSym(op) { return { eq: '=', lt: '<', gt: '>', le: '≤', ge: '≥' }[op]; }

  // "name = ..." or "f(z) = ..." at the start of a line?
  const DEF_RE = /^\s*([A-Za-zͰ-Ͽ][A-Za-z0-9_Ͱ-Ͽ]*)\s*(?:\(\s*([A-Za-zͰ-Ͽ][A-Za-z0-9_]*)\s*\))?\s*=(?!=)([\s\S]*)$/;
  function matchDefinition(text) {
    const m = DEF_RE.exec(normalize(text));
    if (!m) return null;
    const name = m[1], param = m[2] || null, rhs = m[3];
    if (isReservedName(name)) return null;
    if (/[<>≤≥=]/.test(rhs)) return null;
    return { name, param, rhs, rhsOffset: text.length - rhs.length };
  }

  // ---------------- context: definitions, dependencies, compilation ----------------
  function createContext() {
    return {
      defs: Object.create(null), // name -> {name, param, node, error}
      _compiled: Object.create(null),
      _visiting: new Set(),
    };
  }

  // Returns a Set containing any of 'z', 't'.
  function depsOf(node, ctx, locals = null, visiting = new Set()) {
    const out = new Set();
    (function walk(n, loc) {
      switch (n.type) {
        case 'num': return;
        case 'name': {
          const nm = n.name;
          if (loc && loc.has(nm)) { out.add('loc'); return; }
          if (nm === 'z' || nm === 'x' || nm === 'y') { out.add('z'); return; }
          if (nm === 't' || nm === 'θ') { out.add('t'); return; }
          if (CONSTS.has(nm)) return;
          const d = ctx.defs[nm];
          if (!d) throw new GraphError(`"${nm}" is not defined`, { undefinedName: nm });
          if (d.param) throw new GraphError(`${nm} is a function — write ${nm}(…)`);
          if (visiting.has(nm)) throw new GraphError(`"${nm}" is defined in terms of itself`);
          if (!d.node) throw new GraphError(`"${nm}" has an error in its definition`);
          visiting.add(nm);
          depsOf(d.node, ctx, null, visiting).forEach((v) => out.add(v));
          visiting.delete(nm);
          return;
        }
        case 'neg': case 'deg': walk(n.a, loc); return;
        case 'bin': case 'rel': case 'and': case 'or': walk(n.a, loc); walk(n.b, loc); return;
        case 'call': n.args.forEach((a) => walk(a, loc)); return;
        case 'ucall': {
          n.args.forEach((a) => walk(a, loc));
          const d = ctx.defs[n.fn];
          if (!d || !d.node) throw new GraphError(`Function ${n.fn} has an error`);
          if (visiting.has(n.fn)) throw new GraphError(`${n.fn} is defined in terms of itself`);
          visiting.add(n.fn);
          depsOf(d.node, ctx, new Set([d.param]), visiting).forEach((v) => { if (v !== 'loc') out.add(v); });
          visiting.delete(n.fn);
          return;
        }
      }
    })(node, locals);
    return out;
  }

  const BUILTIN = {
    re: (a) => C(a.re, 0), im: (a) => C(a.im, 0), abs: (a) => C(Cx.abs(a), 0), mod: (a) => C(Cx.abs(a), 0),
    arg: (a) => C(Cx.arg(a), 0), conj: Cx.conj, sqrt: Cx.sqrt, exp: Cx.exp, ln: Cx.log, log: Cx.log,
    sin: Cx.sin, cos: Cx.cos, tan: Cx.tan, sinh: Cx.sinh, cosh: Cx.cosh, tanh: Cx.tanh, cis: Cx.cis,
  };
  const BIN = { '+': Cx.add, '-': Cx.sub, '*': Cx.mul, '/': Cx.div, '^': Cx.pow };
  const DUMMY_ENV = { z: C(0.123, 0.456), t: 0.789, loc: null };

  // Compile an AST into (env) => complex. env = {z:{re,im}, t:number, loc:{name:complex}|null}
  function compile(node, ctx, locals = null) {
    const deps = depsOf(node, ctx, locals);
    const fn = compileRaw(node, ctx, locals);
    if (deps.size === 0) { const v = fn(DUMMY_ENV); return () => v; } // constant-fold
    return fn;
  }

  function compileDef(name, ctx) {
    if (ctx._compiled[name]) return ctx._compiled[name];
    const d = ctx.defs[name];
    const fn = d.param ? compile(d.node, ctx, new Set([d.param])) : compile(d.node, ctx);
    ctx._compiled[name] = fn;
    return fn;
  }

  function compileRaw(n, ctx, loc) {
    switch (n.type) {
      case 'num': { const v = C(n.v, 0); return () => v; }
      case 'name': {
        const nm = n.name;
        if (loc && loc.has(nm)) return (env) => env.loc[nm];
        switch (nm) {
          case 'z': return (env) => env.z;
          case 'x': return (env) => C(env.z.re, 0);
          case 'y': return (env) => C(env.z.im, 0);
          case 't': case 'θ': return (env) => C(env.t, 0);
          case 'i': { const v = C(0, 1); return () => v; }
          case 'e': { const v = C(Math.E, 0); return () => v; }
          case 'π': { const v = C(Math.PI, 0); return () => v; }
        }
        const d = ctx.defs[nm];
        if (!d) throw new GraphError(`"${nm}" is not defined`, { undefinedName: nm });
        let f = null;
        return (env) => (f || (f = compileDef(nm, ctx)))(env);
      }
      case 'neg': { const a = compileRaw(n.a, ctx, loc); return (env) => Cx.neg(a(env)); }
      case 'deg': { const a = compileRaw(n.a, ctx, loc), k = C(Math.PI / 180, 0); return (env) => Cx.mul(a(env), k); }
      case 'bin': {
        const a = compileRaw(n.a, ctx, loc), b = compileRaw(n.b, ctx, loc), op = BIN[n.op];
        return (env) => op(a(env), b(env));
      }
      case 'call': {
        const a = compileRaw(n.args[0], ctx, loc), f = BUILTIN[n.fn];
        return (env) => f(a(env));
      }
      case 'ucall': {
        const a = compileRaw(n.args[0], ctx, loc);
        const d = ctx.defs[n.fn];
        const param = d.param;
        let body = null;
        return (env) => {
          body = body || compileDef(n.fn, ctx);
          const v = a(env);
          return body({ z: env.z, t: env.t, loc: Object.assign({}, env.loc, { [param]: v }) });
        };
      }
      case 'rel': case 'and': case 'or':
        throw new GraphError('A relation (=, <, >) can only be used once at the top level');
    }
    throw new GraphError('Unknown expression');
  }

  // ---------- AST helpers used for describing / dragging ----------
  function isRealLiteral(n) {
    return n.type === 'num' || (n.type === 'neg' && n.a.type === 'num');
  }
  function isImagLiteral(n) {
    if (n.type === 'name' && n.name === 'i') return true;
    if (n.type === 'neg') return isImagLiteral(n.a);
    if (n.type === 'bin' && n.op === '*') {
      return (n.a.type === 'num' && n.b.type === 'name' && n.b.name === 'i') ||
             (n.b.type === 'num' && n.a.type === 'name' && n.a.name === 'i');
    }
    return false;
  }
  function isComplexLiteral(n) {
    if (isRealLiteral(n) || isImagLiteral(n)) return true;
    if (n.type === 'bin' && (n.op === '+' || n.op === '-')) {
      return (isRealLiteral(n.a) && isImagLiteral(n.b)) || (isImagLiteral(n.a) && isRealLiteral(n.b));
    }
    return false;
  }
  // r·e^(…), e^(…), exp(…), r·cis(θ): returns { exponent node, isCis } or null.
  function polarParts(n) {
    const expo = (m) => {
      if (m.type === 'bin' && m.op === '^' && m.a.type === 'name' && m.a.name === 'e') return { e: m.b, cis: false };
      if (m.type === 'call' && m.fn === 'exp') return { e: m.args[0], cis: false };
      if (m.type === 'call' && m.fn === 'cis') return { e: m.args[0], cis: true };
      return null;
    };
    const direct = expo(n);
    if (direct) return direct;
    if (n.type === 'bin' && n.op === '*') return expo(n.b) || null;
    return null;
  }

  // Is this a sum of arg(...) terms and constants? (Such equations are compared mod 2π.)
  function isAngleExpr(n, ctx) {
    if (depsOf(n, ctx).size === 0) return true;
    if (n.type === 'call' && n.fn === 'arg') return true;
    if (n.type === 'neg') return isAngleExpr(n.a, ctx);
    if (n.type === 'bin' && (n.op === '+' || n.op === '-')) return isAngleExpr(n.a, ctx) && isAngleExpr(n.b, ctx);
    return false;
  }

  G.CPARSER = {
    tokenize, parse, matchDefinition, createContext, depsOf, compile, compileDef,
    isRealLiteral, isComplexLiteral, isAngleExpr, polarParts, isReservedName, relSym, GraphError, FUNCS,
  };
})(typeof window !== 'undefined' ? window : globalThis);
