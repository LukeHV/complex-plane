/* Typesets expressions as HTML maths: stacked fractions, radicals, superscripts,
 * stretchy |bars| and brackets, conjugate bars, subscripts. Works from the parser's
 * syntax tree, so what you see is exactly what the grapher understood.
 * Also formats numbers exactly where possible (√3/2, 1/3, π/4). */
(function (G) {
  'use strict';
  const P = G.CPARSER;
  const { fmtNum } = G.CX;

  const esc = (s) => String(s).replace(/[&<>"]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));
  const MINUS = '−';

  // ---------- building blocks ----------
  const mi = (s) => `<span class="mi">${esc(s)}</span>`;
  const mn = (s) => `<span class="mn">${esc(String(s).replace('-', MINUS))}</span>`;
  const mo = (s, cls = 'mo') => `<span class="${cls}">${s}</span>`;
  const fn = (s) => `<span class="mf">${esc(s)}</span>`;
  // Visually hidden text: keeps copy/paste and screen readers accurate (e.g. "√(3)/2").
  const vh = (s) => `<span class="vh">${esc(s)}</span>`;
  const wrapIf = (h, yes) => (yes ? vh('(') + h + vh(')') : h);
  const frac = (a, b, pa = false, pb = false) =>
    `<span class="frac"><span class="num">${wrapIf(a, pa)}</span>${vh('/')}<span class="den">${wrapIf(b, pb)}</span></span>`;
  const sup = (a, np = false) => `<span class="sup">${vh('^')}${wrapIf(a, np)}</span>`;
  const RAD = '<svg class="rad" viewBox="0 0 10 20" preserveAspectRatio="none" aria-hidden="true"><path d="M0.6 12.2 L2.6 11 L5.4 19.4 L9.6 0.6 L10 0.6" vector-effect="non-scaling-stroke"/></svg>';
  const sqrt = (a) => `<span class="sqrt">${RAD}${vh('√(')}<span class="rad-body">${a}</span>${vh(')')}</span>`;
  const abs = (a) => `<span class="abs">${vh('|')}${a}${vh('|')}</span>`;
  const bar = (a) => `<span class="conj">${vh('conj(')}${a}${vh(')')}</span>`;
  const PL = '<svg class="pl" viewBox="0 0 10 20" preserveAspectRatio="none" aria-hidden="true"><path d="M8 0.6 Q1 10 8 19.4" vector-effect="non-scaling-stroke"/></svg>';
  const PR = '<svg class="pr" viewBox="0 0 10 20" preserveAspectRatio="none" aria-hidden="true"><path d="M2 0.6 Q9 10 2 19.4" vector-effect="non-scaling-stroke"/></svg>';
  const paren = (x) => x.tall
    ? `<span class="tparen">${PL}${vh('(')}<span class="tp-body">${x.h}</span>${vh(')')}${PR}</span>`
    : `<span class="paren">(</span>${x.h}<span class="paren">)</span>`;

  const GREEK = { alpha: 'α', beta: 'β', gamma: 'γ', delta: 'δ', lambda: 'λ', mu: 'μ', phi: 'φ', omega: 'ω', theta: 'θ', rho: 'ρ', sigma: 'σ', tau: 'τ' };
  function name(nm) {
    if (nm === 'π') return `<span class="mc">π</span>`;
    const m = /^([A-Za-zͰ-Ͽ]+?)_?(\d+|_[A-Za-z0-9]+)$/.exec(nm);
    const base = (b) => mi(GREEK[b] || b);
    if (m && m[1]) return base(m[1]) + `<sub>${esc(m[2].replace(/^_/, ''))}</sub>`;
    return base(nm.replace(/_$/, ''));
  }

  const FN_LABEL = { re: 'Re', im: 'Im', arg: 'arg', mod: 'mod', ln: 'ln', log: 'log', sin: 'sin', cos: 'cos', tan: 'tan', sinh: 'sinh', cosh: 'cosh', tanh: 'tanh', cis: 'cis' };

  // Precedence: 0 relation, 1 sum, 2 product, 2.5 negation, 3 fraction, 4 power, 5 atom
  function leadsWithNumber(n) {
    if (n.type === 'num') return true;
    if (n.type === 'bin' && (n.op === '*' || n.op === '^')) return leadsWithNumber(n.a);
    if (n.type === 'deg') return leadsWithNumber(n.a);
    return false;
  }
  function endsWithNumber(n) {
    if (n.type === 'num') return true;
    if (n.type === 'deg') return false;
    if (n.type === 'bin' && n.op === '*') return endsWithNumber(n.b);
    return false;
  }

  function r(n) {
    switch (n.type) {
      case 'num': return { h: mn(fmtLiteral(n.v)), p: 5 };
      case 'name': return { h: name(n.name), p: 5 };
      case 'deg': { const a = r(n.a); return { h: (a.p < 5 ? paren(a) : a.h) + mo('°', 'mdeg'), p: 5, tall: a.tall }; }
      case 'neg': {
        const a = r(n.a);
        return { h: mo(MINUS, 'mneg') + (a.p < 2 || n.a.type === 'neg' ? paren(a) : a.h), p: 2.5, tall: a.tall };
      }
      case 'bin': return rBin(n);
      case 'call': return rCall(n);
      case 'ucall': { const a = r(n.args[0]); return { h: name(n.fn) + paren(a), p: 5, tall: a.tall }; }
      case 'rel': {
        const a = r(n.a), b = r(n.b);
        const sym = { eq: '=', lt: '&lt;', gt: '&gt;', le: '≤', ge: '≥' }[n.op];
        return { h: a.h + mo(sym, 'mrel') + b.h, p: 0, tall: a.tall || b.tall };
      }
      case 'and': case 'or': {
        // re-join chained relations (1 < |z| < 2) written as a single chain
        const chain = flattenChain(n);
        if (chain) return chain;
        const a = r(n.a), b = r(n.b);
        return { h: a.h + `<span class="mword">${n.type}</span>` + b.h, p: -1, tall: a.tall || b.tall };
      }
    }
    return { h: '?', p: 5 };
  }

  // a < b and b < c  (as produced from "a < b < c") -> show as one chain
  const REL = { eq: '=', lt: '&lt;', gt: '&gt;', le: '≤', ge: '≥' };
  function flattenChain(n) {
    if (n.type !== 'and' || !n.chain) return null;
    const rels = [];
    (function collect(x) { if (x.type === 'and' && x.chain) { collect(x.a); collect(x.b); } else rels.push(x); })(n);
    const first = r(rels[0].a);
    let h = first.h, tall = first.tall;
    for (const rl of rels) { const b = r(rl.b); h += mo(REL[rl.op], 'mrel') + b.h; tall = tall || b.tall; }
    return { h, p: 0, tall };
  }

  function rBin(n) {
    const A = r(n.a), B = r(n.b);
    const tall = A.tall || B.tall;
    switch (n.op) {
      case '+': {
        if (n.b.type === 'neg') return { h: A.h + mo(MINUS) + (r(n.b.a).p < 2 ? paren(r(n.b.a)) : r(n.b.a).h), p: 1, tall };
        return { h: A.h + mo('+') + B.h, p: 1, tall };
      }
      case '-': return { h: A.h + mo(MINUS) + (B.p <= 1 || n.b.type === 'neg' ? paren(B) : B.h), p: 1, tall };
      case '*': {
        const left = A.p < 2 ? paren(A) : A.h;
        const right = B.p < 2 || n.b.type === 'neg' ? paren(B) : B.h;
        let join = '';
        if (leadsWithNumber(n.b) && B.p >= 2 && !(A.p < 2)) join = mo('·', 'mdot');
        else if (endsWithNumber(n.a) && n.b.type === 'num') join = mo('·', 'mdot');
        else if (n.b.type === 'call' || n.b.type === 'ucall') join = '<span class="thin"><span class="vh"> </span></span>';
        return { h: left + join + right, p: 2, tall };
      }
      case '/': return { h: frac(A.h, B.h, A.p < 5, B.p < 5), p: 3, tall: true };
      case '^': {
        const base = A.p < 5 ? paren(A) : A.h;
        return { h: base + sup(B.h, B.p < 5), p: 4, tall: A.tall };
      }
    }
    return { h: '?', p: 5 };
  }

  function rCall(n) {
    const a = r(n.args[0]);
    switch (n.fn) {
      case 'sqrt': return { h: sqrt(a.h), p: 5, tall: a.tall };
      case 'abs': case 'mod': return { h: abs(a.h), p: 5, tall: a.tall };
      case 'conj': return { h: bar(a.h), p: 5, tall: a.tall };
      case 'exp': return { h: mi('e') + sup(a.h, a.p < 5), p: 4 };
    }
    return { h: fn(FN_LABEL[n.fn] || n.fn) + paren(a), p: 5, tall: a.tall };
  }

  function fmtLiteral(v) {
    let s = String(v);
    if (/e/.test(s)) s = String(+v.toPrecision(12));
    return s;
  }

  // Render a whole input line. Returns HTML, or null if the line doesn't parse.
  function renderLine(text, names, funcs) {
    const t = text.trim();
    if (!t) return null;
    if (t.startsWith('#') || t.startsWith('//')) return `<span class="mnote">${esc(t.replace(/^(#|\/\/)\s*/, ''))}</span>`;
    try {
      const d = P.matchDefinition(t);
      if (d) {
        const rhs = P.parse(d.rhs, d.param ? [...names, d.param] : names, funcs);
        const lhs = d.param ? name(d.name) + paren({ h: name(d.param) }) : name(d.name);
        return lhs + mo('=', 'mrel') + r(rhs).h;
      }
      return r(P.parse(t, names, funcs)).h;
    } catch (e) {
      return null;
    }
  }

  // ---------- exact number formatting ----------
  const SQUAREFREE = [1, 2, 3, 5, 6, 7, 10, 11, 13, 14, 15, 17, 19, 21, 22, 23, 26, 29, 30];
  // Finds x = sign · n√k / d with small integers.
  function exactParts(x) {
    if (!Number.isFinite(x) || x === 0) return null;
    const ax = Math.abs(x);
    const s = surdParts(ax);
    if (s) return Object.assign(s, { neg: x < 0 });
    const base = ax / Math.PI; // n·π/d
    for (let d = 1; d <= 12; d++) {
      const n = base * d, rn = Math.round(n);
      if (rn >= 1 && rn <= 100 && Math.abs(n - rn) < 1e-9 * Math.max(1, n)) {
        const g = gcd(rn, d);
        return { neg: x < 0, n: rn / g, d: d / g, k: 1, pi: true };
      }
    }
    return null;
  }
  function surdParts(ax) {
    for (const k of SQUAREFREE) {
      const base = ax / Math.sqrt(k);
      for (let d = 1; d <= 12; d++) {
        const n = base * d, rn = Math.round(n);
        if (rn >= 1 && rn <= 400 && Math.abs(n - rn) < 1e-9 * Math.max(1, n)) {
          const g = gcd(rn, d);
          return { n: rn / g, d: d / g, k };
        }
      }
    }
    return null;
  }
  function gcd(a, b) { while (b) [a, b] = [b, a % b]; return a; }

  // Is it worth showing exactly? (Terminating decimals like 1.25 read better as decimals.)
  function niceExact(x, preferFrac) {
    const e = exactParts(x);
    if (!e) return null;
    if (e.k === 1 && !e.pi && !preferFrac) {
      if (e.d === 1) return null; // integer: decimal formatting is already exact
      if (Math.abs(x * 1000 - Math.round(x * 1000)) < 1e-9) return null;
    }
    return e;
  }

  function exactHTML(e, withSign = true) {
    const top = e.pi ? (e.n === 1 ? '' : mn(e.n)) + '<span class="mc">π</span>'
      : e.k === 1 ? mn(e.n) : (e.n === 1 ? '' : mn(e.n)) + sqrt(mn(e.k));
    const body = e.d === 1 ? top : frac(top, mn(e.d));
    return (withSign && e.neg ? mo(MINUS, 'mneg') : '') + body;
  }

  // HTML for a real number: exact if it's a simple fraction or surd, else 4 s.f.
  function real(x, sig = 4, preferFrac = false) {
    const e = niceExact(x, preferFrac);
    if (e) return exactHTML(e);
    return mn(fmtNum(x, sig));
  }
  // Same, but appends "≈ decimal" after an exact surd/fraction.
  function realApprox(x) {
    const e = niceExact(x);
    if (e) return exactHTML(e) + `<span class="approx"> ≈ ${esc(fmtNum(x, 4))}</span>`;
    return mn(fmtNum(x, 4));
  }

  function complex(z, sig = 4) {
    if (!z || Number.isNaN(z.re) || Number.isNaN(z.im)) return mn('undefined');
    if (!Number.isFinite(z.re) || !Number.isFinite(z.im)) return mn('∞');
    const scale = Math.max(1, Math.abs(z.re), Math.abs(z.im));
    const re = Math.abs(z.re) < 1e-10 * scale ? 0 : z.re;
    const im = Math.abs(z.im) < 1e-10 * scale ? 0 : z.im;
    const imPart = (v) => {
      const av = Math.abs(v);
      if (Math.abs(av - 1) < 1e-12) return mi('i');
      const e = niceExact(av);
      if (e && e.k !== 1 && e.d === 1) return exactHTML(e) + mi('i'); // 2√3 i
      if (e) return exactHTML(e) + mi('i');
      return mn(fmtNum(av, sig)) + mi('i');
    };
    const surdy = (v) => { const e = niceExact(Math.abs(v)); return !!e && (e.k !== 1 || e.d !== 1); };
    const useFrac = re !== 0 && im !== 0 && (surdy(re) || surdy(im));
    if (im === 0) return real(re, sig);
    if (re === 0) return (im < 0 ? mo(MINUS, 'mneg') : '') + imPart(im);
    return real(re, sig, useFrac) + mo(im < 0 ? MINUS : '+') + imPart(im);
  }

  function angle(a) {
    if (Number.isNaN(a)) return mn('undefined');
    const deg = `<span class="approx"> (${esc(fmtNum(a * 180 / Math.PI, 4))}°)</span>`;
    if (Math.abs(a) < 1e-12) return mn('0') + deg;
    for (let d = 1; d <= 12; d++) {
      const n = a * d / Math.PI, rn = Math.round(n);
      if (rn !== 0 && Math.abs(n - rn) < 1e-9) {
        const g = gcd(Math.abs(rn), d), num = Math.abs(rn) / g, den = d / g;
        const top = (num === 1 ? '' : mn(num)) + '<span class="mc">π</span>';
        return (rn < 0 ? mo(MINUS, 'mneg') : '') + (den === 1 ? top : frac(top, mn(den))) + deg;
      }
    }
    return mn(fmtNum(a, 4)) + deg;
  }

  const SUBS = { 0: '₀', 1: '₁', 2: '₂', 3: '₃', 4: '₄', 5: '₅', 6: '₆', 7: '₇', 8: '₈', 9: '₉' };
  function plainName(nm) {
    const m = /^([A-Za-z\u0370-\u03FF]+?)_?(\d+)$/.exec(nm);
    return m ? m[1] + m[2].split('').map((c) => SUBS[c]).join('') : nm.replace(/_/g, '');
  }

  // Wrap an HTML fragment as inline maths.
  const wrap = (h) => `<span class="math">${h}</span>`;

  G.MATH = { renderLine, real, realApprox, complex, angle, wrap, name, plainName, exactParts };
})(typeof window !== 'undefined' ? window : globalThis);
