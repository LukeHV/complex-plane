/* Complex arithmetic + number formatting.
 * Complex numbers are plain {re, im} objects; operations never mutate inputs. */
(function (G) {
  'use strict';

  const C = (re, im = 0) => ({ re, im });
  const TAU = Math.PI * 2;

  const add = (a, b) => ({ re: a.re + b.re, im: a.im + b.im });
  const sub = (a, b) => ({ re: a.re - b.re, im: a.im - b.im });
  const mul = (a, b) => ({ re: a.re * b.re - a.im * b.im, im: a.re * b.im + a.im * b.re });
  const neg = (a) => ({ re: -a.re, im: -a.im });
  function div(a, b) {
    const d = b.re * b.re + b.im * b.im;
    return { re: (a.re * b.re + a.im * b.im) / d, im: (a.im * b.re - a.re * b.im) / d };
  }
  const abs = (a) => Math.sqrt(a.re * a.re + a.im * a.im);
  // Principal argument in (-pi, pi]; undefined at 0. (+0 turns -0 into +0 so the
  // negative real axis gives +pi, not -pi.)
  function arg(a) {
    if (a.re === 0 && a.im === 0) return NaN;
    return Math.atan2(a.im + 0, a.re);
  }
  const conj = (a) => ({ re: a.re, im: -a.im });
  function exp(a) {
    const r = Math.exp(a.re);
    return { re: r * Math.cos(a.im), im: r * Math.sin(a.im) };
  }
  const log = (a) => ({ re: Math.log(abs(a)), im: Math.atan2(a.im + 0, a.re) });
  function sqrt(a) {
    const r = abs(a);
    const re = Math.sqrt(Math.max(0, (r + a.re) / 2));
    let im = Math.sqrt(Math.max(0, (r - a.re) / 2));
    if (a.im < 0) im = -im;
    return { re, im };
  }
  function pow(a, b) {
    // Integer powers by repeated squaring: exact for things like (-1)^2.
    if (b.im === 0 && Number.isInteger(b.re) && Math.abs(b.re) <= 1024) {
      let n = Math.abs(b.re), r = C(1, 0), base = a;
      while (n) { if (n & 1) r = mul(r, base); base = mul(base, base); n = Math.floor(n / 2); }
      return b.re < 0 ? div(C(1, 0), r) : r;
    }
    if (a.re === Math.E && a.im === 0) return exp(b);
    if (a.re === 0 && a.im === 0) return (b.re > 0) ? C(0, 0) : C(NaN, NaN);
    // Positive real base with real exponent: stay exactly real.
    if (a.im === 0 && a.re > 0 && b.im === 0) return C(Math.pow(a.re, b.re), 0);
    return exp(mul(b, log(a)));
  }
  const sin = (a) => ({ re: Math.sin(a.re) * Math.cosh(a.im), im: Math.cos(a.re) * Math.sinh(a.im) });
  const cos = (a) => ({ re: Math.cos(a.re) * Math.cosh(a.im), im: -Math.sin(a.re) * Math.sinh(a.im) });
  const tan = (a) => div(sin(a), cos(a));
  const sinh = (a) => ({ re: Math.sinh(a.re) * Math.cos(a.im), im: Math.cosh(a.re) * Math.sin(a.im) });
  const cosh = (a) => ({ re: Math.cosh(a.re) * Math.cos(a.im), im: Math.sinh(a.re) * Math.sin(a.im) });
  const tanh = (a) => div(sinh(a), cosh(a));
  const cis = (a) => exp({ re: -a.im, im: a.re });

  const Cx = { add, sub, mul, div, neg, abs, arg, conj, exp, log, sqrt, pow, sin, cos, tan, sinh, cosh, tanh, cis };

  // ---------- formatting ----------
  const MINUS = '−';

  function fmtNum(x, sig = 4) {
    if (Number.isNaN(x)) return 'undefined';
    if (!Number.isFinite(x)) return x > 0 ? '∞' : MINUS + '∞';
    if (Math.abs(x) < 1e-10) return '0';
    const r = Math.round(x);
    if (Math.abs(x - r) < 1e-9 * Math.max(1, Math.abs(x))) return String(r).replace('-', MINUS);
    const ax = Math.abs(x);
    let s;
    if (ax >= 1e6 || ax < 1e-4) {
      s = x.toExponential(sig - 1).replace(/\.?0+e/, 'e');
      const [m, e] = s.split('e');
      s = m + '×10^' + (+e);
    } else {
      s = String(+x.toPrecision(sig));
    }
    return s.replace('-', MINUS);
  }

  function cleanParts(z) {
    let re = z.re, im = z.im;
    const scale = Math.max(1, Math.abs(re), Math.abs(im));
    if (Math.abs(re) < 1e-10 * scale) re = 0;
    if (Math.abs(im) < 1e-10 * scale) im = 0;
    return [re, im];
  }

  function fmtComplex(z, sig = 4) {
    if (!z || Number.isNaN(z.re) || Number.isNaN(z.im)) return 'undefined';
    if (!Number.isFinite(z.re) || !Number.isFinite(z.im)) return '∞';
    const [re, im] = cleanParts(z);
    const imStr = (v) => {
      const s = fmtNum(Math.abs(v), sig);
      return (s === '1' ? '' : s) + 'i';
    };
    if (im === 0) return fmtNum(re, sig);
    if (re === 0) return (im < 0 ? MINUS : '') + imStr(im);
    return fmtNum(re, sig) + (im < 0 ? ' ' + MINUS + ' ' : ' + ') + imStr(im);
  }

  // Express an angle as a nice multiple of pi when possible.
  function piFraction(a) {
    if (Math.abs(a) < 1e-12) return '0';
    for (let d = 1; d <= 12; d++) {
      const n = a * d / Math.PI;
      const rn = Math.round(n);
      if (rn !== 0 && Math.abs(n - rn) < 1e-9) {
        const g = gcd(Math.abs(rn), d);
        const num = rn / g, den = d / g;
        const sign = num < 0 ? MINUS : '';
        const top = Math.abs(num) === 1 ? 'π' : Math.abs(num) + 'π';
        return sign + top + (den === 1 ? '' : '/' + den);
      }
    }
    return null;
  }
  function gcd(a, b) { while (b) [a, b] = [b, a % b]; return a; }

  function fmtAngle(a) {
    if (Number.isNaN(a)) return 'undefined';
    const deg = a * 180 / Math.PI;
    const degStr = fmtNum(deg, 4) + '°';
    const pf = piFraction(a);
    return (pf || fmtNum(a, 4)) + ' (' + degStr + ')';
  }

  // Plain ASCII literal for writing a point back into an input box, e.g. "1.5 - 2i".
  function literal(re, im, decimals) {
    const f = (v) => {
      let s = v.toFixed(decimals);
      if (s.includes('.')) s = s.replace(/0+$/, '').replace(/\.$/, '');
      return s === '-0' ? '0' : s;
    };
    const r = f(re), i = f(Math.abs(im));
    if (i === '0') return r;
    const istr = (i === '1' ? '' : i) + 'i';
    if (r === '0') return (im < 0 ? '-' : '') + istr;
    return r + (im < 0 ? ' - ' : ' + ') + istr;
  }

  G.CX = { C, Cx, TAU, fmtNum, fmtComplex, fmtAngle, piFraction, literal, MINUS };
})(typeof window !== 'undefined' ? window : globalThis);
