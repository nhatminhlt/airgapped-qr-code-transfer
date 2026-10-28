// Systematic LT fountain code shared by generator.html and scanner.html.
//
// The file is cut into K blocks of B bytes. Symbol `seed` < K is block `seed`
// itself; symbols >= K are XORs of a pseudo-random set of blocks (degree from
// a robust soliton distribution). The receiver can rebuild the set of blocks
// behind any symbol from its seed alone, so it only needs to collect enough
// symbols - it does not matter which ones.
(function (global) {
  const mulberry32 = (a) => () => {
    a = (a + 0x6d2b79f5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };

  const idhash = (str) => {
    let h = 2166136261;
    for (let i = 0; i < str.length; i++) {
      h = Math.imul(h ^ str.charCodeAt(i), 16777619);
    }
    return h >>> 0;
  };

  const cdf_cache = new Map();
  const degree_cdf = (K) => {
    if (cdf_cache.has(K)) return cdf_cache.get(K);
    const c = 0.1;
    const delta = 0.5;
    const R = c * Math.log(K / delta) * Math.sqrt(K);
    const spike = Math.max(1, Math.min(K, Math.round(K / Math.max(R, 1e-9))));
    const mu = new Float64Array(K + 1);
    let sum = 0;
    for (let i = 1; i <= K; i++) {
      const rho = i === 1 ? 1 / K : 1 / (i * (i - 1));
      let tau = 0;
      if (i < spike) tau = R / (i * K);
      else if (i === spike) tau = Math.max(0, (R * Math.log(R / delta)) / K);
      mu[i] = rho + tau;
      sum += mu[i];
    }
    const cdf = new Float64Array(K + 1);
    let acc = 0;
    for (let i = 1; i <= K; i++) {
      acc += mu[i] / sum;
      cdf[i] = acc;
    }
    cdf_cache.set(K, cdf);
    return cdf;
  };

  // Degree of a repair symbol. Half follow the robust soliton (cheap peeling),
  // half are log-uniform up to K/4 so that, whatever fraction of blocks is
  // still missing, many symbols touch a few of them (good for the Gaussian
  // fallback in the decoder).
  const repair_degree = (rng, K) => {
    if (rng() < Fountain.soliton_share) {
      const cdf = degree_cdf(K);
      const r = rng();
      let lo = 1;
      let hi = K;
      while (lo < hi) {
        const mid = (lo + hi) >> 1;
        if (cdf[mid] >= r) hi = mid;
        else lo = mid + 1;
      }
      return lo;
    }
    const max = Math.max(2, Math.floor(K / 4));
    return Math.min(K, Math.max(1, Math.round(Math.exp(rng() * Math.log(max)))));
  };

  const neighbors = (seed, K, idh) => {
    if (seed < K) return [seed];
    const rng = mulberry32(Math.imul(seed + 1, 2654435761) ^ idh);
    const lo = repair_degree(rng, K);
    const picked = new Set();
    while (picked.size < lo) picked.add(Math.floor(rng() * K));
    return Array.from(picked);
  };

  // padded: Uint8Array of K*B bytes
  const encode = (padded, K, B, idh, seed) => {
    const out = new Uint8Array(B);
    for (const n of neighbors(seed, K, idh)) {
      const off = n * B;
      for (let i = 0; i < B; i++) out[i] ^= padded[off + i];
    }
    return out;
  };

  class Decoder {
    constructor(K, B, idh) {
      this.K = K;
      this.B = B;
      this.idh = idh;
      this.blocks = new Array(K).fill(null);
      this.solved = 0;
      this.refs = Array.from({ length: K }, () => []);
      this.seen = new Set();
      this.active = [];
      this.last_gauss = 0;
    }

    // Returns true if the symbol was new.
    add(seed, bytes) {
      if (this.seen.has(seed)) return false;
      this.seen.add(seed);
      const d = new Uint8Array(this.B);
      d.set(bytes.subarray(0, this.B));
      const unknown = [];
      for (const n of neighbors(seed, this.K, this.idh)) {
        const known = this.blocks[n];
        if (known) {
          for (let i = 0; i < this.B; i++) d[i] ^= known[i];
        } else {
          unknown.push(n);
        }
      }
      if (unknown.length === 1) {
        this._solve(unknown[0], d);
      } else if (unknown.length > 1) {
        const sym = { unknown, d, done: false };
        for (const n of unknown) this.refs[n].push(sym);
        this.active.push(sym);
      }
      this._maybe_gauss();
      return true;
    }

    // Once there are at least as many pending symbols as missing blocks,
    // solve the remaining system over GF(2) (rows = symbols, cols = blocks).
    _maybe_gauss() {
      const missing = this.K - this.solved;
      if (!missing || missing > 700) return;
      this.active = this.active.filter((x) => !x.done);
      const rows = this.active.length;
      if (rows < missing) return;
      if (rows < this.last_gauss + Math.max(2, Math.ceil(missing * 0.02))) return;
      this.last_gauss = rows;
      this._gauss();
    }

    _gauss() {
      const cols = [];
      const col_of = new Map();
      for (let i = 0; i < this.K; i++) {
        if (!this.blocks[i]) {
          col_of.set(i, cols.length);
          cols.push(i);
        }
      }
      const m = cols.length;
      const words = (m + 31) >>> 5;
      const rows = this.active.map((sym) => {
        const bits = new Uint32Array(words);
        for (const n of sym.unknown) {
          const c = col_of.get(n);
          bits[c >>> 5] |= 1 << (c & 31);
        }
        return { bits, d: sym.d.slice() };
      });
      const pivot_row = new Array(m).fill(-1);
      let used = 0;
      for (let c = 0; c < m; c++) {
        const w = c >>> 5;
        const mask = 1 << (c & 31);
        let r = -1;
        for (let i = used; i < rows.length; i++) {
          if (rows[i].bits[w] & mask) {
            r = i;
            break;
          }
        }
        if (r < 0) continue;
        [rows[used], rows[r]] = [rows[r], rows[used]];
        const piv = rows[used];
        for (let i = 0; i < rows.length; i++) {
          if (i !== used && rows[i].bits[w] & mask) {
            const row = rows[i];
            for (let k = 0; k < words; k++) row.bits[k] ^= piv.bits[k];
            for (let k = 0; k < this.B; k++) row.d[k] ^= piv.d[k];
          }
        }
        pivot_row[c] = used;
        used++;
      }
      for (let c = 0; c < m; c++) {
        const r = pivot_row[c];
        if (r < 0) continue;
        const row = rows[r];
        let single = true;
        for (let k = 0; k < words; k++) {
          const expect = k === c >>> 5 ? 1 << (c & 31) : 0;
          if (row.bits[k] !== expect) {
            single = false;
            break;
          }
        }
        if (single && !this.blocks[cols[c]]) this._solve(cols[c], row.d);
      }
    }

    _solve(index, data) {
      const stack = [[index, data]];
      while (stack.length) {
        const [i, d] = stack.pop();
        if (this.blocks[i]) continue;
        this.blocks[i] = d;
        this.solved++;
        for (const sym of this.refs[i]) {
          if (sym.done) continue;
          for (let k = 0; k < this.B; k++) sym.d[k] ^= d[k];
          sym.unknown = sym.unknown.filter((n) => n !== i);
          if (sym.unknown.length === 1) {
            sym.done = true;
            stack.push([sym.unknown[0], sym.d]);
          } else if (sym.unknown.length === 0) {
            sym.done = true;
          }
        }
        this.refs[i] = [];
      }
    }

    get complete() {
      return this.solved === this.K;
    }

    result(length) {
      const out = new Uint8Array(this.K * this.B);
      for (let i = 0; i < this.K; i++) out.set(this.blocks[i], i * this.B);
      return out.subarray(0, length);
    }
  }

  const Fountain = { idhash, neighbors, encode, Decoder, soliton_share: 0.2 };
  if (typeof module !== "undefined") module.exports = Fountain;
  else global.Fountain = Fountain;
})(typeof window !== "undefined" ? window : globalThis);
