/*
 * psd.js — Particle size distribution (PSD) of ground coffee from a microscope image.
 * Zero dependencies. Works with PSD.html (element ids are prefixed "psd-").
 *
 * Structure
 *   PSD.core     DOM-free analysis functions (usable on their own, or in a Worker)
 *   PSD.drawChart(canvas, spec)   minimal canvas plotter used by the GUI
 *   PSD.getResults()              current image results as plain arrays (for your own graphing)
 *   PSD.getCumulativeResults()    pooled results of all images added to Cumulative
 *   PSD.onResults = fn(result)    optional callback with whichever result is shown
 *                                 (result.source is 'image' or 'combined')
 *   PSD.init()                    binds the GUI (called automatically if #psd-app exists)
 *
 * Method
 *   1. Grey = 0.299R + 0.587G + 0.114B. A pixel is "particle" if grey <= threshold and it lies
 *      inside the centred ellipse (region of interest, ROI).
 *   2. Particles are 8-connected components. Optional separation of touching particles uses a
 *      distance-transform watershed: exact Euclidean distance transform (Felzenszwalb & Huttenlocher),
 *      pixels flooded from the highest distance downwards with union-find. Two basins meeting at
 *      a saddle of distance s stay separate only if s < neckRatio * (smaller peak) and the smaller
 *      peak stands >= 1 px above the saddle; otherwise they merge. No pixels are removed, so
 *      areas are preserved.
 *   3. Any particle with a pixel on the image edge or adjacent (8-neighbour) to the ellipse
 *      boundary is excluded.
 *   4. Diameter = equivalent circular diameter d = 2*sqrt(A/pi), A in um^2.
 *      um per pixel = (image width in mm * 1000) / image width in pixels (square pixels assumed).
 *   5. Distributions weight each particle by d^0 (number), d^2 (area), d^3 (volume).
 *      Means are the means of those weighted distributions: D[1,0], D[3,2], D[4,3].
 *      D10/D50/D90 are read from the cumulative curve (linear interpolation between particles),
 *      so values read off the plotted cumulative curve agree with the reported numbers.
 *   7. Cumulative (pooled) data: "Add to Cumulative" stores the diameters (um) of every particle in the
 *      current image that does not touch an edge, using that image's own scale and settings.
 *      The size range is applied to the pooled set when it is shown, so it can still be changed.
 *   6. Histograms: equal-width bins in the plotted scale (linear, or log10).
 *      Frequency = % of total weight per bin.
 *      Probability density = fraction per um (linear axis) or per log10 unit (log axis);
 *      it integrates to 1 and does not depend on bin width.
 */
(function (global) {
  'use strict';

  // =====================================================================================
  // Core analysis (no DOM)
  // =====================================================================================

  const EXPONENT = { number: 0, area: 2, volume: 3 };
  const TYPES = ['number', 'area', 'volume'];
  const LOG_AXIS = { min: 10, max: 2000 };
  let fraction = 0 //Added later so used as global
  /** RGBA bytes -> Uint8 grey. */
  function toGray(rgba, nPixels) {
    const g = new Uint8Array(nPixels);
    for (let i = 0, j = 0; i < nPixels; i++, j += 4) {
      g[i] = (rgba[j] * 299 + rgba[j + 1] * 587 + rgba[j + 2] * 114 + 500) / 1000;
    }
    return g;
  }

  /**
   * Centred ellipse as inclusive pixel spans per row: pixel (x,y) is inside if xs[y] <= x <= xe[y].
   * aPct, bPct are % of the half width / half height. Empty rows have xs = W, xe = -1.
   */
  function ellipseSpans(W, H, aPct, bPct, cxPct, cyPct) {
    const cx = W * (cxPct === undefined ? 50 : cxPct) / 100;
    const cy = H * (cyPct === undefined ? 50 : cyPct) / 100;
    const a = (aPct / 100) * (W / 2), b = (bPct / 100) * (H / 2);
    const xs = new Int32Array(H), xe = new Int32Array(H);
    for (let y = 0; y < H; y++) {
      const t = (y + 0.5 - cy) / b;
      if (t < -1 || t > 1) { xs[y] = W; xe[y] = -1; continue; }
      const hw = a * Math.sqrt(1 - t * t);
      let s = Math.ceil(cx - hw - 0.5), e = Math.floor(cx + hw - 0.5);
      if (s < 0) s = 0;
      if (e > W - 1) e = W - 1;
      if (s > e) { s = W; e = -1; }
      xs[y] = s; xe[y] = e;
    }
    return { xs, xe, cx, cy, a, b };
  }

  /** Otsu threshold of grey values inside the ROI. Particle = grey <= returned value. */
  function otsuThreshold(gray, W, H, spans) {
    const hist = new Float64Array(256);
    let total = 0;
    for (let y = 0; y < H; y++) {
      const row = y * W;
      for (let x = spans.xs[y]; x <= spans.xe[y]; x++) hist[gray[row + x]]++;
    }
    let sumAll = 0;
    for (let i = 0; i < 256; i++) { sumAll += i * hist[i]; total += hist[i]; }
    let wB = 0, sumB = 0, best = -1, bestT = 127;
    for (let t = 0; t < 256; t++) {
      wB += hist[t];
      if (wB === 0) continue;
      const wF = total - wB;
      if (wF === 0) break;
      sumB += t * hist[t];
      const mB = sumB / wB, mF = (sumAll - sumB) / wF;
      const v = wB * wF * (mB - mF) * (mB - mF);
      if (v > best) { best = v; bestT = t; }
    }
    return bestT;
  }

  /** 1-D squared distance transform of a sampled function (Felzenszwalb & Huttenlocher 2012). */
  function dt1d(f, n, d, v, z) {
    let k = 0;
    v[0] = 0; z[0] = -Infinity; z[1] = Infinity;
    for (let q = 1; q < n; q++) {
      let s = ((f[q] + q * q) - (f[v[k]] + v[k] * v[k])) / (2 * q - 2 * v[k]);
      while (s <= z[k]) {
        k--;
        s = ((f[q] + q * q) - (f[v[k]] + v[k] * v[k])) / (2 * q - 2 * v[k]);
      }
      k++; v[k] = q; z[k] = s; z[k + 1] = Infinity;
    }
    k = 0;
    for (let q = 0; q < n; q++) {
      while (z[k + 1] < q) k++;
      const dq = q - v[k];
      d[q] = dq * dq + f[v[k]];
    }
  }

  /** Squared Euclidean distance of each foreground pixel (mask[p] < 0) to the nearest background pixel. */
  function edtSquared(mask, W, H) {
    const N = W * H, BIG = 1e20;
    const D = new Float32Array(N);
    for (let i = 0; i < N; i++) D[i] = mask[i] < 0 ? BIG : 0;
    const n = Math.max(W, H);
    const f = new Float64Array(n), d = new Float64Array(n), z = new Float64Array(n + 1), v = new Int32Array(n);
    for (let x = 0; x < W; x++) {
      let any = false;
      for (let y = 0, p = x; y < H; y++, p += W) { f[y] = D[p]; if (f[y] !== 0) any = true; }
      if (!any) continue;
      dt1d(f, H, d, v, z);
      for (let y = 0, p = x; y < H; y++, p += W) D[p] = d[y];
    }
    for (let y = 0; y < H; y++) {
      const o = y * W;
      let any = false;
      for (let x = 0; x < W; x++) { f[x] = D[o + x]; if (f[x] !== 0) any = true; }
      if (!any) continue;
      dt1d(f, W, d, v, z);
      for (let x = 0; x < W; x++) D[o + x] = d[x];
    }
    return D;
  }

  function find(parent, i) {
    while (parent[i] !== i) { parent[i] = parent[parent[i]]; i = parent[i]; }
    return i;
  }

  /**
   * Threshold + label particles.
   * opts: { threshold (0-255), aPct, bPct, split (bool), neckRatio (0-1) }
   * Returns { W, H, labels (Int32Array, 0 = background), count, areaPx (Int32Array, index = label),
   *           touchesEdge (Uint8Array), spans, ms }
   */
  function segment(gray, W, H, opts) {
    const t0 = now();
    const N = W * H;
    const spans = ellipseSpans(W, H, opts.aPct, opts.bPct, opts.cxPct, opts.cyPct);
    const T = opts.threshold;
    const labels = new Int32Array(N);
    let nFg = 0;
    for (let y = 0; y < H; y++) {
      const row = y * W;
      for (let x = spans.xs[y], e = spans.xe[y]; x <= e; x++) {
        if (gray[row + x] <= T) { labels[row + x] = -1; nFg++; }
      }
    }
    const empty = { W, H, labels, count: 0, areaPx: new Int32Array(1), touchesEdge: new Uint8Array(1), spans, ms: 0 };
    if (nFg === 0) { empty.ms = now() - t0; return empty; }

    // Foreground pixels in raster order
    const order = new Int32Array(nFg);
    for (let p = 0, k = 0; p < N; p++) if (labels[p] < 0) order[k++] = p;

    // Union-find over basins. labels: -1 unprocessed, -2 queued, 0 background, >0 basin id + 1.
    const split = !!opts.split;
    const parent = new Int32Array(nFg);
    const peak = split ? new Float32Array(nFg) : null;
    const ratio = +opts.neckRatio || 0, MIN_DEPTH = 1.0;
    let nB = 0;

    // Assign pixel p (distance dp) to the basin of its labelled neighbours. Where several basins meet,
    // pairs that fail the separation criterion are merged; a pixel bordering basins that stay separate
    // goes to the basin holding most of its neighbours (tie: higher peak), which keeps dividing lines
    // central instead of letting one basin creep around the rim of the other.
    // Returns the basin id, or -1 if the pixel has no labelled neighbour.
    const roots = new Int32Array(8), counts = new Int32Array(8);
    function resolve(p, dp) {
      const x = p % W, y = (p - x) / W;
      const x0 = x > 0 ? -1 : 0, x1 = x < W - 1 ? 1 : 0, y0 = y > 0 ? -1 : 0, y1 = y < H - 1 ? 1 : 0;
      let n = 0;
      for (let dy = y0; dy <= y1; dy++) {
        const base = p + dy * W;
        for (let dx = x0; dx <= x1; dx++) {
          const lq = labels[base + dx];
          if (lq <= 0) continue;
          const r = find(parent, lq - 1);
          let i = 0;
          while (i < n && roots[i] !== r) i++;
          if (i === n) { roots[n] = r; counts[n] = 1; n++; } else counts[i]++;
        }
      }
      if (n <= 1) return n ? roots[0] : -1;
      if (!split) {
        for (let i = 1; i < n; i++) parent[roots[i]] = roots[0];
        return roots[0];
      }
      for (let i = 1; i < n; i++) {
        for (let j = 0; j < i; j++) {
          const ri = find(parent, roots[i]), rj = find(parent, roots[j]);
          if (ri === rj) continue;
          const lo = peak[ri] < peak[rj] ? ri : rj, hi = lo === ri ? rj : ri;
          const pl = peak[lo];
          if (!(dp < ratio * pl && pl - dp >= MIN_DEPTH)) parent[lo] = hi;   // merge
        }
      }
      let best = -1, bestCount = 0;
      for (let i = 0; i < n; i++) {
        const r = find(parent, roots[i]);
        let c = 0;
        for (let j = 0; j < n; j++) if (find(parent, roots[j]) === r) c += counts[j];
        if (c > bestCount || (c === bestCount && peak[r] > peak[best])) { best = r; bestCount = c; }
      }
      return best;
    }

    if (!split) {
      // Plain 8-connected component labelling (raster scan).
      for (let k = 0; k < nFg; k++) {
        const p = order[k];
        let cur = resolve(p, 0);
        if (cur < 0) { cur = nB++; parent[cur] = cur; }
        labels[p] = cur + 1;
      }
    } else {
      // Distance-transform watershed. Squared EDT values are exact integers -> bucket by value.
      const sq = edtSquared(labels, W, H);
      const cap = W * W + H * H;
      const keyOf = p => Math.min(Math.round(sq[p]), cap);
      let maxK = 0;
      for (let i = 0; i < nFg; i++) { const k = keyOf(order[i]); if (k > maxK) maxK = k; }
      const pos = new Int32Array(maxK + 2);
      for (let i = 0; i < nFg; i++) pos[maxK - keyOf(order[i]) + 1]++;
      let maxBucket = 0;
      for (let k = 1; k < pos.length; k++) { if (pos[k] > maxBucket) maxBucket = pos[k]; pos[k] += pos[k - 1]; }
      const sorted = new Int32Array(nFg);
      for (let i = 0; i < nFg; i++) { const p = order[i]; sorted[pos[maxK - keyOf(p)]++] = p; }
      // after placement pos[j] = end of bucket j (bucket 0 = largest distance)

      const queue = new Int32Array(maxBucket);
      for (let j = 0; j <= maxK; j++) {
        const a = j === 0 ? 0 : pos[j - 1], b = pos[j];
        if (a === b) continue;
        const level = maxK - j, dp = Math.sqrt(level);
        let qh = 0, qt = 0;
        const pushSameLevelNeighbours = p => {
          const x = p % W, y = (p - x) / W;
          const x0 = x > 0 ? -1 : 0, x1 = x < W - 1 ? 1 : 0, y0 = y > 0 ? -1 : 0, y1 = y < H - 1 ? 1 : 0;
          for (let dy = y0; dy <= y1; dy++) for (let dx = x0; dx <= x1; dx++) {
            const q = p + dy * W + dx;
            if (labels[q] === -1 && keyOf(q) === level) { labels[q] = -2; queue[qt++] = q; }
          }
        };
        const flood = () => {
          while (qh < qt) {
            const p = queue[qh++];
            let cur = resolve(p, dp);
            if (cur < 0) { cur = nB++; parent[cur] = cur; peak[cur] = dp; }
            labels[p] = cur + 1;
            pushSameLevelNeighbours(p);
          }
        };
        // Seed the level with pixels that touch already-labelled (higher) pixels: breadth-first
        // growth within a level avoids a raster-order bias at the dividing lines.
        for (let i = a; i < b; i++) {
          const p = sorted[i];
          const x = p % W, y = (p - x) / W;
          const x0 = x > 0 ? -1 : 0, x1 = x < W - 1 ? 1 : 0, y0 = y > 0 ? -1 : 0, y1 = y < H - 1 ? 1 : 0;
          let has = false;
          for (let dy = y0; dy <= y1 && !has; dy++) for (let dx = x0; dx <= x1; dx++) {
            if (labels[p + dy * W + dx] > 0) { has = true; break; }
          }
          if (has) { labels[p] = -2; queue[qt++] = p; }
        }
        flood();
        // Remaining pixels of this level are new maxima (or plateaus attached to them)
        for (let i = a; i < b; i++) {
          const p = sorted[i];
          if (labels[p] !== -1) continue;
          const c = nB++; parent[c] = c; peak[c] = dp;
          labels[p] = c + 1;
          pushSameLevelNeighbours(p);
          flood();
        }
      }
    }

    // Compact labels 1..count
    const map = new Int32Array(nB);
    let count = 0;
    for (let k = 0; k < nFg; k++) {
      const p = order[k];
      const r = find(parent, labels[p] - 1);
      if (map[r] === 0) map[r] = ++count;
      labels[p] = map[r];
    }

    // Area and edge contact
    const areaPx = new Int32Array(count + 1);
    const touchesEdge = new Uint8Array(count + 1);
    const xs = spans.xs, xe = spans.xe;
    for (let y = 0; y < H; y++) {
      const s = xs[y], e = xe[y];
      if (s > e) continue;
      const row = y * W, yEdge = (y === 0 || y === H - 1);
      for (let x = s; x <= e; x++) {
        const L = labels[row + x];
        if (L === 0) continue;
        areaPx[L]++;
        if (touchesEdge[L]) continue;
        if (yEdge || x === 0 || x === W - 1 || x === s || x === e ||
            x - 1 < xs[y - 1] || x + 1 > xe[y - 1] || x - 1 < xs[y + 1] || x + 1 > xe[y + 1]) {
          touchesEdge[L] = 1;
        }
      }
    }
    return { W, H, labels, count, areaPx, touchesEdge, spans, ms: now() - t0 };
  }

  /**
   * Convert pixel areas to diameters and apply exclusions.
   * category per label: 1 included, 2 touches edge, 3 below dMin, 4 above dMax.
   */
  function measure(seg, umPerPx, dMin, dMax) {
    const k = 2 * umPerPx / Math.sqrt(Math.PI);
    const category = new Uint8Array(seg.count + 1);
    const counts = { segmented: seg.count, touchingEdge: 0, belowMin: 0, aboveMax: 0, included: 0 };
    const list = [];
    for (let L = 1; L <= seg.count; L++) {
      if (seg.touchesEdge[L]) { category[L] = 2; counts.touchingEdge++; continue; }
      const d = k * Math.sqrt(seg.areaPx[L]);
      if (d < dMin) { category[L] = 3; counts.belowMin++; }
      else if (d > dMax) { category[L] = 4; counts.aboveMax++; }
      else { category[L] = 1; list.push(d); }
    }
    const diameters = Float64Array.from(list).sort();
    counts.included = diameters.length;
    return { diameters, category, counts };
  }

  /** Diameters (um) of all particles that do not touch an edge, in label order. */
  function particleDiameters(seg, umPerPx) {
    const k = 2 * umPerPx / Math.sqrt(Math.PI);
    const out = [];
    for (let L = 1; L <= seg.count; L++) if (!seg.touchesEdge[L]) out.push(k * Math.sqrt(seg.areaPx[L]));
    return Float64Array.from(out);
  }

  /** Apply the size range to diameters (any order). Returns sorted included diameters and counts. */
  function applySizeRange(diameters, dMin, dMax) {
    const kept = [];
    let belowMin = 0, aboveMax = 0;
    for (let i = 0; i < diameters.length; i++) {
      const d = diameters[i];
      if (d < dMin) belowMin++; else if (d > dMax) aboveMax++; else kept.push(d);
    }
    return { diameters: Float64Array.from(kept).sort(), belowMin, aboveMax };
  }

  function weightOf(d, exp) { return exp === 0 ? 1 : exp === 2 ? d * d : d * d * d; }

  /** Linear interpolation on a monotone (x, y%) curve. */
  function percentile(x, y, p) {
    for (let k = 1; k < y.length; k++) {
      if (y[k] >= p) {
        const y0 = y[k - 1], y1 = y[k];
        return y1 === y0 ? x[k] : x[k - 1] + (p - y0) / (y1 - y0) * (x[k] - x[k - 1]);
      }
    }
    return x[x.length - 1];
  }

  /**
   * Weighted mean, D10/D50/D90 and cumulative undersize curve for sorted diameters.
   * Cumulative: x = [d1, d1, d2, ..., dn], y = [0, C1, C2, ..., 100] (%).
   */
  function weightedStats(sortedD, exp) {
    const n = sortedD.length;
    if (n === 0) return null;
    let Wt = 0, M = 0;
    const x = new Array(n + 1), y = new Array(n + 1);
    const cum = new Float64Array(n);
    for (let i = 0; i < n; i++) {
      const d = sortedD[i], w = weightOf(d, exp);
      Wt += w; M += w * d; cum[i] = Wt;
    }
    x[0] = sortedD[0]; y[0] = 0;
    for (let i = 0; i < n; i++) { x[i + 1] = sortedD[i]; y[i + 1] = 100 * cum[i] / Wt; }
    y[n] = 100;
    return {
      mean: M / Wt,
      d10: percentile(x, y, 10), d50: percentile(x, y, 50), d90: percentile(x, y, 90),
      cumulative: { x, y }
    };
  }

  /**
   * Histogram of weighted diameters.
   * opts: { lo, hi, nBins, log (bool), density (bool) }
   * Returns { edges, x (bin centres; geometric for log), y, width }
   */
  function histogram(sortedD, exp, opts) {
    const n = Math.max(1, opts.nBins | 0);
    let lo = opts.lo, hi = opts.hi;
    if (!(hi > lo)) hi = lo + 1;
    const log = !!opts.log;
    const L0 = log ? Math.log10(lo) : lo, L1 = log ? Math.log10(hi) : hi;
    const step = (L1 - L0) / n;
    const edges = new Array(n + 1), x = new Array(n), y = new Array(n);
    for (let i = 0; i <= n; i++) { const e = L0 + i * step; edges[i] = log ? Math.pow(10, e) : e; }
    const sums = new Float64Array(n);
    let Wt = 0;
    for (let i = 0; i < sortedD.length; i++) {
      const d = sortedD[i], w = weightOf(d, exp);
      Wt += w;
      if (d < lo || d > hi) continue;
      let idx = Math.floor(((log ? Math.log10(d) : d) - L0) / step);
      if (idx >= n) idx = n - 1;
      if (idx < 0) idx = 0;
      sums[idx] += w;
    }
    for (let i = 0; i < n; i++) {
      const frac = Wt > 0 ? sums[i] / Wt : 0;
      y[i] = opts.density ? frac / step : 100 * frac;     // step is um (linear) or log10 units
      x[i] = log ? Math.sqrt(edges[i] * edges[i + 1]) : 0.5 * (edges[i] + edges[i + 1]);
    }
    return { edges, x, y, width: step };
  }

  /**
   * Everything needed for the plots and the text output, as plain arrays.
   * opts: { dMin, dMax, nBins, log, density }
   */
  function buildPlotData(sortedD, opts) {
    const log = !!opts.log;
    const xMin = log ? LOG_AXIS.min : opts.dMin;
    const xMax = log ? LOG_AXIS.max : opts.dMax;
    const lo = log ? Math.max(opts.dMin, LOG_AXIS.min) : opts.dMin;
    const hi = log ? Math.min(opts.dMax, LOG_AXIS.max) : opts.dMax;
    let notBinned = 0;
    for (let i = 0; i < sortedD.length; i++) if (sortedD[i] < lo || sortedD[i] > hi) notBinned++;
    const out = {
      xScale: log ? 'log' : 'linear', xMin, xMax, binRange: [lo, hi], nBins: opts.nBins,
      yMode: opts.density ? 'density' : 'frequency',
      xLabel: 'Equivalent circular diameter (\u00b5m)',
      yLabel: opts.density
        ? (log ? 'Probability density (per log\u2081\u2080 \u00b5m)' : 'Probability density (\u00b5m\u207b\u00b9)')
        : 'Frequency (%)',
      cumulativeLabel: 'Cumulative undersize (%)',
      notBinned,
      distribution: {}, cumulative: {}, stats: {}
    };
    for (const t of TYPES) {
      const h = histogram(sortedD, EXPONENT[t], { lo, hi, nBins: opts.nBins, log, density: opts.density });
      out.distribution[t] = { x: h.x, y: h.y, edges: h.edges };
      const s = weightedStats(sortedD, EXPONENT[t]);
      out.cumulative[t] = s ? s.cumulative : { x: [], y: [] };
      out.stats[t] = s ? { mean: s.mean, d10: s.d10, d50: s.d50, d90: s.d90 } : null;
    }
    return out;
  }

  function now() { return (typeof performance !== 'undefined' ? performance : Date).now(); }

  // =====================================================================================
  // Minimal chart renderer
  // =====================================================================================

  function niceNum(x) {
    const e = Math.floor(Math.log10(x)), f = x / Math.pow(10, e);
    return (f < 1.5 ? 1 : f < 3 ? 2 : f < 7 ? 5 : 10) * Math.pow(10, e);
  }
  function decimalsFor(step) { return Math.max(0, -Math.floor(Math.log10(step) + 1e-9)); }

  /**
   * spec: { xScale, xMin, xMax, yMin, yMax (optional -> auto), xLabel, yLabel,
   *         series: [{ name, color, dash, width, type: 'step'|'line', x, y, edges }],
   *         guides: [{ y, label }], message }
   */
  function drawChart(canvas, spec) {
    const dpr = global.devicePixelRatio || 1;
    const cssW = canvas.clientWidth, cssH = canvas.clientHeight;
    if (!cssW || !cssH) return;
    canvas.width = Math.round(cssW * dpr); canvas.height = Math.round(cssH * dpr);
    const ctx = canvas.getContext('2d');
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.clearRect(0, 0, cssW, cssH);
    const cs = getComputedStyle(canvas);
    const ink = cs.getPropertyValue('--chart-ink').trim() || '#233036';
    const muted = cs.getPropertyValue('--chart-muted').trim() || '#66737a';
    const grid = cs.getPropertyValue('--chart-grid').trim() || '#e3e7e9';
    const font = cs.fontFamily || 'sans-serif';

    const visible = spec.series.filter(s => s.x && s.x.length);
    let yMin = spec.yMin != null ? spec.yMin : 0, yMax = spec.yMax, yStep;
    if (yMax == null) {
      let mx = 0;
      for (const s of visible) for (const v of s.y) if (v > mx) mx = v;
      if (mx <= 0) mx = 1;
      yStep = niceNum(mx / 5);
      yMax = Math.ceil(mx * 1.04 / yStep) * yStep;
    } else {
      yStep = niceNum((yMax - yMin) / 5);
    }
    const yd = decimalsFor(yStep);
    const yTicks = [];
    for (let v = yMin; v <= yMax + yStep * 1e-6; v += yStep) yTicks.push(v);
    ctx.font = '12px ' + font;
    let labelW = 0;
    for (const v of yTicks) labelW = Math.max(labelW, ctx.measureText(v.toFixed(yd)).width);

    const m = { l: Math.ceil(labelW) + 36, r: 22, t: 34, b: 46 };
    const pw = cssW - m.l - m.r, ph = cssH - m.t - m.b;
    if (pw < 40 || ph < 40) return;
    const log = spec.xScale === 'log';
    const lx0 = log ? Math.log10(spec.xMin) : spec.xMin, lx1 = log ? Math.log10(spec.xMax) : spec.xMax;
    const X = v => m.l + ((log ? Math.log10(Math.max(v, 1e-9)) : v) - lx0) / (lx1 - lx0) * pw;

    const Y = v => m.t + ph - (v - yMin) / (yMax - yMin) * ph;

    ctx.font = '12px ' + font;
    ctx.lineWidth = 1;

    // Y grid + labels
    ctx.textAlign = 'right'; ctx.textBaseline = 'middle';
    for (const v of yTicks) {
      const py = Math.round(Y(v)) + 0.5;
      ctx.strokeStyle = grid; ctx.beginPath(); ctx.moveTo(m.l, py); ctx.lineTo(m.l + pw, py); ctx.stroke();
      ctx.fillStyle = muted; ctx.fillText(v.toFixed(yd), m.l - 7, py);
    }

    // X grid + labels
    ctx.textAlign = 'center'; ctx.textBaseline = 'top';
    const xTick = (v, major, label) => {
      const px = Math.round(X(v)) + 0.5;
      if (px < m.l - 0.5 || px > m.l + pw + 0.5) return;
      ctx.strokeStyle = grid;
      if (major) { ctx.beginPath(); ctx.moveTo(px, m.t); ctx.lineTo(px, m.t + ph); ctx.stroke(); }
      ctx.strokeStyle = muted;
      ctx.beginPath(); ctx.moveTo(px, m.t + ph); ctx.lineTo(px, m.t + ph + (major ? 5 : 3)); ctx.stroke();
      if (label != null) {
        const hw = ctx.measureText(label).width / 2;
        ctx.fillStyle = muted; ctx.fillText(label, Math.min(px, cssW - hw - 1), m.t + ph + 8);
      }
    };
    if (log) {
      const labelled = { 10: 1, 20: 1, 50: 1, 100: 1, 200: 1, 500: 1, 1000: 1 };
      for (let dec = 1; dec <= 1000; dec *= 10) {
        for (let j = 1; j <= 9; j++) {
          const v = j * dec;
          if (v < spec.xMin || v > spec.xMax) continue;
          xTick(v, j === 1, labelled[v] ? String(v) : null);
        }
      }
    } else {
      const step = niceNum((spec.xMax - spec.xMin) / Math.max(3, Math.floor(pw / 80)));
      const xd = decimalsFor(step);
      for (let v = Math.ceil(spec.xMin / step) * step; v <= spec.xMax + step * 1e-6; v += step) {
        xTick(v, true, v.toFixed(xd));
      }
    }

    // Axes frame
    ctx.strokeStyle = muted;
    ctx.beginPath(); ctx.moveTo(m.l + 0.5, m.t); ctx.lineTo(m.l + 0.5, m.t + ph + 0.5); ctx.lineTo(m.l + pw, m.t + ph + 0.5); ctx.stroke();

    // Axis titles
    ctx.fillStyle = ink; ctx.font = '12.5px ' + font;
    ctx.textAlign = 'center'; ctx.textBaseline = 'bottom';
    ctx.fillText(spec.xLabel || '', m.l + pw / 2, cssH - 4);
    ctx.save(); ctx.translate(14, m.t + ph / 2); ctx.rotate(-Math.PI / 2);
    ctx.textBaseline = 'middle'; ctx.fillText(spec.yLabel || '', 0, 0); ctx.restore();

    // Plot area clip
    ctx.save();
    ctx.beginPath(); ctx.rect(m.l, m.t - 2, pw, ph + 3); ctx.clip();

    for (const g of spec.guides || []) {
      ctx.strokeStyle = muted; ctx.setLineDash([2, 4]);
      ctx.beginPath(); ctx.moveTo(m.l, Math.round(Y(g.y)) + 0.5); ctx.lineTo(m.l + pw, Math.round(Y(g.y)) + 0.5); ctx.stroke();
      ctx.setLineDash([]);
    }

    for (const s of visible) {
      ctx.strokeStyle = s.color; ctx.lineWidth = s.width || 2; ctx.setLineDash(s.dash || []);
      ctx.lineJoin = 'round';
      ctx.beginPath();
      if (s.type === 'step') {
        const e = s.edges;
        ctx.moveTo(X(e[0]), Y(0));
        for (let i = 0; i < s.y.length; i++) { ctx.lineTo(X(e[i]), Y(s.y[i])); ctx.lineTo(X(e[i + 1]), Y(s.y[i])); }
        ctx.lineTo(X(e[e.length - 1]), Y(0));
      } else {
        if (s.extend) ctx.moveTo(X(spec.xMin), Y(s.y[0]));
        else ctx.moveTo(X(s.x[0]), Y(s.y[0]));
        for (let i = 0; i < s.x.length; i++) ctx.lineTo(X(s.x[i]), Y(s.y[i]));
        if (s.extend) ctx.lineTo(X(spec.xMax), Y(s.y[s.y.length - 1]));
      }
      ctx.stroke();
    }
    ctx.restore();
    ctx.setLineDash([]);

    // Legend (top, left aligned)
    ctx.font = '12px ' + font; ctx.textAlign = 'left'; ctx.textBaseline = 'middle';
    let lx = m.l;
    for (const s of spec.series) {
      if (!s.x || !s.x.length) continue;
      ctx.strokeStyle = s.color; ctx.lineWidth = s.width || 2; ctx.setLineDash(s.dash || []);
      ctx.beginPath(); ctx.moveTo(lx, 14); ctx.lineTo(lx + 22, 14); ctx.stroke();
      ctx.setLineDash([]);
      ctx.fillStyle = ink; ctx.fillText(s.name, lx + 28, 14);
      lx += 28 + ctx.measureText(s.name).width + 18;
    }

    if (spec.message) {
      ctx.fillStyle = muted; ctx.font = '13px ' + font; ctx.textAlign = 'center';
      ctx.fillText(spec.message, m.l + pw / 2, m.t + ph / 2);
    }
  }

  // =====================================================================================
  // GUI controller
  // =====================================================================================

  const SERIES_STYLE = {
    number: { name: 'Number', color: '#3b63a6', dash: [], width: 2 },
    area:   { name: 'Area',   color: '#b0701c', dash: [7, 4], width: 2 },
    volume: { name: 'Volume', color: '#2d7a58', dash: [], width: 2.5 }
  };

  // Colours of the thresholded view (RGB)
  const VIEW = {
    bg:        [255, 255, 255],
    fg:        [38, 46, 52],     // particle (preview) / included
    edge:      [224, 134, 36],   // touches ellipse or image edge
    small:     [66, 140, 214],   // below min size
    large:     [196, 64, 150],   // above max size
    outBg:     [226, 229, 231],  // outside ellipse, background
    outFg:     [160, 166, 170]   // outside ellipse, particle
  };

  const S = {
    ready: false, img: null, W: 0, H: 0, gray: null, viewData: null, fileName: '',
    seg: null, segKey: '', meas: null, plot: null, result: null,
    lastSegMs: Infinity, timer: 0, rafView: 0, rafResults: 0,
    combined: [], combinedResult: null, clearArmed: false, clearTimer: 0
  };

  const $ = id => document.getElementById(id);
  function params() {
    const p=getParams()
    let pkeys=Object.keys(p)
    let lsString=""
    pkeys.forEach((pkeys)=>{
        if (pkeys=="show"){

        } else {
        lsString+= pkeys +"\t"+ p[pkeys]+"\n";
        }
        })
    localStorage.setItem("PSDsettings",lsString)
    return p
  }

  function getParams() {
    const clamp = (v, lo, hi) => Math.min(hi, Math.max(lo, v));
    let widthMm = parseFloat($('psd-width-mm').value);
    if (!isFinite(widthMm)) widthMm = 25;
    widthMm = clamp(Math.round(widthMm * 10) / 10, 10, 40);

    return {
      widthMm,
      widthUm: widthMm * 1000,
      thresholded: $('psd-show-threshold').checked,
      threshold: +$('psd-threshold').value,
      aPct: +$('psd-ell-a').value,
      bPct: +$('psd-ell-b').value,
      cxPct: +$('psd-ell-cx').value,
      cyPct: +$('psd-ell-cy').value,
      split: $('psd-split').checked,
      neckRatio: +$('psd-neck').value,
      dMin: +$('psd-dmin').value,
      dMax: +$('psd-dmax').value,
      nBins: +$('psd-bins').value,
      log: $('psd-log').checked,
      kde: $('psd-kde').checked,
      density: !$('psd-frequency').checked,
      showCombined: $('psd-show-cumulative').checked,
      show: { number: $('psd-series-number').checked, area: $('psd-series-area').checked, volume: $('psd-series-volume').checked }
    };
  }

  function segKeyOf(p) { return [p.threshold, p.aPct, p.bPct, p.cxPct, p.cyPct, p.split ? 1 : 0, p.split ? p.neckRatio : 0].join('|'); }

  function syncOutputs() {
    const p = params();
    $('psd-threshold-val').value = p.threshold;
    $('psd-ell-a-val').value = p.aPct + ' %';
    $('psd-ell-b-val').value = p.bPct + ' %';
    $('psd-ell-cx-val').value = (+p.cxPct).toFixed(1) + ' %';
    $('psd-ell-cy-val').value = (+p.cyPct).toFixed(1) + ' %';
    $('psd-neck-val').value = p.neckRatio.toFixed(2);
    $('psd-dmin-val').value = p.dMin + ' \u00b5m';
    $('psd-dmax-val').value = p.dMax + ' \u00b5m';
    $('psd-bins-val').value = p.nBins;
    $('psd-neck').disabled = !p.split;
    $('psd-neck-row').classList.toggle('is-disabled', !p.split);
    if (S.img) {
      const um = p.widthUm / S.W;
      $('psd-scale-info').textContent =
        S.W + ' \u00d7 ' + S.H + ' px, ' + fmt(um, 2) + ' \u00b5m per pixel, field ' +
        p.widthMm.toFixed(1) + ' \u00d7 ' + (p.widthMm * S.H / S.W).toFixed(1) + ' mm';
    }
  }

  // ---------- Image loading ----------

  function loadFile(file) {
    if (!file) return;
    const url = URL.createObjectURL(file);
    const img = new Image();
    setStatus('Loading ' + file.name + '\u2026');
    img.onload = () => {
      URL.revokeObjectURL(url);
      const W = img.naturalWidth, H = img.naturalHeight;
      const c = $('psd-image-canvas');
      c.width = W; c.height = H;
      const ctx = c.getContext('2d', { willReadFrequently: false });
      ctx.drawImage(img, 0, 0);
      const data = ctx.getImageData(0, 0, W, H);
      Object.assign(S, {
        img, W, H, fileName: file.name, gray: toGray(data.data, W * H),
        viewData: ctx.createImageData(W, H), seg: null, segKey: '', meas: null, plot: null, result: null,
        lastSegMs: Infinity
      });
      const wrap = $('psd-viewer-frame');
      wrap.style.aspectRatio = W + ' / ' + H;
      wrap.style.width = 'min(100%, calc(74vh * ' + (W / H).toFixed(5) + '))';
      $('psd-app').classList.add('has-image');
      //autoThreshold(false);
      syncOutputs();
      requestView();
      updateResults();
      if (params().thresholded) scheduleAnalysis(30);
      else setStatus('Loaded ' + file.name + '. Tick \u201cThresholded view\u201d to analyse.');
    };
    img.onerror = () => {
      URL.revokeObjectURL(url);
      setStatus('Could not read ' + file.name + '. Use a PNG, JPEG, BMP or WebP image (browsers do not decode most TIFFs).', true);
    };
    img.src = url;
  }

//   function autoThreshold(analyse) {
//     if (!S.img || !analyse) return;
//     const p = params();
//     const t = otsuThreshold(S.gray, S.W, S.H, ellipseSpans(S.W, S.H, p.aPct, p.bPct));
//     $('psd-threshold').value = t;
//     syncOutputs();
//     requestView(); updateResults(); if (p.thresholded) scheduleAnalysis(10);
//   }

  // ---------- Image view ----------

  function requestView() {
    if (S.rafView) return;
    S.rafView = requestAnimationFrame(() => { S.rafView = 0; renderView(); });
  }

  function renderView() {
    if (!S.img) { drawOverlay(); return; }
    const p = params();
    const c = $('psd-image-canvas'), ctx = c.getContext('2d');
    if (!p.thresholded) {
      ctx.drawImage(S.img, 0, 0);
    } else {
      const current = S.seg && S.segKey === segKeyOf(p) && S.meas;
      if (current) renderClassified(); else renderPreview(p);
      ctx.putImageData(S.viewData, 0, 0);
    }
    drawOverlay();
    $('psd-legend').hidden = !p.thresholded;
  }

  function renderPreview(p) {
    const { W, H, gray } = S, out = S.viewData.data, T = p.threshold;
    const sp = ellipseSpans(W, H, p.aPct, p.bPct, p.cxPct, p.cyPct);
    for (let y = 0, p4 = 0; y < H; y++) {
      const s = sp.xs[y], e = sp.xe[y], row = y * W;
      for (let x = 0; x < W; x++, p4 += 4) {
        const inside = x >= s && x <= e, dark = gray[row + x] <= T;
        const col = inside ? (dark ? VIEW.fg : VIEW.bg) : (dark ? VIEW.outFg : VIEW.outBg);
        out[p4] = col[0]; out[p4 + 1] = col[1]; out[p4 + 2] = col[2]; out[p4 + 3] = 255;
      }
    }
  }

  function renderClassified() {
    const { W, H, gray } = S, out = S.viewData.data;
    const { labels, spans } = S.seg, cat = S.meas.category, T = S.seg.threshold;
    const palette = [VIEW.bg, VIEW.fg, VIEW.edge, VIEW.small, VIEW.large];
    for (let y = 0, p4 = 0; y < H; y++) {
      const s = spans.xs[y], e = spans.xe[y], row = y * W;
      for (let x = 0; x < W; x++, p4 += 4) {
        const p = row + x;
        let col;
        if (x < s || x > e) {
          col = gray[p] <= T ? VIEW.outFg : VIEW.outBg;
        } else {
          const L = labels[p];
          if (L === 0) col = VIEW.bg;
          else {
            // separation lines between touching particles shown as background
            const r = x < W - 1 ? labels[p + 1] : 0, d = y < H - 1 ? labels[p + W] : 0;
            col = (r && r !== L) || (d && d !== L) ? VIEW.bg : palette[cat[L]];
          }
        }
        out[p4] = col[0]; out[p4 + 1] = col[1]; out[p4 + 2] = col[2]; out[p4 + 3] = 255;
      }
    }
  }

  function drawOverlay() {
    const ov = $('psd-overlay-canvas');
    const dpr = Math.max(0.5, Math.min(global.devicePixelRatio || 1,
                                       3000 / Math.max(1, ov.clientWidth)));
    const w = ov.clientWidth, h = ov.clientHeight;
    ov.width = Math.max(1, Math.round(w * dpr)); ov.height = Math.max(1, Math.round(h * dpr));
    const ctx = ov.getContext('2d');
    ctx.clearRect(0, 0, ov.width, ov.height);
    if (!S.img || !w) return;
    const p = params();
    const s = ov.width / S.W;
    const cx = S.W * p.cxPct / 100 * s, cy = S.H * p.cyPct / 100 * s,
          a = p.aPct / 100 * S.W / 2 * s, b = p.bPct / 100 * S.H / 2 * s;
    if (!p.thresholded) {
      ctx.fillStyle = 'rgba(18, 24, 28, 0.5)';
      ctx.beginPath(); ctx.rect(0, 0, ov.width, ov.height);
      ctx.moveTo(cx + a, cy);
      ctx.ellipse(cx, cy, a, b, 0, 0, Math.PI * 2);
      ctx.fill('evenodd');
    }
    ctx.beginPath(); ctx.ellipse(cx, cy, a, b, 0, 0, Math.PI * 2);
    ctx.lineWidth = 2 * dpr;
    ctx.strokeStyle = p.thresholded ? 'rgba(31, 111, 139, 0.95)' : 'rgba(120, 220, 255, 0.95)';
    ctx.stroke();
  }

  // ---------- Analysis scheduling ----------

  function scheduleAnalysis(delay) {
    clearTimeout(S.timer);
    if (!S.img || !params().thresholded) return;
    setStatus('Analysing\u2026');
    S.timer = setTimeout(runSegmentation, delay);
  }

  function runSegmentation() {
    const p = params();
    if (!S.img || !p.thresholded) return;
    const key = segKeyOf(p);
    if (key !== S.segKey || !S.seg) {
      const seg = segment(S.gray, S.W, S.H, p);
      seg.threshold = p.threshold;
      S.seg = seg; S.segKey = key; S.lastSegMs = seg.ms;
    }
    updateResults();
    requestView();
    setStatus(S.fileName + ':-    Segmented ' + S.seg.count + ' objects in ' + Math.round(S.seg.ms) + ' ms' +
      (p.split ? ' with separation of touching particles.' : '.'));
  }

  // ---------- Results ----------

  function requestResults() {
    if (S.rafResults) return;
    S.rafResults = requestAnimationFrame(() => { S.rafResults = 0; updateResults(); });
  }

  function isCurrent(p) { return !!(S.seg && S.segKey === segKeyOf(p)); }

  function updateResults() {
    const p = params();
    const app = $('psd-app');
    const current = isCurrent(p);

    // Current image
    if (S.seg) {
      const umPerPx = p.widthUm / S.W;
      S.meas = measure(S.seg, umPerPx, p.dMin, p.dMax);
      S.plot = buildPlotData(S.meas.diameters, p);
      S.result = makeResult(p, umPerPx);
      if (p.thresholded && current) requestView();
    } else {
      S.meas = null; S.plot = null; S.result = null;
    }

    // Cumulative data (always recomputed so the running table follows the size range)
    S.combinedResult = S.combined.length ? makeCombinedResult(p) : null;

    const shown = p.showCombined ? S.combinedResult : S.result;
    let note = '';
      let Below=0, Above=0
      if (shown) {
    for (let i=0; i<shown.diameters.length;i++  ){
      if(shown.diameters[i]<=100) {
        Below+=shown.diameters[i]**3
      } else
      {Above+=shown.diameters[i]**3}
    }
    fraction=(100*Below/(Above+Below)).toFixed(2)+"%"
  }
    if (p.showCombined) {
      if (!S.combined.length) note = 'The Cumulative data is empty. Analyse an image, then choose \u201cAdd to Cumulative\u201d.';
    } else if (!S.img) note = 'Load a microscope image to begin.';
    else if (!S.seg) note = p.thresholded ? 'Analysing\u2026' : 'Tick \u201cThresholded view\u201d to run the analysis.';
    else if (!current) note = p.thresholded
      ? 'Settings changed. Results update when you release the control.'
      : 'Settings changed. Tick \u201cThresholded view\u201d to update the results.';
    $('psd-results-note').textContent = note;
    $('psd-results-note').hidden = !note;
    app.classList.toggle('is-stale', !p.showCombined && !!S.seg && !current);
    app.classList.toggle('has-results', !!shown);
    app.classList.toggle('is-combined', p.showCombined);

    renderStats(shown);
    renderCharts(shown, p);
    renderCombinedTable();
    renderCombinedControls(p);
    if (shown && typeof api.onResults === 'function') {
      try { api.onResults(shown); } catch (e) { console.error(e); }
    }
  }

  function makeResult(p, umPerPx) {
    return {
      source: 'image',
      file: S.fileName,
      image: { widthPx: S.W, heightPx: S.H, widthUm: p.widthUm, umPerPixel: umPerPx },
      settings: {
        threshold: S.seg.threshold, ellipseAPct: p.aPct, ellipseBPct: p.bPct,
        ellipseCxPct: p.cxPct, ellipseCyPct: p.cyPct,
        separateTouching: p.split, neckRatio: p.neckRatio,
        dMinUm: p.dMin, dMaxUm: p.dMax, nBins: p.nBins, logAxis: p.log, yMode: S.plot.yMode
      },
      counts: S.meas.counts,
      diameters: Array.from(S.meas.diameters),
      stats: S.plot.stats,
      plot: S.plot,
    };
  }

  // ---------- Cumulative data (pooled over images) ----------

  function signatureOf(p) {
    return [S.fileName, S.W, S.H, segKeyOf(p), p.widthMm.toFixed(1)].join('|');
  }

  function addToCombined() {
    const p = params();
    if (!S.img || !isCurrent(p)) return;
    const sig = signatureOf(p);
    if (S.combined.some(e => e.signature === sig)) return;
    const umPerPx = p.widthUm / S.W;
    S.combined.push({
      file: S.fileName, signature: sig,
      widthPx: S.W, heightPx: S.H, widthMm: p.widthMm, umPerPixel: umPerPx,
      settings: { threshold: S.seg.threshold, ellipseAPct: p.aPct, ellipseBPct: p.bPct, ellipseCxPct: p.cxPct, ellipseCyPct: p.cyPct, separateTouching: p.split, neckRatio: p.neckRatio },
      segmented: S.seg.count,
      touchingEdge: S.meas.counts.touchingEdge,
      diameters: particleDiameters(S.seg, umPerPx)     // all particles not touching an edge (um)
    });
    const inRange = applySizeRange(S.combined[S.combined.length - 1].diameters, p.dMin, p.dMax).diameters.length;
    setStatus('Added ' + S.fileName + ' to Cumulative as image ' + S.combined.length + ' (' + inRange + ' particles in range).');
    updateResults();
  }

  function removeFromCombined(index) {
    const e = S.combined[index];
    if (!e) return;
    S.combined.splice(index, 1);
    setStatus('Removed ' + e.file + ' from Cumulative.');
    updateResults();
  }

  function clearCombined() {
    const btn = $('psd-clear-cumulative');
    if (!S.clearArmed) {
      S.clearArmed = true;
      btn.textContent = 'Confirm clear';
      btn.classList.add('is-armed');
      clearTimeout(S.clearTimer);
      S.clearTimer = setTimeout(disarmClear, 4000);
      return;
    }
    disarmClear();
    const n = S.combined.length;
    S.combined = [];
    setStatus('Cleared Cumulative (' + n + ' image' + (n === 1 ? '' : 's') + ' removed).');
    updateResults();
  }

  function disarmClear() {
    S.clearArmed = false;
    clearTimeout(S.clearTimer);
    const btn = $('psd-clear-cumulative');
    btn.textContent = 'Clear Cumulative';
    btn.classList.remove('is-armed');
  }

  /** Pool the first `upTo` entries, apply the current size range. */
  function poolEntries(upTo, p) {
    const n = Math.min(upTo, S.combined.length);
    let total = 0;
    for (let i = 0; i < n; i++) total += S.combined[i].diameters.length;
    const all = new Float64Array(total);
    for (let i = 0, o = 0; i < n; i++) { all.set(S.combined[i].diameters, o); o += S.combined[i].diameters.length; }
    return applySizeRange(all, p.dMin, p.dMax);
  }

  function makeCombinedResult(p) {
    const pooled = poolEntries(S.combined.length, p);
    const plot = buildPlotData(pooled.diameters, p);
    let segmented = 0, touchingEdge = 0;
    const images = S.combined.map((e, i) => {
      segmented += e.segmented; touchingEdge += e.touchingEdge;
      const own = applySizeRange(e.diameters, p.dMin, p.dMax);
      const run = poolEntries(i + 1, p);
      const d50 = (arr, exp) => { const s = weightedStats(arr, exp); return s ? s.d50 : null; };
      return {
        index: i + 1, file: e.file, widthPx: e.widthPx, heightPx: e.heightPx, widthMm: e.widthMm,
        umPerPixel: e.umPerPixel, settings: e.settings,
        counts: { segmented: e.segmented, touchingEdge: e.touchingEdge, belowMin: own.belowMin, aboveMax: own.aboveMax, included: own.diameters.length },
        d50Number: d50(own.diameters, 0), d50Volume: d50(own.diameters, 3),
        running: { included: run.diameters.length, d50Number: d50(run.diameters, 0), d50Volume: d50(run.diameters, 3) }
      };
    });
    return {
      source: 'combined',
      images,
      settings: { dMinUm: p.dMin, dMaxUm: p.dMax, nBins: p.nBins, logAxis: p.log, yMode: plot.yMode },
      counts: { images: images.length, segmented, touchingEdge, belowMin: pooled.belowMin, aboveMax: pooled.aboveMax, included: pooled.diameters.length },
      diameters: Array.from(pooled.diameters),
      stats: plot.stats,
      plot,
    };
  }

  function renderCombinedControls(p) {
    const n = S.combined.length;
    const R = S.combinedResult;
    $('psd-cumulative-summary').textContent = n
      ? n + ' image' + (n === 1 ? '' : 's') + ', ' + R.counts.included + ' particles in range'
      : 'Cumulative is empty';
    $('psd-clear-cumulative').disabled = n === 0;
    if (n === 0 && S.clearArmed) disarmClear();

    let canAdd = false, hint = '';
    if (!S.img) hint = 'Load and analyse an image to add it.';
    else if (!S.seg) hint = 'Analyse this image (thresholded view) before adding it.';
    else if (!isCurrent(p)) hint = 'Settings changed. Update the analysis before adding.';
    else {
      const sig = signatureOf(p);
      const same = S.combined.findIndex(e => e.signature === sig);
      const sameFile = S.combined.findIndex(e => e.file === S.fileName && e.widthPx === S.W && e.heightPx === S.H);
      if (same >= 0) hint = 'This analysis is already in Cumulative as image ' + (same + 1) + '.';
      else {
        canAdd = true;
        if (sameFile >= 0) hint = S.fileName + ' is already image ' + (sameFile + 1) + ' (different settings). Adding it again counts its particles twice.';
        else if (S.result) hint = S.result.counts.included + ' particles in range will be added.';
      }
    }
    $('psd-add-cumulative').disabled = !canAdd;
    $('psd-add-hint').textContent = hint;
    $('psd-add-hint').classList.toggle('is-warning', canAdd && hint.indexOf('twice') >= 0);
  }

  function renderCombinedTable() {
    const section = $('psd-pool-section');
    const body = $('psd-pool-body');
    const R = S.combinedResult;
    section.hidden = !R;
    body.innerHTML = '';
    if (!R) return;
    for (const im of R.images) {
      const tr = document.createElement('tr');
      const cells = [
        String(im.index),
        null,
        String(im.counts.included), fmt(im.d50Number, 0), fmt(im.d50Volume, 0),
        String(im.running.included), fmt(im.running.d50Number, 0), fmt(im.running.d50Volume, 0)
      ];
      cells.forEach((c, k) => {
        const td = document.createElement(k === 1 ? 'th' : 'td');
        if (k === 1) {
          td.scope = 'row';
          td.textContent = im.file;
          td.title = im.file + '\nwidth ' + im.widthMm.toFixed(1) + ' mm, threshold ' + im.settings.threshold +
            ', ellipse ' + im.settings.ellipseAPct + ' % \u00d7 ' + im.settings.ellipseBPct + ' %' +
            (im.settings.separateTouching ? ', separation ' + im.settings.neckRatio.toFixed(2) : ', no separation');
        } else td.textContent = c;
        if (k >= 5) td.className = 'psd-running';
        tr.appendChild(td);
      });
      const td = document.createElement('td');
      const btn = document.createElement('button');
      btn.type = 'button'; btn.className = 'psd-button psd-button-small'; btn.textContent = 'Remove';
      btn.setAttribute('aria-label', 'Remove image ' + im.index + ' (' + im.file + ') from Cumulative');
      btn.addEventListener('click', () => removeFromCombined(im.index - 1));
      td.appendChild(btn);
      tr.appendChild(td);
      body.appendChild(tr);
    }
  }

  function fmt(v, dp) { return v == null || !isFinite(v) ? '\u2013' : v.toFixed(dp); }

  function renderStats(r) {
    const body = $('psd-stats-body');
    $('psd-n').textContent = r ? r.counts.included : '\u2013';
    $('psd-n-suffix').textContent = r && r.source === 'combined'
      ? ' from ' + r.counts.images + ' image' + (r.counts.images === 1 ? '' : 's') + ' (Cumulative)'
      : '';
    $('psd-counts').textContent = r
      ? 'of ' + r.counts.segmented + ' objects found: ' + r.counts.touchingEdge + ' touch an edge, ' +
        r.counts.belowMin + ' below ' + r.settings.dMinUm + ' \u00b5m, ' +
        r.counts.aboveMax + ' above ' + r.settings.dMaxUm + ' \u00b5m' +", Fines = "+ fraction
      : '';
    const rows = [
      ['number', 'Number', 'D[1,0]'],
      ['area', 'Area', 'D[3,2]'],
      ['volume', 'Volume', 'D[4,3]']
    ];
    body.innerHTML = '';
    for (const [key, label, sym] of rows) {
      const s = r && r.stats[key];
      const tr = document.createElement('tr');
      tr.innerHTML =
        '<th scope="row"><span class="psd-swatch psd-swatch-' + key + '"></span>' + label + '</th>' +
        '<td>' + fmt(s && s.mean, 0) + ' <span class="psd-sym">' + sym + '</span></td>' +
        '<td>' + fmt(s && s.d10, 0) + '</td>' +
        '<td class="psd-d50">' + fmt(s && s.d50, 0) + '</td>' +
        '<td>' + fmt(s && s.d90, 0) + '</td>';
      body.appendChild(tr);
    }
    $('psd-export').disabled = !r || !r.counts.included;
    $('psd-export').textContent = r && r.source === 'combined' ? 'Export Cumulative CSV' : 'Export CSV';
  }

  function renderCharts(r, p) {
    p = p || params();
    const plot = r && r.plot;
    const distCanvas = $('psd-chart-dist'), cumCanvas = $('psd-chart-cum');
    const empty = !plot || r.diameters.length === 0;
    const axis = plot || {
      xScale: p.log ? 'log' : 'linear', xMin: p.log ? LOG_AXIS.min : p.dMin, xMax: p.log ? LOG_AXIS.max : p.dMax,
      xLabel: 'Equivalent circular diameter (\u00b5m)', yLabel: p.density ? 'Probability density' : 'Frequency (%)',
      cumulativeLabel: 'Cumulative undersize (%)'
    };
    const msg = !r ? (p.showCombined ? 'Cumulative is empty' : !S.img ? 'No image loaded' : 'No analysis yet')
      : empty ? 'No particles in range' : null;
    const distSeries = [], cumSeries = [];
    for (const t of TYPES) {
      if (!p.show[t] || empty) continue;
      const st = SERIES_STYLE[t];

//We add the KDE stuff here - inelegant but direct
const kdeMode=p.kde
if (kdeMode){
let Bins=[],Vals=[]
for (let i=0;i<plot.distribution[t].x.length;i++){
    Bins.push(plot.distribution[t].x[i])
    Vals.push(plot.distribution[t].y[i])
}
// 2. Compute Statistics
const totalWeight = Vals.reduce((sum, val) => sum + val, 0);
const weightedMean = Bins.reduce((sum, bin, i) => sum + bin * Vals[i], 0) / totalWeight;
const weightedVariance = Bins.reduce((sum, bin, i) => sum + Vals[i] * Math.pow(bin - weightedMean, 2), 0) / totalWeight;
const weightedStd = Math.sqrt(weightedVariance);
const n = Bins.length;

// 3. Bandwidth (h) Options Dashboard
const hSilverman = 1.06 * weightedStd * Math.pow(n, -0.2);
const hScott = 1.059 * weightedStd * Math.pow(n, -0.2); 
const manualFactor = 0.5; // Your tweak factor to bring out sub-peaks

const strategy = 'TUNED_SCOTT'; 

let h;
switch(strategy) {
    case 'SILVERMAN':
        h = hSilverman;
        break;
    case 'SCOTT':
        h = hScott;
        break;
    case 'TUNED_SILVERMAN':
        h = hSilverman * manualFactor;
        break;
    case 'TUNED_SCOTT':
        h = hScott * manualFactor; // Resolves to ~87.4, right in your sweet spot
        break;
}

// 4. Standard Gaussian Kernel Function
function gaussianKernel(u) {
    return Math.exp(-0.5 * u * u) / Math.sqrt(2 * Math.PI);
}

// 5. Generate evaluation points from min to max in steps of 10
const kdeData = [];
const startX = Bins[0];
const endX = Bins[Bins.length-1];
const step = 10;
for (let x = startX; x <= endX; x += step) {
    let weightedKernelSum = 0;
    
    for (let i = 0; i < Bins.length; i++) {
        const xi = Bins[i];
        const wi = Vals[i];
        const u = (x - xi) / h;
        weightedKernelSum += wi * gaussianKernel(u);
    }
    
    const density = weightedKernelSum / (h * totalWeight);
    kdeData.push({ x: x, y: density });
}
for (let i=0;i<kdeData.length;i++){
    plot.distribution[t].x[i]=kdeData[i].x
    plot.distribution[t].y[i]=kdeData[i].y
}
}
     const distType=kdeMode? 'line':'step'
      distSeries.push(Object.assign({ type: distType, x: plot.distribution[t].x, y: plot.distribution[t].y, edges: plot.distribution[t].edges }, st));
      cumSeries.push(Object.assign({ type: 'line', extend: true, x: plot.cumulative[t].x, y: plot.cumulative[t].y }, st));
    }
    drawChart(distCanvas, {
      xScale: axis.xScale, xMin: axis.xMin, xMax: axis.xMax, xLabel: axis.xLabel, yLabel: axis.yLabel,
      series: distSeries, message: msg
    });
    drawChart(cumCanvas, {
      xScale: axis.xScale, xMin: axis.xMin, xMax: axis.xMax, yMin: 0, yMax: 100,
      xLabel: axis.xLabel, yLabel: axis.cumulativeLabel, series: cumSeries,
      guides: empty ? [] : [{ y: 50 }], message: msg
    });
    const noteEl = $('psd-dist-note');
    if (plot && plot.notBinned > 0 && plot.xScale === 'log') {
      noteEl.textContent = plot.notBinned + ' included particle(s) lie outside the 10\u20131500 \u00b5m log axis and are not drawn in the histogram (they are included in all statistics).';
      noteEl.hidden = false;
    } else noteEl.hidden = true;
  }

  function renderShownCharts() {
    const p = params();
    renderCharts(p.showCombined ? S.combinedResult : S.result, p);
  }

  // ---------- CSV export (exports whatever is shown: current image or Cumulative) ----------

  function exportCsv() {
    const p = params();
    const r = p.showCombined ? S.combinedResult : S.result;
    if (!r) return;
    const q = v => (v == null ? '' : typeof v === 'number' ? (Number.isInteger(v) ? String(v) : String(parseFloat(v.toPrecision(6)))) : '"' + String(v).replace(/"/g, '""') + '"');
    const L = [];
    const combined = r.source === 'combined';
    L.push(combined ? 'Coffee particle size analysis: Cumulative data' : 'Coffee particle size analysis');
    if (!combined) {
      L.push('File,' + q(r.file));
      L.push('Image (px),' + r.image.widthPx + ',' + r.image.heightPx);
      L.push('Image width (um),' + q(r.image.widthUm));
      L.push('um per pixel,' + q(r.image.umPerPixel));
      const s = r.settings;
      L.push('Threshold,' + s.threshold);
      L.push('Ellipse a (%),' + s.ellipseAPct + ',Ellipse b (%),' + s.ellipseBPct +
             ',Centre x (%),' + s.ellipseCxPct + ',Centre y (%),' + s.ellipseCyPct);
      L.push('Separate touching,' + (s.separateTouching ? 'yes' : 'no') + ',Neck ratio,' + s.neckRatio);
    } else {
      L.push('Images,' + r.counts.images);
    }
    L.push('Size range (um),' + r.settings.dMinUm + ',' + r.settings.dMaxUm);
    L.push('Objects found,' + r.counts.segmented + ',Touching edge,' + r.counts.touchingEdge +
      ',Below min,' + r.counts.belowMin + ',Above max,' + r.counts.aboveMax + ',Included,' + r.counts.included);
    L.push('');
    if (combined) {
      L.push('Image #,File,Width (px),Height (px),Width (mm),um per pixel,Threshold,Ellipse a (%),Ellipse b (%),Separate touching,Neck ratio,' +
        'Objects found,Touching edge,Included,D50 number (um),D50 volume (um),Running included,Running D50 number (um),Running D50 volume (um)');
      for (const im of r.images) {
        const s = im.settings;
        L.push([im.index, q(im.file), im.widthPx, im.heightPx, q(im.widthMm), q(im.umPerPixel), s.threshold, s.ellipseAPct, s.ellipseBPct,
          s.separateTouching ? 'yes' : 'no', q(s.neckRatio), im.counts.segmented, im.counts.touchingEdge, im.counts.included,
          q(im.d50Number), q(im.d50Volume), im.running.included, q(im.running.d50Number), q(im.running.d50Volume)].join(','));
      }
      L.push('');
    }
    L.push('Distribution,Mean (um),Mean type,D10 (um),D50 (um),D90 (um)');
    const sym = { number: 'D[1,0]', area: 'D[3,2]', volume: 'D[4,3]' };
    for (const t of TYPES) {
      const st = r.stats[t];
      if (st) L.push([t, q(st.mean), sym[t], q(st.d10), q(st.d50), q(st.d90)].join(','));
    }
    L.push('');
    L.push('Histogram (' + r.plot.xScale + ' bins),' + r.plot.yLabel);
    L.push('Bin low (um),Bin high (um),Bin centre (um),Number,Area,Volume');
    const dn = r.plot.distribution;
    for (let i = 0; i < dn.number.x.length; i++) {
      L.push([q(dn.number.edges[i]), q(dn.number.edges[i + 1]), q(dn.number.x[i]), q(dn.number.y[i]), q(dn.area.y[i]), q(dn.volume.y[i])].join(','));
    }
    L.push('');
    L.push('Included particles (sorted),Cumulative undersize (%)');
    const c = r.plot.cumulative;
    if (combined) {
      // image number for each particle, in the same sorted order
      const pairs = [];
      S.combined.forEach((e, i) => { for (const d of e.diameters) if (d >= p.dMin && d <= p.dMax) pairs.push([d, i + 1]); });
      pairs.sort((a, b) => a[0] - b[0]);
      L.push('Diameter (um),Image #,Number,Area,Volume');
      for (let i = 0; i < pairs.length; i++) {
        L.push([q(pairs[i][0]), pairs[i][1], q(c.number.y[i + 1]), q(c.area.y[i + 1]), q(c.volume.y[i + 1])].join(','));
      }
    } else {
      L.push('Diameter (um),Number,Area,Volume');
      for (let i = 0; i < r.diameters.length; i++) {
        L.push([q(r.diameters[i]), q(c.number.y[i + 1]), q(c.area.y[i + 1]), q(c.volume.y[i + 1])].join(','));
      }
    }
    const blob = new Blob(['\ufeff' + L.join('\r\n')], { type: 'text/csv;charset=utf-8' });
    saveTextFile(blob)
    // const a = document.createElement('a');
    // a.href = URL.createObjectURL(blob);
    // a.download = combined ? 'cumulative_' + r.counts.images + '_images_psd.csv'
    //   : (r.file || 'image').replace(/\.[^.]+$/, '') + '_psd.csv';
    // document.body.appendChild(a); a.click(); a.remove();
    // setTimeout(() => URL.revokeObjectURL(a.href), 1000);
  }
async function saveTextFile(theText) {
    // Prompt the user for a file location and name
    try {
 const now=new String(new Date(Date.now())).slice(4, 24)

        const handle = await window.showSaveFilePicker({
            suggestedName: now,
            types: [{ description: "CSV Files", accept: { "text/plain": [".csv"] } }]
        });
        const writable = await handle.createWritable();
        await writable.write(theText);
        await writable.close();
    } catch { }
}

  function setStatus(text, isError) {
    const el = $('psd-status');
    if (!el) return;
    el.textContent = text;
    el.classList.toggle('is-error', !!isError);
  }

  // ---------- Binding ----------

  function init() {
    if (S.ready || !$('psd-app')) return;
    S.ready = true;
    //Get saved values
    const lsString=localStorage.getItem("PSDsettings")
    if (lsString){
        //Inelegant code
        const theStrings=lsString.split("\n")
        for (let i=0; i<theStrings.length-1; i++){
            const pair=theStrings[i].split("\t")
            if (pair[0]=="widthMm") $('psd-width-mm').value=pair[1]
             if (pair[0]=="thresholded") $('psd-show-threshold').checked=pair[1]=="true"
             if (pair[0]=="threshold") $('psd-threshold').value=pair[1]
            if (pair[0]=="aPct") $('psd-ell-a').value=pair[1]
            if (pair[0]=="bPct") $('psd-ell-b').value=pair[1]
            if (pair[0]=="cxPct") $('psd-ell-cx').value=pair[1]
            if (pair[0]=="cyPct") $('psd-ell-cy').value=pair[1]
            if (pair[0]=="split") $('psd-split').checked=pair[1]=="true"
            if (pair[0]=="neckRatio") $('psd-neck').value=pair[1]
            if (pair[0]=="dMin") $('psd-dmin').value=pair[1]
            if (pair[0]=="dMax") $('psd-dmax').value=pair[1]
            if (pair[0]=="nBins") $('psd-bins').value=pair[1]
            if (pair[0]=="log") $('psd-log').checked=pair[1]=="true"
            if (pair[0]=="kde") $('psd-kde').checked=pair[1]=="true"
           if (pair[0]=="density") $('psd-frequency').checked=!pair[1]=="true"
            if (pair[0]=="showCombined") $('psd-show-cumulative').checked=pair[1]=="true"
            // if (pair[0]=="show"){
            //     console.log(pair[1])
            // }
   }
    } 

    const fileInput = $('psd-file');
    fileInput.addEventListener('change', () => loadFile(fileInput.files[0]));
    const drop = $('psd-viewer');
    drop.addEventListener('dragover', e => { e.preventDefault(); drop.classList.add('is-drop'); });
    drop.addEventListener('dragleave', () => drop.classList.remove('is-drop'));
    drop.addEventListener('drop', e => {
      e.preventDefault(); drop.classList.remove('is-drop');
      const f = e.dataTransfer.files && e.dataTransfer.files[0];
      if (f) loadFile(f);
    });

    // Scale: cheap update
    $('psd-width-mm').addEventListener('change', () => {
      $('psd-width-mm').value = params().widthMm.toFixed(1);
      syncOutputs(); updateResults();
    });

    // View toggle
    $('psd-show-threshold').addEventListener('change', () => {
      syncOutputs(); requestView(); updateResults();
      if (params().split) scheduleAnalysis(20);
      else { clearTimeout(S.timer); if (S.img) setStatus('Original view. No analysis is performed while this view is shown.'); }
    });

    // Controls that require re-segmentation
    for (const id of ['psd-threshold', 'psd-ell-a', 'psd-ell-b', 'psd-ell-cx', 'psd-ell-cy', 'psd-neck']) {
      const el = $(id);
      el.addEventListener('input', () => {
        syncOutputs(); requestView(); updateResults();
        if (S.lastSegMs < 60) scheduleAnalysis(0);        // fast images update live
      });
      el.addEventListener('change', () => scheduleAnalysis(10));
    }
    $('psd-split').addEventListener('change', () => { syncOutputs(); requestView(); updateResults(); scheduleAnalysis(10); });

    // Cheap controls: re-measure and re-plot only
    for (const id of ['psd-dmin', 'psd-dmax', 'psd-bins']) {
      $(id).addEventListener('input', () => { syncOutputs(); requestResults(); });
    }
    for (const id of ['psd-log','psd-kde', 'psd-frequency', 'psd-series-number', 'psd-series-area', 'psd-series-volume']) {
      $(id).addEventListener('change', () => { syncOutputs(); updateResults(); });
    }
    $('psd-export').addEventListener('click', exportCsv);
    $('psd-add-cumulative').addEventListener('click', addToCombined);
    $('psd-clear-cumulative').addEventListener('click', clearCombined);
    $('psd-show-cumulative').addEventListener('change', () => updateResults());

    if (typeof ResizeObserver !== 'undefined') {
      new ResizeObserver(() => drawOverlay()).observe($('psd-viewer-frame'));
      const ro = new ResizeObserver(() => renderShownCharts());
      ro.observe($('psd-chart-dist')); ro.observe($('psd-chart-cum'));
    } else {
      global.addEventListener('resize', () => { drawOverlay(); renderShownCharts(); });
    }

    syncOutputs();
    updateResults();
  }

  const api = {
    core: { toGray, ellipseSpans, otsuThreshold, edtSquared, segment, measure, particleDiameters, applySizeRange,
            weightedStats, histogram, buildPlotData, percentile },
    drawChart,
    init,
    loadFile,
    getResults: () => S.result,                 // current image
    getCumulativeResults: () => S.combinedResult, // pooled images (null if empty)
    onResults: null
  };
  global.PSD = api;
  if (typeof module !== 'undefined' && module.exports) module.exports = api;

  if (typeof document !== 'undefined') {
    if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', init);
    else init();
  }
})(typeof window !== 'undefined' ? window : globalThis);