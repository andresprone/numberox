/* Numberox engine v1 — original, dependency-free numerical fill-in generator.
 * Browser/Worker: NumberoxEngine; CommonJS: require('./engine.js').
 * Digits are strings, including leading zeroes. slot.value is the answer at
 * that slot, but solvers treat ALL values as an unordered bank, not clues.
 * Only givens constrain the bank. solution is used only as an open-cell mask.
 * countSolutions(p, limit=2, {maxNodes=20000,maxOperations=3000000}={}):
 * cutoff means enumeration stopped at the limit OR a deterministic work budget.
 * Uniqueness is proven ONLY by count === 1 && cutoff === false (limit >= 2).
 * analyze uses singles, then crossing-support elimination, then bounded search.
 * Ratings are estimates of these techniques, not calibrated human difficulty.
 */
(function (root, factory) {
  'use strict';
  var api = factory();
  if (typeof module === 'object' && module.exports) module.exports = api;
  if (root) root.NumberoxEngine = api;
}(typeof globalThis !== 'undefined' ? globalThis : this, function () {
  'use strict';
  var SIZES = {small: {w: 9, h: 9, target: 10, min: 7}, medium: {w: 12, h: 12, target: 18, min: 12}, large: {w: 15, h: 15, target: 28, min: 18}};
  var PROFILES = {easy: {alphabet: 10, fraction: 0.23, attempts: 5}, medium: {alphabet: 5, fraction: 0.13, attempts: 24}, hard: {alphabet: 4, fraction: 0, attempts: 80}};
  var own = function (o, k) { return Object.prototype.hasOwnProperty.call(o, k); };
  function rng(seed) {
    var h = 2166136261;
    for (var i = 0; i < seed.length; i++) h = Math.imul(h ^ seed.charCodeAt(i), 16777619);
    return function () {
      h += 0x6D2B79F5;
      var t = Math.imul(h ^ h >>> 15, 1 | h);
      t ^= t + Math.imul(t ^ t >>> 7, 61 | t);
      return ((t ^ t >>> 14) >>> 0) / 4294967296;
    };
  }
  function shuffle(a, random) {
    for (var i = a.length - 1; i > 0; i--) { var j = Math.floor(random() * (i + 1)), t = a[i]; a[i] = a[j]; a[j] = t; }
    return a;
  }
  function runs(mask, w, h) {
    var result = [];
    for (var axis = 0; axis < 2; axis++) {
      var outer = axis ? w : h, inner = axis ? h : w;
      for (var a = 0; a < outer; a++) {
        var line = [];
        for (var b = 0; b <= inner; b++) {
          var idx = axis ? b * w + a : a * w + b;
          if (b < inner && mask[idx]) line.push(idx);
          else { if (line.length >= 3) result.push({id: (axis ? 'V' : 'H') + (line[0] + 1), cells: line}); line = []; }
        }
      }
    }
    return result;
  }
  function layout(config, random) {
    var w = config.w, h = config.h, best = null;
    for (var trial = 0; trial < 5; trial++) {
      var mask = Array(w * h).fill(false);
      var row = Math.floor(h / 2), start = Math.floor((w - 5) / 2);
      for (var x = start; x < start + 5; x++) mask[row * w + x] = true;
      for (var step = 1; step < config.target; step++) {
        var choices = [];
        for (var axis = 0; axis < 2; axis++) {
          for (var r = 0; r < h; r++) for (var c = 0; c < w; c++) {
            for (var len = 3; len <= 7; len++) {
              var dr = axis, dc = 1 - axis;
              if (r + dr * (len - 1) >= h || c + dc * (len - 1) >= w) break;
              if ((r - dr >= 0 && c - dc >= 0 && mask[(r - dr) * w + c - dc]) ||
                  (r + dr * len < h && c + dc * len < w && mask[(r + dr * len) * w + c + dc * len])) continue;
              var cells = [], crosses = 0, okay = true;
              for (var k = 0; k < len && okay; k++) {
                var rr = r + dr * k, cc = c + dc * k, p = rr * w + cc;
                if (mask[p]) {
                  if ((rr - dr >= 0 && cc - dc >= 0 && mask[(rr - dr) * w + cc - dc]) ||
                      (rr + dr < h && cc + dc < w && mask[(rr + dr) * w + cc + dc])) okay = false;
                  crosses++;
                } else if ((rr - dc >= 0 && cc - dr >= 0 && mask[(rr - dc) * w + cc - dr]) ||
                           (rr + dc < h && cc + dr < w && mask[(rr + dc) * w + cc + dr])) okay = false;
                cells.push(p);
              }
              if (okay && crosses && crosses < len) choices.push({cells: cells, score: crosses * 2 + random() * 3 + (7 - len) * 0.12});
            }
          }
        }
        if (!choices.length) break;
        choices.sort(function (a, b) { return b.score - a.score; });
        choices[0].cells.forEach(function (p) { mask[p] = true; });
      }
      var slots = runs(mask, w, h);
      if (!best || slots.length > best.slots.length) best = {mask: mask, slots: slots};
      if (slots.length >= config.target) break;
    }
    if (best.slots.length < config.min) throw new Error('Layout budget exhausted');
    return best;
  }
  function positiveBudget(value, fallback) {
    if (value === undefined) return fallback;
    if (!Number.isSafeInteger(value) || value < 0) throw new TypeError('Budget must be a nonnegative safe integer');
    return value;
  }
  function budget(options) {
    options = options || {};
    return {nodes: 0, operations: 0, maxNodes: positiveBudget(options.maxNodes, 20000), maxOperations: positiveBudget(options.maxOperations, 3000000), cutoff: false};
  }
  function tick(work, n) {
    work.operations += n || 1;
    if (work.operations > work.maxOperations) { work.cutoff = true; return false; }
    return true;
  }
  // Validate structure, not the hidden answer. Arbitrary unsatisfiable banks and
  // contradictory visible digits are valid solver inputs, not format errors.
  function compile(p) {
    if (!p || !Number.isInteger(p.width) || !Number.isInteger(p.height) || p.width < 1 || p.height < 1 || p.width > 40 || p.height > 40 ||
        !Array.isArray(p.solution) || p.solution.length !== p.width * p.height || !Array.isArray(p.slots) || !p.slots.length || p.slots.length > 100) throw new TypeError('Invalid puzzle dimensions or slots');
    var mask = p.solution.map(function (d) { if (d !== null && (typeof d !== 'string' || !/^\d$/.test(d))) throw new TypeError('Invalid cell'); return d !== null; });
    var expected = runs(mask, p.width, p.height), signatures = new Set(expected.map(function (s) { return s.cells.join(','); }));
    if (expected.length !== p.slots.length) throw new TypeError('Slots must be all maximal runs of length >= 3');
    var values = [], ids = new Set(), seen = new Set(), owners = Array.from({length: mask.length}, function () { return []; });
    p.slots.forEach(function (s, i) {
      if (!s || typeof s.id !== 'string' || ids.has(s.id) || !Array.isArray(s.cells) || !signatures.delete(s.cells.join(',')) ||
          typeof s.value !== 'string' || !/^\d{3,}$/.test(s.value) || s.value.length !== s.cells.length || seen.has(s.value)) throw new TypeError('Invalid or duplicate slot/value');
      ids.add(s.id); seen.add(s.value); values.push(s.value);
      s.cells.forEach(function (cell, pos) { owners[cell].push([i, pos]); });
    });
    for (var k = 0; k < mask.length; k++) if (mask[k] && !owners[k].length) throw new TypeError('Uncovered open cell');
    var givens = p.givens || {};
    Object.keys(givens).forEach(function (key) {
      var n = Number(key);
      if (!Number.isInteger(n) || String(n) !== key || n < 0 || n >= mask.length || !mask[n] || typeof givens[key] !== 'string' || !/^\d$/.test(givens[key])) throw new TypeError('Invalid given');
    });
    var links = Array.from({length: p.slots.length}, function () { return []; });
    owners.forEach(function (o) {
      if (o.length === 2) { links[o[0][0]].push({other: o[1][0], here: o[0][1], there: o[1][1]}); links[o[1][0]].push({other: o[0][0], here: o[1][1], there: o[0][1]}); }
    });
    var domains = p.slots.map(function (s) {
      var d = [];
      values.forEach(function (v, j) { if (v.length === s.cells.length && s.cells.every(function (cell, pos) { return !own(givens, cell) || givens[cell] === v[pos]; })) d.push(j); });
      return d;
    });
    return {values: values, links: links, domains: domains, slots: p.slots, owners: owners};
  }
  function stats() { return {singlesSteps: 0, pruningEliminations: 0, hiddenSingles: 0, rounds: 0}; }
  // Level 0: placing forced words, crossing digits and using each word once.
  // Level 1: also eliminate candidates lacking support in a crossing's domain.
  function propagate(model, domains, level, work, metrics) {
    var changed = true, placed = new Set();
    while (changed) {
      if (!tick(work)) return null;
      changed = false; metrics.rounds++;
      var used = new Map();
      for (var i = 0; i < domains.length; i++) {
        if (!domains[i].length) return false;
        if (domains[i].length === 1) {
          var value = domains[i][0];
          if (used.has(value)) return false;
          used.set(value, i);
          if (!placed.has(i)) { placed.add(i); metrics.singlesSteps++; }
        }
      }
      for (var s = 0; s < domains.length; s++) {
        var before = domains[s];
        var after = [];
        for (var q = 0; q < before.length; q++) {
          var candidate = before[q], valid = !used.has(candidate) || used.get(candidate) === s;
          for (var e = 0; valid && e < model.links[s].length; e++) {
            var link = model.links[s][e], other = domains[link.other];
            if (level === 0 && other.length !== 1) continue;
            var supported = false;
            for (var v = 0; v < other.length; v++) {
              if (!tick(work)) return null;
              if (other[v] !== candidate && model.values[candidate][link.here] === model.values[other[v]][link.there]) { supported = true; break; }
            }
            if (!supported) valid = false;
          }
          if (valid) after.push(candidate);
        }
        if (!after.length) return false;
        if (after.length !== before.length) { changed = true; if (level) metrics.pruningEliminations += before.length - after.length; domains[s] = after; }
      }
      // A bank entry with exactly one possible destination is a hidden single.
      var homes = Array.from({length: model.values.length}, function () { return []; });
      domains.forEach(function (d, slot) { d.forEach(function (v) { homes[v].push(slot); }); });
      for (var a = 0; a < homes.length; a++) {
        if (!homes[a].length) return false;
        if (homes[a].length === 1 && domains[homes[a][0]].length > 1) { domains[homes[a][0]] = [a]; changed = true; metrics.hiddenSingles++; }
      }
    }
    return true;
  }
  function cloneDomains(d) { return d.map(function (a) { return a.slice(); }); }
  function search(model, limit, options, initial) {
    var work = budget(options), count = 0, witnesses = [], maxDepth = 0, limitHit = false;
    function visit(domains, depth) {
      if (work.cutoff || limitHit) return;
      if (++work.nodes > work.maxNodes) { work.cutoff = true; return; }
      maxDepth = Math.max(maxDepth, depth);
      if (propagate(model, domains, 1, work, stats()) !== true) return;
      var selected = -1;
      for (var i = 0; i < domains.length; i++) if (domains[i].length > 1 && (selected < 0 || domains[i].length < domains[selected].length ||
          (domains[i].length === domains[selected].length && model.links[i].length > model.links[selected].length))) selected = i;
      if (selected < 0) { count++; witnesses.push(domains.map(function (d) { return d[0]; })); if (count >= limit) limitHit = true; return; }
      for (var j = 0; j < domains[selected].length && !work.cutoff && !limitHit; j++) {
        var next = cloneDomains(domains); next[selected] = [domains[selected][j]]; visit(next, depth + 1);
      }
    }
    visit(cloneDomains(initial || model.domains), 0);
    return {count: count, cutoff: work.cutoff || limitHit, budgetCutoff: work.cutoff, witnesses: witnesses, nodes: work.nodes, operations: work.operations, maxDepth: maxDepth};
  }
  function countSolutions(puzzle, limit, options) {
    if (limit === undefined) limit = 2;
    if (!Number.isSafeInteger(limit) || limit < 1) throw new TypeError('limit must be a positive safe integer');
    var result = search(compile(puzzle), limit, options);
    return {count: result.count, cutoff: result.cutoff};
  }
  function analyze(puzzle) {
    var model = compile(puzzle), domains = cloneDomains(model.domains), work = budget(), basic = stats(), advanced = stats();
    var initialCandidates = domains.reduce(function (n, d) { return n + d.length; }, 0);
    var initialSingles = domains.filter(function (d) { return d.length === 1; }).length;
    var status = propagate(model, domains, 0, work, basic);
    var singlesSolved = status === true && domains.every(function (d) { return d.length === 1; });
    var singlesResolved = domains.filter(function (d) { return d.length === 1; }).length;
    if (status === true && !singlesSolved) status = propagate(model, domains, 1, work, advanced);
    var pruningSolved = status === true && domains.every(function (d) { return d.length === 1; });
    var unresolved = domains.filter(function (d) { return d.length !== 1; }).length;
    var proof = null;
    if (status === true && !pruningSolved) proof = search(model, 2, undefined, domains);
    var contradiction = status === false || !!(proof && proof.count === 0 && !proof.cutoff);
    var lookahead = proof ? proof.maxDepth : 0;
    var cutoff = work.cutoff || !!(proof && proof.budgetCutoff);
    var solved = !contradiction && (pruningSolved || !!(proof && proof.count === 1 && !proof.cutoff));
    var label = contradiction ? 'invalid' : cutoff ? 'unrated' : singlesSolved ? 'easy' : pruningSolved ? 'medium' : 'hard';
    var givenCells = Object.keys(puzzle.givens || {}).length;
    var givenSlots = puzzle.slots.filter(function (s) { return s.cells.every(function (c) { return own(puzzle.givens || {}, c); }); }).length;
    var openCells = puzzle.solution.filter(function (d) { return d !== null; }).length;
    return {label: label, estimated: true, method: 'singles-crossing-support-bounded-search',
      logicSteps: Math.max(0, domains.filter(function (d) { return d.length === 1; }).length - givenSlots) + basic.hiddenSingles + advanced.hiddenSingles + advanced.pruningEliminations,
      lookahead: lookahead, singlesSolved: singlesSolved, pruningSolved: pruningSolved, solved: solved,
      contradiction: contradiction, cutoff: cutoff, initialCandidates: initialCandidates, initialSingles: initialSingles,
      singlesResolved: singlesResolved, pruningEliminations: advanced.pruningEliminations, hiddenSingles: basic.hiddenSingles + advanced.hiddenSingles,
      unresolved: unresolved, searchNodes: proof ? proof.nodes : 0, givenCells: givenCells, givenSlots: givenSlots,
      openCells: openCells, clueFraction: givenCells / openCells,
      explanation: label === 'easy' ? 'Solved by forced placements and used-number elimination.' : label === 'medium' ? 'Requires testing candidate compatibility at crossings in this solver.' : label === 'hard' ? 'Crossing support stalls; bounded branching is needed or the puzzle is ambiguous.' : 'No complete difficulty assessment.',
      singlesSteps: Math.max(0, singlesResolved - givenSlots)};
  }
  function construct(size, difficulty, seed, random, board) {
    var config = SIZES[size], profile = PROFILES[difficulty];
    var alphabet = difficulty === 'hard' && size === 'small' ? 3 : profile.alphabet;
    var digits = shuffle('0123456789'.split(''), random).slice(0, alphabet);
    var solution, slots, valid = false;
    for (var retry = 0; retry < 200 && !valid; retry++) {
      solution = board.mask.map(function (open) { return open ? digits[Math.floor(random() * digits.length)] : null; });
      slots = board.slots.map(function (s) { return {id: s.id, cells: s.cells.slice(), value: s.cells.map(function (i) { return solution[i]; }).join('')}; });
      valid = new Set(slots.map(function (s) { return s.value; })).size === slots.length;
    }
    if (!valid) return null;
    var p = {version: 1, seed: seed, size: size, difficulty: difficulty, width: config.w, height: config.h, solution: solution, slots: slots, givens: {}, rating: null};
    var order = shuffle(slots.slice(), random);
    // A complete starter word is always visible; its position removes the common
    // transpose/row-column swap ambiguity without pretending IDs are clues.
    order.sort(function (a, b) { return difficulty === 'easy' ? b.cells.length - a.cells.length : a.cells.length - b.cells.length; });
    order[0].cells.forEach(function (c) { p.givens[c] = solution[c]; });
    var cells = shuffle(solution.map(function (d, i) { return d === null ? -1 : i; }).filter(function (i) { return i >= 0; }), random);
    var target = Math.ceil(cells.length * profile.fraction);
    for (var i = 0; Object.keys(p.givens).length < target && i < cells.length; i++) p.givens[cells[i]] = solution[cells[i]];
    var proof, rating;
    for (var pass = 0; pass <= cells.length; pass++) {
      var model = compile(p);
      proof = search(model, 2);
      if (proof.count === 1 && !proof.cutoff) {
        rating = analyze(p);
        if (difficulty !== 'easy' || rating.singlesSolved) break;
      }
      // Prefer a digit which distinguishes a witnessed alternative completion.
      var differences = new Set();
      proof.witnesses.forEach(function (assignment) {
        slots.forEach(function (s, index) { s.cells.forEach(function (cell, pos) { if (model.values[assignment[index]][pos] !== solution[cell]) differences.add(cell); }); });
      });
      var next = cells.find(function (c) { return !own(p.givens, c) && differences.has(c); });
      if (next === undefined && proof.count === 1 && !proof.cutoff && difficulty === 'easy') {
        var stalled = cloneDomains(model.domains), scores = {};
        propagate(model, stalled, 0, budget(), stats());
        stalled.forEach(function (domain, index) {
          domain.forEach(function (v) { slots[index].cells.forEach(function (c, pos) {
            if (!own(p.givens, c) && model.values[v][pos] !== solution[c]) scores[c] = (scores[c] || 0) + 1;
          }); });
        });
        var highest = 0;
        cells.forEach(function (c) { if ((scores[c] || 0) > highest) { highest = scores[c]; next = c; } });
      }
      if (next === undefined) next = cells.find(function (c) { return !own(p.givens, c); });
      if (next === undefined) return null;
      p.givens[next] = solution[next];
    }
    if (!proof || proof.count !== 1 || proof.cutoff) return null;
    if (difficulty === 'hard') {
      cells.forEach(function (c) {
        if (!own(p.givens, c) || order[0].cells.indexOf(c) !== -1) return;
        delete p.givens[c];
        var reduced = search(compile(p), 2);
        if (reduced.count === 1 && !reduced.cutoff) proof = reduced;
        else p.givens[c] = solution[c];
      });
      rating = analyze(p);
    }
    rating = rating || analyze(p);
    rating.uniqueness = 'verified'; rating.uniquenessNodes = proof.nodes; rating.uniquenessCutoff = false;
    rating.requested = difficulty; rating.profile = difficulty === 'easy' ? 'more-clues-singles' : difficulty === 'medium' ? 'fewer-clues-crossing-candidates' : 'minimal-starters-repeated-digits';
    rating.digitAlphabet = digits.length;
    p.rating = rating;
    return p;
  }
  function generate(size, difficulty, seed) {
    if (typeof size !== 'string' || typeof difficulty !== 'string' || !own(SIZES, size) || !own(PROFILES, difficulty) || typeof seed !== 'string') throw new TypeError('Expected size small|medium|large, difficulty easy|medium|hard, and a string seed');
    var random = rng('numberox-v1\u0000' + size + '\u0000' + difficulty + '\u0000' + seed);
    var board = layout(SIZES[size], random), best = null, bestScore = -Infinity;
    for (var attempt = 0; attempt < PROFILES[difficulty].attempts; attempt++) {
      if (attempt && attempt % 12 === 0) board = layout(SIZES[size], random);
      var p = construct(size, difficulty, seed, random, board);
      if (!p) continue;
      var r = p.rating, level = r.label === 'hard' ? 2 : r.label === 'medium' ? 1 : 0;
      var score = (r.label === difficulty ? 1000 : 0) + level * (difficulty === 'easy' ? -100 : 100) - r.clueFraction * 50 + Math.min(20, r.pruningEliminations);
      if (score > bestScore) { best = p; bestScore = score; }
      if (r.label === difficulty) break;
    }
    if (!best) throw new Error('Generation budget exhausted; try a different seed');
    return best;
  }
  return Object.freeze({generate: generate, countSolutions: countSolutions, analyze: analyze});
}));
