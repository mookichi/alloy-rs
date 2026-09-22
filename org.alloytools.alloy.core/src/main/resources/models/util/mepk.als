module util/mepk

/*
 * Symbolic error-tracking real numbers: (m, e, p, k) format.
 *
 * Theory: mepk_formal.md -- each value carries centre c = m * 2^lsb
 * with lsb = e - p + 1 and guaranteed radius R = 2^(e - p + k),
 * i.e. soundness |x - c| <= R (structural induction over §3-§5).
 *
 * Encoding notes (Phase C: library-first, no grammar/Kodkod changes):
 *  - Values are ordinary atoms (sig Mepk), operations are preds relating
 *    inputs to a result atom. Funs cannot synthesise fresh atoms in Alloy.
 *  - Only exponent-level relations are asserted (integer comparisons on
 *    e/p/k). The exact centre computation (round_to_precision, guard-bit
 *    integer division) is delegated to the Java oracle MepkOps; the Alloy
 *    side states the SOUND upper bound (k'), never a tighter claim.
 *  - 2^(...) is never computed (would overflow the fixed bitwidth Int);
 *    compare exponents instead (§6 of the theory).
 *  - Division precondition k2 < p2 is a GUARD: a model violating it is
 *    UNSAT by construction (fact-gated), per user decision. This catches
 *    the "denominator may span zero" singularity (§5).
 *  - CEGAR: tau = p - k - g; needsRefine when k >= p or tau <= 0 (§7).
 *  - Sum many values with pairwise (binary-tree) accumulation, NOT
 *    sequential: sequential k grows with N, pairwise with O(log N).
 */

// ---- core carrier ------------------------------------------------------

sig Mepk { m, e, p, k: Int }

// ---- primitives (§2) ----------------------------------------------------

// max(A - B, 0): non-negative part of the difference
fun maxDiff[A, B: Int]: Int {
  (minus[A, B] < 0 => 0 else minus[A, B])
}

// combine_k(A,B) = max(A-B,0) + 1 ; guarantees 2^A + 2^B <= 2^(B + combine_k)
fun combineK[A, B: Int]: Int {
  plus[maxDiff[A, B], 1]
}

fun lsb[x: Mepk]: Int { plus[minus[x.e, x.p], 1] }

// radius exponent: R = 2^(e - p + k); compare these, never 2^(...)
fun radiusExp[x: Mepk]: Int { plus[minus[x.e, x.p], x.k] }

// target-guarantee bits: tau = p - k - g (§7)
fun accuracyTau[x: Mepk, g: Int]: Int { minus[minus[x.p, x.k], g] }

pred wellformed[x: Mepk] {
  x.p > 0
  x.k >= 0
  // zero is represented with m = 0 (exponent unconstrained); nonzero needs range
  x.m != 0 => x.e >= lsb[x]
}

pred divGuard[d: Mepk] { d.k < d.p }

pred precisionLost[x: Mepk, g: Int] {
  x.k >= x.p or accuracyTau[x, g] <= 0
}

pred needsRefine[x: Mepk, g: Int] {
  precisionLost[x, g] or not divGuard[x]
}

// ---- addition / subtraction (§3) ---------------------------------------
// l = min(lsb1, lsb2); d_i = lsb_i - l
// A = l + max(k1 + d1, k2 + d2)   (R1 + R2 exponent bound, Lemma 2 n=2)
// p' = min(p1, p2); B = e' - p'   (rounding error, Lemma 1)
// k' = combine_k(A, B)
// e' shrinks automatically on cancellation, so no separate shift s.

fun addL[a, b: Mepk]: Int {
  (lsb[a] < lsb[b] => lsb[a] else lsb[b])
}

fun addA[a, b: Mepk]: Int {
  let l = addL[a, b] |
  let t1 = plus[a.k, minus[lsb[a], l]] |
  let t2 = plus[b.k, minus[lsb[b], l]] |
    plus[l, (t1 > t2 => t1 else t2)]
}

fun addP[a, b: Mepk]: Int {
  (a.p < b.p => a.p else b.p)
}

pred mepkAdd[a, b, res: Mepk] {
  wellformed[a] and wellformed[b] and wellformed[res]
  res.p = addP[a, b]
  // res.e / res.m are left to the solver (centre depends on rounding);
  // the error exponent is pinned to the sound bound:
  res.k = combineK[addA[a, b], minus[res.e, res.p]]
}

pred mepkSub[a, b, res: Mepk] {
  // identical error propagation to addition (§3: x1 ± x2)
  mepkAdd[a, b, res]
}

// ---- multiplication (§4) ------------------------------------------------
// C = e1 + e2 + max(k1-p1+1, k2-p2+1, k1+k2-p1-p2) + 2  (Lemma 2, n=3)
// B = e' - p'; k' = combine_k(C, B)

fun mulC[a, b: Mepk]: Int {
  let t1 = plus[minus[a.k, a.p], 1] |
  let t2 = plus[minus[b.k, b.p], 1] |
  let t3 = minus[plus[a.k, b.k], plus[a.p, b.p]] |
  let m12 = (t1 > t2 => t1 else t2) |
  let mx = (m12 > t3 => m12 else t3) |
    plus[plus[a.e, b.e], plus[mx, 2]]
}

fun mulP[a, b: Mepk]: Int {
  (a.p < b.p => a.p else b.p)
}

pred mepkMul[a, b, res: Mepk] {
  wellformed[a] and wellformed[b] and wellformed[res]
  res.p = mulP[a, b]
  res.k = combineK[mulC[a, b], minus[res.e, res.p]]
}

// ---- division (§5) -------------------------------------------------------
// D = e1 - e2 + max(k1-p1, k2-p2) + 3
// B = e' - p'; k' = combine_k(D, B)
// REQUIRES divGuard[denominator]; violations are UNSAT (no finite bound
// can absorb a denominator interval spanning zero).

fun divD[a, b: Mepk]: Int {
  let t1 = minus[a.k, a.p] |
  let t2 = minus[b.k, b.p] |
  let mx = (t1 > t2 => t1 else t2) |
    plus[plus[minus[a.e, b.e], mx], 3]
}

fun divP[a, b: Mepk]: Int {
  (a.p < b.p => a.p else b.p)
}

pred mepkDiv[num, den, res: Mepk] {
  wellformed[num] and wellformed[den] and wellformed[res]
  divGuard[den]
  res.p = divP[num, den]
  res.k = combineK[divD[num, den], minus[res.e, res.p]]
}

// ---- worked assertions (solver-backed checks, bitwidth-safe) ------------

// NOTE: exponent arithmetic below is exact mathematics over the fixed-
// bitwidth Int, so run checks with the "Forbid Overflows" option enabled
// (options.noOverflow = true); otherwise plus/minus may wrap and produce
// spurious counterexamples near min/max Int.

assert CombineKBounds {
  // Bounded to a range where minus/plus are exact (no wrap): with
  // bitwidth 5 (Int -16..15), A,B in [-4,4] keeps every intermediate
  // value in [-8,13]. Wider claims need "Forbid Overflows".
  all A, B: Int |
    (A >= -4 and A <= 4 and B >= -4 and B <= 4) implies
      (plus[B, combineK[A, B]] >= A and combineK[A, B] >= 1)
}

assert DivGuardUnsat {
  // contrapositive of the gate: a denominator with k >= p admits NO result
  all num, den: Mepk |
    (wellformed[num] and wellformed[den] and den.k >= den.p) =>
      (no res: Mepk | mepkDiv[num, den, res])
}

assert TauDetectsLoss {
  all x: Mepk, g: Int |
    (wellformed[x] and g >= 0 and x.k >= x.p) => precisionLost[x, g]
}
