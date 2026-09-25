//! Builtin `Real` signature: exact-centre `c = m * 2^e` values over the
//! shared `Real.m`/`Real.e` lanes (`EReal extends Real`), with desugared
//! `real*` operation predicates (exact arithmetic, no rounding) and
//! `setReal` (dyadic literals only).

use alloy_front_rs::{parse_module, run, solve};

fn sat(src: &str) {
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("run");
    assert!(solve(&cnf).expect("solve").is_some(), "expected SAT: {src}");
}

fn unsat(src: &str) {
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("run");
    assert!(
        solve(&cnf).expect("solve").is_none(),
        "expected UNSAT: {src}"
    );
}

fn build_err(src: &str, want: &str) {
    let m = parse_module(src).expect("parse");
    let err = run(&m, 0).expect_err("expected build error");
    let msg = format!("{err:?}");
    assert!(
        msg.contains(want),
        "error {msg:?} should mention {want:?} ({src})"
    );
}

#[test]
fn lane_reads_are_bitmask_values() {
    sat("pred p { some x: Real | x.m = 3 }\nrun p for 2 Real");
    unsat("pred p { some x: Real | x.m = 3 and x.m = 4 }\nrun p for 2 Real");
    sat("pred p { some x: Real | x.m = -1 }\nrun p for 2 Real");
    sat("pred p { some x: Real | x.e = -1 }\nrun p for 2 Real");
}

#[test]
fn real_wellformed_rejects_even_mantissa() {
    // Odd mantissae are wellformed; even nonzero ones are not.
    sat("pred p { some x: Real | x.m = 3 and realWellformed[x] }\nrun p for 2 Real");
    unsat("pred p { some x: Real | x.m = 6 and realWellformed[x] }\nrun p for 2 Real");
    sat("pred p { some x: Real | x.m = 0 and realWellformed[x] }\nrun p for 2 Real");
}

#[test]
fn set_real_binds_dyadic_only() {
    sat("pred p { some x: Real | setReal[x, 0.5] }\nrun p for 2 Real");
    sat("pred p { some x: Real | setReal[x, 3.0] }\nrun p for 2 Real");
    sat("pred p { some x: Real | setReal[x, -1.5] }\nrun p for 2 Real");
    // Exact centre: 0.5 is (1, -1) after normalization.
    sat("pred p { some x: Real | setReal[x, 0.5] and x.m = 1 and x.e = -1 }\nrun p for 2 Real");
    // Non-dyadic literals fail loudly (no rounding in `setReal` itself;
    // use the rounding variants below).
    build_err(
        "pred p { some x: Real | setReal[x, 0.1] }\nrun p for 2 Real",
        "setRealNearest",
    );
}

#[test]
fn set_real_rounding_variants() {
    // Nearest/Down/Up all accept 0.1; results bracket the truth.
    sat("pred p { some x: Real | setRealNearest[x, 0.1] }\nrun p for 2 Real");
    sat("pred p { some d, u: Real | setRealDown[d, 0.1] and setRealUp[u, 0.1] and realLT[d, u] }\nrun p for 2 Real");
    unsat("pred p { some d, u: Real | setRealDown[d, 0.1] and setRealUp[u, 0.1] and realEq[d, u] }\nrun p for 2 Real");
    // Bracketing against dyadic bounds (inline dyadic literals are exact):
    // down(0.1) < 0.125 and 0.0625 < up(0.1).
    sat("pred p { some d: Real | setRealDown[d, 0.1] and realLT[d, 0.125] }\nrun p for 2 Real");
    sat("pred p { some u: Real | setRealUp[u, 0.1] and realLT[0.0625, u] }\nrun p for 2 Real");
    // Nearest coincides with one of the brackets.
    sat("pred p { some d, u, n: Real | setRealDown[d, 0.1] and setRealUp[u, 0.1] and setRealNearest[n, 0.1] and (realEq[n, d] or realEq[n, u]) }\nrun p for 3 Real");
    // Dyadic inputs are exact in every mode (same centre as setReal).
    sat("pred p { some x, y: Real | setRealNearest[x, 0.5] and setReal[y, 0.5] and realEq[x, y] }\nrun p for 2 Real");
    sat("pred p { some x, y: Real | setRealDown[x, 0.5] and setReal[y, 0.5] and realEq[x, y] }\nrun p for 2 Real");
    sat("pred p { some x, y: Real | setRealUp[x, 0.5] and setReal[y, 0.5] and realEq[x, y] }\nrun p for 2 Real");
    // Second arg must still be a decimal literal.
    build_err(
        "pred p { some x, y: Real | setRealNearest[x, y] }\nrun p for 2 Real",
        "decimal literal",
    );
}

#[test]
fn real_arith_is_exact() {
    // 0.5 + 0.5 = 1.0 exactly.
    sat("pred p { some a, b, c: Real | setReal[a, 0.5] and setReal[b, 0.5] and realAdd[a, b, c] and realEq[c, 1.0] }\nrun p for 3 Real");
    unsat("pred p { some a, b, c: Real | setReal[a, 0.5] and setReal[b, 0.5] and realAdd[a, b, c] and realLT[1.0, c] }\nrun p for 3 Real");
    // 1.5 - 0.5 = 1.0.
    sat("pred p { some a, b, c: Real | setReal[a, 1.5] and setReal[b, 0.5] and realSub[a, b, c] and realEq[c, 1.0] }\nrun p for 3 Real");
    // 1.5 * 2.0 = 3.0.
    sat("pred p { some a, c: Real | setReal[a, 1.5] and realMul[a, 2.0, c] and realEq[c, 3.0] }\nrun p for 3 Real");
    unsat("pred p { some a, c: Real | setReal[a, 1.5] and realMul[a, 2.0, c] and realEq[c, 2.0] }\nrun p for 3 Real");
    // 3.0 / 0.5 = 6.0 (cross-multiplied, exact).
    sat("pred p { some a, c: Real | setReal[a, 3.0] and realDiv[a, 0.5, c] and realEq[c, 6.0] }\nrun p for 3 Real");
    // Division by zero is UNSAT.
    unsat("pred p { some a, b, c: Real | setReal[b, 0.0] and realDiv[a, b, c] }\nrun p for 2 Real");
}

#[test]
fn real_comparisons() {
    sat("pred p { some a, b: Real | setReal[a, 1.5] and setReal[b, 4.0] and realLT[a, b] }\nrun p for 2 Real");
    unsat("pred p { some a, b: Real | setReal[a, 1.5] and setReal[b, 4.0] and realLT[b, a] }\nrun p for 2 Real");
    sat("pred p { some a: Real | setReal[a, 1.5] and realLTE[a, 1.5] }\nrun p for 2 Real");
    sat("pred p { some a, b: Real | setReal[a, 0.5] and setReal[b, 0.5] and realEq[a, b] }\nrun p for 2 Real");
    unsat("pred p { some a, b: Real | setReal[a, 0.5] and setReal[b, 0.25] and realEq[a, b] }\nrun p for 2 Real");
}

#[test]
fn real_value_equality_via_eq() {
    // `R = lit` binds the centre (Real reading: m/e only).
    sat("one sig R extends Real {}\nfact { R = 0.5 }\nrun {} for 2 Real");
    unsat("one sig R extends Real {}\nfact { R = 0.5 and R = 1.5 }\nrun {} for 2 Real");
    sat("one sig R extends Real {}\nfact { R = 0.5 and R != 1.5 }\nrun {} for 2 Real");
}

#[test]
fn ereal_models_still_use_ereal_reading() {
    // `EReal`-rooted `= lit` keeps the legacy lane-exact reading.
    sat("one sig R1 extends EReal {}\nfact { R1 = 0.5 }\nrun {} for 2 EReal");
    unsat("one sig R1 extends EReal {}\nfact { R1 = 0.5 and R1 = 1.5 }\nrun {} for 2 EReal");
}

#[test]
fn extends_real_partitions() {
    // `extends Real` children are disjoint subsets of `Real`.
    sat("sig X extends Real {}\nsig Y extends Real {}\npred p { some X and some Y }\nrun p for 2 Real");
    unsat("sig X extends Real {}\nsig Y extends Real {}\npred p { some X and some Y }\nrun p for 1 Real");
    unsat("sig X extends Real {}\nsig Y extends Real {}\npred p { some (X & Y) }\nrun p for 3 Real");
    // `Real` is abstract (covered by extenders): with a single extender
    // nothing lies outside it; with siblings it does (via the sibling).
    unsat("sig X extends Real {}\npred p { some Real - X }\nrun p for 2 Real");
    sat("sig X extends Real {}\nsig Y extends Real {}\npred p { some Real - X }\nrun p for 2 Real");
    // Without extenders, free values work as before.
    sat("pred p { some x: Real | setReal[x, 0.5] }\nrun p for 2 Real");
    // Scope guard: EReal cannot exceed Real.
    build_err("pred p { some x: EReal | realWellformed[x] }\nrun p for 1 Real, 2 EReal", "EReal");
}

#[test]
fn real_comparisons_gt_gte() {
    sat("pred p { some a, b: Real | setReal[a, 1.5] and setReal[b, 4.0] and realGT[b, a] }\nrun p for 2 Real");
    unsat("pred p { some a, b: Real | setReal[a, 1.5] and setReal[b, 4.0] and realGT[a, b] }\nrun p for 2 Real");
    unsat("pred p { some a, b: Real | setReal[a, 0.5] and setReal[b, 0.5] and realGT[a, b] }\nrun p for 2 Real");
    sat("pred p { some a: Real | setReal[a, 1.5] and realGTE[a, 1.5] }\nrun p for 2 Real");
    unsat("pred p { some a, b: Real | setReal[a, 1.5] and setReal[b, 4.0] and realGTE[a, b] }\nrun p for 2 Real");
}

#[test]
fn for_zero_real_with_literal_const() {
    // Literals are constants needing no atoms.
    sat("pred p { realEq[0.5, 0.5] }\nrun p for 0 Real");
    unsat("pred p { realEq[0.5, 1.5] }\nrun p for 0 Real");
}

#[test]
fn one_extender_collapses_real() {
    // Reported case: `one sig X extends Real` yields exactly one Real
    // value (abstract cover, own atoms, no free-pool ghosts).
    sat("one sig X extends Real {}\nfact { setRealNearest[X, 1.2345] }\nrun {} for 11 Int");
    sat("one sig X extends Real {}\nfact { setRealNearest[X, 1.2345] }\npred p { #Real = 1 }\nrun p for 11 Int");
    unsat("one sig X extends Real {}\nfact { setRealNearest[X, 1.2345] }\npred p { #Real = 2 }\nrun p for 11 Int");
    // Coexistence with EReal still works.
    sat("one sig A extends Real {}\none sig B extends EReal {}\nfact { A = 0.5 and setEReal[B, 0.5] }\nrun {} for 1 Real, 1 EReal");
}

#[test]
fn real_succ_pred() {
    // Successor is exact and minimal (default widths: succ(0.5) = 0.5625).
    sat("pred p { some a, b: Real | setReal[a, 0.5] and realSucc[a, b] and realEq[b, 0.5625] }\nrun p for 2 Real");
    unsat("pred p { some a, b: Real | setReal[a, 0.5] and realSucc[a, b] and realEq[b, 1.5] }\nrun p for 2 Real");
    // Predecessor mirrors (pred(0.5625) = 0.5).
    sat("pred p { some a, b: Real | setReal[a, 0.5625] and realPred[a, b] and realEq[b, 0.5] }\nrun p for 2 Real");
    // Negatives mirror through zero (succ(-0.5) = -pred(0.5)).
    sat("pred p { some a, b: Real | setReal[a, -0.5] and realSucc[a, b] and realEq[b, -0.46875] }\nrun p for 2 Real");
    unsat("pred p { some a, b: Real | setReal[a, -0.5] and realSucc[a, b] and realEq[b, -0.5625] }\nrun p for 2 Real");
    // Zero steps to ±(1, emin).
    sat("pred p { some a, b: Real | setReal[a, 0.0] and realSucc[a, b] and realGT[b, 0.0] }\nrun p for 2 Real");
    // Top of lane has no successor.
    unsat("pred p { some a, b: Real | realSucc[a, b] and a.m = 15 and a.e = 7 }\nrun p for 2 Real");
}

#[test]
fn real_up_down_functions() {
    // Function form in arithmetic position (hoisted to skolem-fast shape).
    sat("pred p { some a, c: Real | setReal[a, 0.5] and realAdd[realUp[a], 0.25, c] and realEq[c, 0.8125] }\nrun p for 3 Real");
    // Round trip: Down(Up(x)) = x.
    sat("pred p { some a, b, c: Real | setReal[a, 0.5] and realEq[realUp[a], b] and realEq[realDown[b], c] and realEq[a, c] }\nrun p for 3 Real");
    // Literal arguments constant-fold (needs an atom to carry lanes).
    sat("pred p { realEq[realUp[0.5], 0.5625] }\nrun p for 1 Real");
    unsat("pred p { realEq[realUp[0.5], 1.5] }\nrun p for 1 Real");
}
