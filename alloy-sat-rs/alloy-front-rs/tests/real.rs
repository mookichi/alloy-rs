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
    // Non-dyadic literals fail loudly (no rounding in `Real`).
    build_err(
        "pred p { some x: Real | setReal[x, 0.1] }\nrun p for 2 Real",
        "setReal",
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
    // `Real` itself is not covered: free values coexist with extenders.
    sat("sig X extends Real {}\npred p { some Real - X }\nrun p for 2 Real");
    // Scope guard: EReal cannot exceed Real.
    build_err("pred p { some x: EReal | realWellformed[x] }\nrun p for 1 Real, 2 EReal", "EReal");
}

#[test]
fn for_zero_real_with_literal_const() {
    // Literals are constants needing no atoms.
    sat("pred p { realEq[0.5, 0.5] }\nrun p for 0 Real");
    unsat("pred p { realEq[0.5, 1.5] }\nrun p for 0 Real");
}
