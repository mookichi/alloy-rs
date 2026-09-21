//! Signed overflow prohibition (Iter2): overflowing comparisons go UNSAT,
//! division-by-zero goes UNSAT regardless of type.
//!
//! Two-phase search primitives: the gated (`run`) build excludes
//! overflowing models while the wrapping (`build_cnf_with(_, false)`)
//! build keeps them; `validate` agrees with the wrapping build.

use alloy_front_rs::{build_cnf_with, parse_module, run, solve, validate, CnfKind};

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

#[test]
fn div_by_zero_is_unsat() {
    // Type-independent: x/0 and x%0 can never hold.
    unsat("sig X in Signed {}\nrun { some x: X | x / 0 = 1 } for 4 Int");
    unsat("sig X in Signed {}\nrun { some x: X | x % 0 = 1 } for 4 Int");
    unsat("sig A {}\nrun { some a: A | #A / 0 = 1 } for 4 Int");
}

#[test]
fn mul_overflow_is_unsat() {
    // X = {0,1,2} reads as BITS value 7 (tainted); 7*7 = 49 overflows
    // the E=5 circuit (-16..15), so the comparison cannot hold.
    unsat("sig X in Signed {}\nfact pin { X = {0, 1, 2} }\nrun { X * X = 49 } for 4 Int");
    // ... and the wrapped value does not rescue it either.
    unsat("sig X in Signed {}\nfact pin { X = {0, 1, 2} }\nrun { X * X = -15 } for 4 Int");
}

#[test]
fn non_overflowing_arithmetic_still_sat() {
    // 7 * 1 = 7 fits: SAT preserved (`{0}` reads as bitmask 1).
    sat("sig X in Signed {}\nfact pin { X = {0, 1, 2} }\nrun { X * {0} = 7 } for 4 Int");
    // Pure-literal arithmetic is untainted (constant-folded), unaffected.
    sat("pred p { 7 = {0, 1, 2} }\nrun p for 4 Int");
}

#[test]
fn two_phase_gated_misses_wrapping_keeps() {
    // `run { X * X = -15 }` (X pinned to BITS value 7): the gated build
    // excludes the overflowing model, the wrapping build keeps it, and
    // `validate` agrees with each build respectively.
    let src =
        "sig X in Signed {}\nfact pin { X = {0, 1, 2} }\nrun { X * X = -15 } for 4 Int";
    let m = parse_module(src).expect("parse");
    let gated = run(&m, 0).expect("gated build");
    assert!(solve(&gated).expect("solve").is_none());
    let wrapping = build_cnf_with(&m, 0, CnfKind::Run, false).expect("wrapping build");
    let inst = solve(&wrapping).expect("solve").expect("wrapping keeps the model");
    assert!(validate(&wrapping, &inst).is_some(), "E-bit eval agrees");
    assert!(
        validate(&gated, &inst).is_none(),
        "gated validate rejects the overflowing model"
    );
}

#[test]
fn evaluator_flags_overflow_on_wrapping_model() {
    // `X * X = 49`: the constant wraps identically (49 -> -15 at E=5),
    // so the wrapping build is SAT while the gated build is UNSAT.
    // `validate` on the wrapping build holds (E-bit evaluator agreement).
    let src =
        "sig X in Signed {}\nfact pin { X = {0, 1, 2} }\nrun { X * X = 49 } for 4 Int";
    let m = parse_module(src).expect("parse");
    assert!(solve(&run(&m, 0).expect("gated")).expect("solve").is_none());
    let wrapping = build_cnf_with(&m, 0, CnfKind::Run, false).expect("wrapping");
    let inst = solve(&wrapping).expect("solve").expect("wrapping SAT");
    assert!(validate(&wrapping, &inst).is_some());
}
