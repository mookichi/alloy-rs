//! Builtin `EReal` signature: `(m, e, p, k)` error-tracking values with
//! dedicated bit lanes (`M$`/`E$`/`P$`/`K$` atoms, two's-complement MSB
//! reading via the lane-scoped `BitsIn` cast) and desugared `ereal*`
//! operation predicates (mirrors `util/mepk.als`: `p`/`k` exponents
//! pinned, `m`/`e` centres free).

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
    // x.m = 3 needs bits {M$0, M$1} (top M$5 weighs -32, absent here).
    sat("pred p { some x: EReal | x.m = 3 }\nrun p for 2 EReal");
    // Total-function lanes: one value per atom, so two values clash.
    unsat("pred p { some x: EReal | x.m = 3 and x.m = 4 }\nrun p for 2 EReal");
    // Exponent lanes read likewise (p = 5 needs {P$0, P$2}).
    sat("pred p { some x: EReal | x.p = 5 }\nrun p for 2 EReal");
    // Negative mantissa via two's complement.
    sat("pred p { some x: EReal | x.m = -1 }\nrun p for 2 EReal");
}

#[test]
fn ereal_add_is_satisfiable() {
    sat("pred p { some a, b, c: EReal | erealAdd[a, b, c] }\nrun p for 2 EReal");
    sat("pred p { some a, b, c: EReal | erealSub[a, b, c] }\nrun p for 2 EReal");
    sat("pred p { some a, b, c: EReal | erealMul[a, b, c] }\nrun p for 2 EReal");
    sat("pred p { some a, b, c: EReal | erealDiv[a, b, c] }\nrun p for 2 EReal");
}

#[test]
fn div_guard_violation_is_unsat() {
    // k >= p denies the §5 precondition: no result exists (mirrors
    // `DivGuardUnsat` in mepk.als).
    unsat(
        "pred p { some a, b, c: EReal | b.k >= b.p and erealDiv[a, b, c] }\nrun p for 2 EReal",
    );
}

#[test]
fn wellformed_rejects_bad_precision() {
    unsat("pred p { some x: EReal | x.p = 0 and erealWellformed[x] }\nrun p for 2 EReal");
    sat("pred p { some x: EReal | erealWellformed[x] }\nrun p for 2 EReal");
    sat("pred p { some x: EReal | erealDivGuard[x] }\nrun p for 2 EReal");
}

#[test]
fn ereal_in_user_sig_fields() {
    // User sigs may hold EReal values; joins chain through lanes.
    sat("sig A { x: EReal }\npred p { some a: A | a.x.m = 3 }\nrun p for 2 A, 2 EReal");
    unsat(
        "sig A { x: EReal }\npred p { some a: A | a.x.m = 3 and a.x.m = 4 }\nrun p for 2 A, 2 EReal",
    );
}

#[test]
fn in_ereal_accepted_extends_rejected() {
    sat("sig X in EReal {}\npred p { some x: X | erealWellformed[x] }\nrun p for 2 EReal");
    build_err("sig EReal {}\npred p { some EReal }\nrun p for 1", "reserved");
}

#[test]
fn extends_ereal_partitions() {
    // A lone extender covers the parent.
    sat("sig X extends EReal {}\npred p { some X }\nrun p for 2 EReal");
    unsat(
        "sig X extends EReal {}\npred p { some EReal - X }\nrun p for 2 EReal",
    );
    // Lanes work through extenders.
    sat("sig X extends EReal {}\npred p { some x: X | setEReal[x, 0.5] }\nrun p for 2 EReal");
    // Siblings are disjoint: one atom cannot host both.
    unsat(
        "sig X extends EReal {}\nsig Y extends EReal {}\npred p { some X and some Y }\nrun p for 1 EReal",
    );
    sat(
        "sig X extends EReal {}\nsig Y extends EReal {}\npred p { some X and some Y }\nrun p for 2 EReal",
    );
    unsat(
        "sig X extends EReal {}\nsig Y extends EReal {}\npred p { some (X & Y) }\nrun p for 3 EReal",
    );
    // Nested extenders partition level by level.
    sat(
        "abstract sig S extends EReal {}\nsig A extends S {}\nsig B extends S {}\npred p { some A and some B }\nrun p for 2 EReal",
    );
    unsat(
        "abstract sig S extends EReal {}\nsig A extends S {}\nsig B extends S {}\npred p { some (A & B) }\nrun p for 3 EReal",
    );
}

#[test]
fn extender_sig_mults_are_cardinalities() {
    // `one` extender holds exactly one atom (bounds stay flexible;
    // Java `BoundsComputer` enforces `one` as a formula here too).
    sat("one sig X extends EReal {}\npred p { #X = 1 }\nrun p for 3 EReal");
    unsat("one sig X extends EReal {}\npred p { #X = 2 }\nrun p for 3 EReal");
    // `lone` caps at one; `some` forces nonempty.
    unsat("lone sig X extends EReal {}\npred p { #X = 2 }\nrun p for 3 EReal");
    sat("lone sig X extends EReal {}\nrun {} for 3 EReal");
    unsat("some sig X extends EReal {}\npred p { no X }\nrun p for 2 EReal");
    // Same for `in` children of the shared population.
    sat("one sig X in EReal {}\npred p { #X = 1 }\nrun p for 3 EReal");
    unsat("one sig X in EReal {}\npred p { #X = 2 }\nrun p for 3 EReal");
}

#[test]
fn models_without_ereal_are_unaffected() {
    // No EReal mention: no lane atoms, no lane relations, legacy reading.
    sat("sig A {}\npred p { some A }\nrun p for 2");
    // A lone user field named `m` keeps its Int reading while EReal
    // stays unallocated.
    sat("sig S { m: Int }\npred p { some s: S | s.m = 3 }\nrun p for 2 S");
}

// ---- setEReal: decimal literals bound to lane values -----------------------

/// Expected lanes under default test widths (no `for n Int` → int_count
/// 4 → M 5 → max_p 4), computed by the same oracle the lowering uses.
fn conv_lanes(s: &str) -> (i64, i64, i64, i64) {
    let w = alloy_kodkod_rs::mepk::MepkWidths::from_rule(4);
    let max_p = w.m_width.saturating_sub(1).max(1);
    let c = alloy_kodkod_rs::mepk::decimal_to_mepk(s, max_p).unwrap();
    (c.v.m as i64, c.v.e as i64, c.v.p as i64, c.v.k as i64)
}

#[test]
fn set_ereal_binds_lanes() {
    sat("pred p { some x: EReal | setEReal[x, 0.5] }\nrun p for 2 EReal");
    sat("pred p { some x: EReal | setEReal[x, 3.1415926535898] }\nrun p for 2 EReal");
    sat("pred p { some x: EReal | setEReal[x, -0.5] }\nrun p for 2 EReal");
    sat("pred p { some x: EReal | setEReal[x, .5] }\nrun p for 2 EReal");
    sat("pred p { some x: EReal | setEReal[x, 1.5e-1] }\nrun p for 2 EReal");
    // Bound lanes agree with the oracle conversion.
    let (m, e, p, k) = conv_lanes("0.5");
    sat(&format!(
        "pred p {{ some x: EReal | setEReal[x, 0.5] and x.m = {m} and x.e = {e} and x.p = {p} and x.k = {k} }}\nrun p for 2 EReal"
    ));
    // Contradicting any lane is UNSAT.
    unsat(&format!(
        "pred p {{ some x: EReal | setEReal[x, 0.5] and x.m = {} }}\nrun p for 2 EReal",
        m + 1
    ));
    // Non-dyadic rounding agrees too.
    let (m, e, p, k) = conv_lanes("0.1");
    sat(&format!(
        "pred p {{ some x: EReal | setEReal[x, 0.1] and x.m = {m} and x.e = {e} and x.p = {p} and x.k = {k} }}\nrun p for 2 EReal"
    ));
}

#[test]
fn set_ereal_rejects() {
    // Out of the i128 oracle range: loud lowering error, not UNSAT.
    build_err(
        "pred p { some x: EReal | setEReal[x, 1e100] }\nrun p for 2 EReal",
        "cannot convert",
    );
    // Non-literal second argument.
    build_err(
        "pred p { some x, y: EReal | setEReal[x, y] }\nrun p for 2 EReal",
        "decimal literal",
    );
    // Decimal outside setEReal: explicit error, never silent zero.
    build_err(
        "pred p { some x: EReal | x.m = 3.14 }\nrun p for 2 EReal",
        "only valid inside",
    );
}

#[test]
fn lane_widths_must_fit_bitwidth() {
    // `for 1 Int` gives E=2 circuits but rule widths need more (m=2,
    // w_exp=3): EReal must fail loudly instead of misreading lanes.
    build_err(
        "pred p { some x: EReal | erealWellformed[x] }\nrun p for 1 Int",
        "exceeds problem bitwidth",
    );
}
