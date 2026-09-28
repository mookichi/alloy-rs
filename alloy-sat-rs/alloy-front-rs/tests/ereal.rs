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
    sat("pred p { some a, b, c: EReal | erealAdd[c, a, b] }\nrun p for 2 EReal");
    sat("pred p { some a, b, c: EReal | erealSub[c, a, b] }\nrun p for 2 EReal");
    sat("pred p { some a, b, c: EReal | erealMul[c, a, b] }\nrun p for 2 EReal");
    sat("pred p { some a, b, c: EReal | erealDiv[c, a, b] }\nrun p for 2 EReal");
}

#[test]
fn add_result_centre_is_pinned() {
    // Phase 1 window-pin: 0.5+0.5 = 1.0, so `c < 0.0` is UNSAT.
    // (With free centres both directions were SAT.)
    // Literals are ERealConstants (no witness atoms needed).
    unsat("pred p { some a, b, c: EReal | setEReal[a, 0.5] and setEReal[b, 0.5] and erealAdd[c, a, b] and erealLT[c, 0.0] }\nrun p for 5 EReal");
    // Control: the true direction stays SAT.
    sat("pred p { some a, b, c: EReal | setEReal[a, 0.5] and setEReal[b, 0.5] and erealAdd[c, a, b] and erealLT[0.0, c] }\nrun p for 5 EReal");
    // Subtraction likewise: 0.5-0.5 = 0.0 is not above 1.0.
    unsat("pred p { some a, b, c: EReal | setEReal[a, 0.5] and setEReal[b, 0.5] and erealSub[c, a, b] and erealLT[1.0, c] }\nrun p for 5 EReal");
    sat("pred p { some a, b, c: EReal | setEReal[a, 1.5] and setEReal[b, 0.5] and erealSub[c, a, b] and erealLT[0.0, c] }\nrun p for 5 EReal");
}

#[test]
fn div_guard_violation_is_unsat() {
    // k >= p denies the §5 precondition: no result exists (mirrors
    // `DivGuardUnsat` in mepk.als).
    unsat(
        "pred p { some a, b, c: EReal | b.k >= b.p and erealDiv[c, a, b] }\nrun p for 2 EReal",
    );
}

#[test]
fn mul_result_centre_is_pinned() {
    // Phase 2 window-pin: 2.0*3.0 = 6.0 (oracle `6 ± 4`), so `c < 0.0`
    // is UNSAT. Scopes allow room for hoisted literals.
    unsat("pred p { some a, c: EReal | setEReal[a, 2.0] and erealMul[c, a, 3.0] and erealLT[c, 0.0] }\nrun p for 6 EReal");
    // Control: the true direction stays SAT.
    sat("pred p { some a, c: EReal | setEReal[a, 2.0] and erealMul[c, a, 3.0] and erealLT[0.0, c] }\nrun p for 6 EReal");
}

#[test]
fn div_result_centre_is_pinned() {
    // Phase 2 window-pin: 3.0/0.5 = 6.0 (oracle `6 ± 4`).
    unsat("pred p { some a, c: EReal | setEReal[a, 3.0] and erealDiv[c, a, 0.5] and erealLT[c, 0.0] }\nrun p for 6 EReal");
    // Control (high precision, where the radius is tight): the true
    // direction stays SAT. At `max_p = 4` the sound radius (`R' = 8`
    // after the P0-1 Q-fix) genuinely cannot separate `6.0` from `0.0`,
    // so the control runs under `for 12 Int` (`R' = 0.5`).
    sat("pred p { some a, c: EReal | setEReal[a, 3.0] and erealDiv[c, a, 0.5] and erealLT[0.0, c] }\nrun p for 6 EReal, 12 Int");
}

#[test]
fn handmade_denormalized_lanes_rejected() {
    // m=1, p=4 is denormalized (|m| < 2^(p-1)) with k<p: div must reject
    // loudly (the `k < p` guard alone cannot exclude a zero-spanning
    // denominator here). Documents GIGO-as-UNSAT.
    unsat("pred p { some a, b, c: EReal | b.m = 1 and b.p = 4 and b.k = 0 and erealWellformed[b] and erealDiv[c, a, b] }\nrun p for 4 EReal");
    // Upper-bound edge: m=-16, p=4 has |m| = 2^p (not <): the §4 bound
    // `|c| < 2^(e+1)` fails, so mul rejects it too.
    unsat("pred p { some a, b, c: EReal | a.m = -16 and a.p = 4 and a.k = 0 and a.e = 0 and erealWellformed[a] and erealMul[c, a, b] }\nrun p for 4 EReal");
}

#[test]
fn div_zero_centre_is_unsat() {
    // rev2 §9.1(a): exact cancellation `b.m = 0` is out of domain even
    // when `k < p` holds (infinite relative error).
    unsat(
        "pred p { some a, b, c: EReal | b.m = 0 and b.k < b.p and erealWellformed[b] and erealDiv[c, a, b] }\nrun p for 2 EReal",
    );
}

#[test]
fn wellformed_rejects_bad_precision() {
    unsat("pred p { some x: EReal | x.p = 0 and erealWellformed[x] }\nrun p for 2 EReal");
    sat("pred p { some x: EReal | erealWellformed[x] }\nrun p for 2 EReal");
    sat("pred p { some x: EReal | erealDivGuard[x] }\nrun p for 2 EReal");
}

#[test]
fn valid_is_permanent_on_operands() {
    // Denormalized add/sub operands are UNSAT at the point of use
    // (previously only results and div denominators were pinned).
    unsat("pred p { some a, b, c: EReal | a.m = 1 and a.p = 4 and a.k = 0 and erealWellformed[a] and erealAdd[c, a, b] }\nrun p for 4 EReal");
    unsat("pred p { some a, b, c: EReal | a.m = 1 and a.p = 4 and a.k = 0 and erealWellformed[a] and erealSub[c, a, b] }\nrun p for 4 EReal");
    // Precision beyond the mantissa lane is rejected too
    // (default `for 4 Int` widths: m_width = 5, so p = 6 is out of range).
    unsat("pred p { some a, b, c: EReal | a.m = 32 and a.p = 6 and a.k = 0 and erealWellformed[a] and erealAdd[c, a, b] }\nrun p for 4 EReal");
    // Control: the normalized shape (m = 8 in [2^3, 2^4)) stays SAT.
    sat("pred p { some a, b, c: EReal | a.m = 8 and a.p = 4 and a.k = 0 and erealWellformed[a] and erealAdd[c, a, b] }\nrun p for 4 EReal");
}

#[test]
fn literals_need_no_witness_atoms() {
    // ERealConstant: decimal literals consume no scope atoms (previously
    // hoisted to `$elit` witnesses). With zero `EReal` atoms the hoisted
    // form is UNSAT; the constant form stays SAT.
    sat("pred p { erealWellformed[0.5] }\nrun p for 0 EReal");
    sat("pred p { erealValid[0.5] }\nrun p for 0 EReal");
    sat("pred p { erealLT[0.25, 0.5] }\nrun p for 0 EReal");
}

#[test]
fn ereal_valid_predicate() {
    // Strict goal-state Valid (core + k < p): converted literals satisfy it.
    sat("pred p { some x: EReal | setEReal[x, 0.5] and erealValid[x] }\nrun p for 2 EReal");
    // Precision loss (k >= p) fails the strict predicate but stays
    // representable for erealNeedsRefine.
    unsat("pred p { some x: EReal | x.m = 8 and x.p = 4 and x.k = 4 and erealValid[x] }\nrun p for 2 EReal");
    sat("pred p { some x: EReal | x.m = 8 and x.p = 4 and x.k = 4 and erealWellformed[x] }\nrun p for 2 EReal");
    // Denormalized lanes fail it too.
    unsat("pred p { some x: EReal | x.m = 1 and x.p = 4 and x.k = 0 and erealValid[x] }\nrun p for 2 EReal");
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
    // `EReal` is abstract: extenders are proper subsets, siblings are
    // disjoint, and the parent is covered by its extenders (decimal
    // literals are `ERealConstant` tuples needing no witness atoms, so
    // no spare room is required; `for N EReal` caps the population).
    // A lone extender covers the parent: nothing sits outside it.
    unsat("sig X extends EReal {}\npred p { some EReal - X }\nrun p for 2 EReal");
    unsat("one sig X extends EReal {}\npred p { some EReal - X }\nrun p for 2 EReal");
    // Parent collapses onto a `one` extender regardless of scope.
    unsat("one sig X extends EReal {}\npred p { #EReal = 2 }\nrun p for 3 EReal");
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
    // Abstract parents keep coverage (Java parity): nothing in S sits
    // outside its extenders.
    unsat(
        "abstract sig S extends EReal {}\nsig A extends S {}\nsig B extends S {}\npred p { some S - (A + B) }\nrun p for 3 EReal",
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
    // (Bare `1e100` is not a real literal — no decimal point — so the
    // dotted form is used here.)
    build_err(
        "pred p { some x: EReal | setEReal[x, 1.0e100] }\nrun p for 2 EReal",
        "cannot convert",
    );
    // Non-literal second argument.
    build_err(
        "pred p { some x, y: EReal | setEReal[x, y] }\nrun p for 2 EReal",
        "decimal literal",
    );
    // Decimal in integer lane position: explicit error, never silent zero.
    build_err(
        "pred p { some x: EReal | x.m = 3.14 }\nrun p for 2 EReal",
        "lane position",
    );
    // Decimal outside EReal value positions (`in` takes sets, and a
    // literal is not a set): explicit error.
    build_err(
        "pred p { some x: EReal | 3.14 in EReal }\nrun p for 2 EReal",
        "EReal value positions",
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

// ---- Phase 1: decimal literals as EReal values ---------------------------
// `R = lit` reads as value equality (`setEReal`); `erealExactEq` is lane
// identity; literals hoist in `ereal*` argument position. Integer/real
// are told apart purely by the decimal point (`1e3` is not a real).

fn parse_err(src: &str, want: &str) {
    let err = match parse_module(src) {
        Ok(_) => panic!("expected parse error: {src}"),
        Err(e) => e,
    };
    let msg = format!("{err:?}");
    assert!(
        msg.contains(want),
        "error {msg:?} should mention {want:?} ({src})"
    );
}

#[test]
fn lit_eq_sugar_on_extenders() {
    // The motivating shape: one-sigs extending EReal bound by value.
    sat("one sig R1 extends EReal {}\nfact { R1 = 1.2 }\nrun {} for 2 EReal");
    sat("one sig R2 extends EReal {}\nfact { R2 = -1.3e1 }\nrun {} for 2 EReal");
    // Value — not atom identity: two disjoint siblings may share a value.
    sat("one sig R1 extends EReal {}\none sig R2 extends EReal {}\nfact { R1 = 1.2 and R2 = 1.2 }\nrun {} for 3 EReal");
    // One atom cannot hold two values.
    unsat("one sig R1 extends EReal {}\nfact { R1 = 1.2 and R1 = 2.71 }\nrun {} for 2 EReal");
    // `!=` is the negation.
    unsat("one sig R1 extends EReal {}\nfact { R1 = 1.2 and R1 != 1.2 }\nrun {} for 2 EReal");
    sat("one sig R1 extends EReal {}\nfact { R1 = 1.2 and R1 != 2.71 }\nrun {} for 2 EReal");
    // Literal-vs-literal folds at lowering.
    sat("one sig R1 extends EReal {}\nfact { R1 = 1.2 and 1.20 = 1.2 }\nrun {} for 2 EReal");
    unsat("one sig R1 extends EReal {}\nfact { R1 = 1.2 and 1.2 = 2.71 }\nrun {} for 2 EReal");
}

#[test]
fn exact_eq_is_lane_identity() {
    sat("pred p { some a, b: EReal | setEReal[a, 0.5] and setEReal[b, 0.5] and erealExactEq[a, b] }\nrun p for 2 EReal");
    unsat("pred p { some a, b: EReal | setEReal[a, 0.5] and setEReal[b, 0.25] and erealExactEq[a, b] }\nrun p for 2 EReal");
    // Reflexivity holds.
    sat("pred p { some a: EReal | setEReal[a, 0.5] and erealExactEq[a, a] }\nrun p for 2 EReal");
}

#[test]
fn lits_hoist_in_ereal_args() {
    // `erealAdd[c, a, 0.5]` with a pinned addend is satisfiable.
    sat("pred p { some a, c: EReal | setEReal[a, 0.25] and erealAdd[c, a, 0.5] }\nrun p for 3 EReal");
    // Wellformedness of a literal value.
    sat("pred p { erealWellformed[0.5] }\nrun p for 1 EReal");
    // Out-of-range literal in argument position still fails loudly.
    build_err(
        "pred p { some a, c: EReal | erealAdd[c, a, 1.0e100] }\nrun p for 2 EReal",
        "cannot convert",
    );
}

#[test]
fn bare_exponent_is_not_a_real() {
    // No decimal point: `1e3` lexes as integer + name, so `setEReal`
    // (which needs a decimal literal second arg) cannot even parse it.
    parse_err(
        "pred p { some x: EReal | setEReal[x, 1e3] }\nrun p for 2 EReal",
        "expected",
    );
}

// ---- Phase 2: closed-interval comparisons --------------------------------
// Each value denotes `[lo, hi]`, `lo = c-R`, `hi = c+R`, `c = m*2^lsb`
// (`lsb = e-p+1`), `R = 2^(e-p+k)`. The test oracle below recomputes
// the relations in exact i128 arithmetic, independent of the lowering.

/// Closed interval of one oracle conversion, as exact scaled integers.
struct Iv {
    m: i128,
    lsb: i32,
    r: i32,
}

fn iv_of(s: &str) -> Iv {
    let w = alloy_kodkod_rs::mepk::MepkWidths::from_rule(4);
    let max_p = w.m_width.saturating_sub(1).max(1);
    let c = alloy_kodkod_rs::mepk::decimal_to_mepk(s, max_p).unwrap();
    let (m, e, p, k) = (c.v.m, c.v.e, c.v.p as i32, c.v.k);
    Iv {
        m,
        lsb: e - p + 1,
        r: e - p + k,
    }
}

/// Scale `m*2^lsb + s*2^r` to the common exponent `t` (exact; `t` is the
/// minimum of all four scales, so every shift is non-negative and tiny).
fn edge_at(v: &Iv, s: i128, t: i32) -> i128 {
    v.m * (1i128 << ((v.lsb - t) as u32)) + s * (1i128 << ((v.r - t) as u32))
}

#[derive(Clone, Copy)]
enum Rel {
    MayEq,
    Covers,
    Lt,
    Lte,
    MayLte,
    ExactEq,
    Gt,
    Gte,
}

impl Rel {
    fn pred(self) -> &'static str {
        match self {
            Rel::MayEq => "erealMayEq",
            Rel::Covers => "erealCovers",
            Rel::Lt => "erealLT",
            Rel::Lte => "erealLTE",
            Rel::MayLte => "erealMayLTE",
            Rel::ExactEq => "erealExactEq",
            Rel::Gt => "erealGT",
            Rel::Gte => "erealGTE",
        }
    }
    /// Ground truth in exact integer arithmetic on closed intervals.
    /// `exact` also requires lane identity (same conversion).
    fn holds(self, a: &Iv, b: &Iv, exact: bool) -> bool {
        let t = a.lsb.min(a.r).min(b.lsb).min(b.r);
        let (lo_a, hi_a) = (edge_at(a, -1, t), edge_at(a, 1, t));
        let (lo_b, hi_b) = (edge_at(b, -1, t), edge_at(b, 1, t));
        match self {
            Rel::MayEq => lo_a <= hi_b && lo_b <= hi_a,
            Rel::Covers => lo_a <= lo_b && hi_b <= hi_a,
            Rel::Lt => hi_a < lo_b,
            Rel::Lte => hi_a <= lo_b,
            Rel::MayLte => lo_b <= hi_a && hi_a <= hi_b,
            Rel::ExactEq => exact,
            Rel::Gt => hi_b < lo_a,
            Rel::Gte => hi_b <= lo_a,
        }
    }
}

/// Assert the solver agrees with the exact oracle for `pred[X, Y]`.
fn check_rel(rel: Rel, x: &str, y: &str) {
    let (a, b) = (iv_of(x), iv_of(y));
    // Lane identity holds iff the oracle conversions agree on all lanes.
    let lanes = |s: &str| conv_lanes(s);
    let exact = lanes(x) == lanes(y);
    let src = format!(
        "pred p {{ some a, b: EReal | setEReal[a, {x}] and setEReal[b, {y}] and {}[a, b] }}\nrun p for 2 EReal",
        rel.pred()
    );
    let m = parse_module(&src).expect("parse");
    let cnf = run(&m, 0).expect("run");
    let found = solve(&cnf).expect("solve").is_some();
    let want = rel.holds(&a, &b, exact);
    assert!(
        found == want,
        "{}[{x}, {y}]: solver sat={found}, oracle={want}",
        rel.pred()
    );
}

#[test]
fn interval_comparisons_match_oracle() {
    use Rel::*;
    let vals = [
        "0.5", "1.5", "2.0", "0.75", "8.0", "0.1", "-1.3e1", "1.2", "0.0", "-0.5",
    ];
    let rels = [MayEq, Covers, Lt, Lte, MayLte, ExactEq, Gt, Gte];
    for &x in &vals {
        for &y in &vals {
            for &rel in &rels {
                check_rel(rel, x, y);
            }
        }
    }
}

#[test]
fn interval_pred_shapes() {
    // Literals hoist in the new predicates too.
    sat("one sig R1 extends EReal {}\nfact { R1 = 1.2 and erealLTE[R1, 8.0] }\nrun {} for 2 EReal");
    unsat("one sig R1 extends EReal {}\nfact { R1 = 1.2 and erealLT[R1, 0.5] }\nrun {} for 2 EReal");
    sat("one sig R1 extends EReal {}\nfact { R1 = 1.2 and erealGT[R1, 0.5] }\nrun {} for 2 EReal");
    unsat("one sig R1 extends EReal {}\nfact { R1 = 1.2 and erealGTE[R1, 8.0] }\nrun {} for 2 EReal");
    // Arity is checked.
    build_err(
        "pred p { some a: EReal | erealLT[a] }\nrun p for 2 EReal",
        "expects 2 args",
    );
    // The motivating end-to-end shape (predicates only; no infix yet).
    // NOTE (Phase 1 window-pin): R3 = 1.2 + (-13.0) denotes [-14, -10]
    // (oracle `1.25 ± 0.125` plus `-13 ± 0.5` round to `-12 ± 2`), which
    // overlaps R2 = [-13.5, -12.5] but is not above it: `erealLTE[R2, R3]`
    // (`hi_R2 <= lo_R3`) is genuinely false here, so the chained check
    // uses overlap (`erealMayEq`), which holds.
    sat("one sig R1, R2, R3 extends EReal {}\nfact { R1 = 1.2 and R2 = -1.3e1 and erealAdd[R3, R1, R2] and erealMayEq[R2, R3] }\nrun {} for 3 EReal");
}

#[test]
fn interval_pred_wide_lanes() {
    // Regression: under `for 12 Int` the scaled-comparison barrel is
    // ~107 bits wide; circuit construction must not panic (the old
    // `1usize << i` shifter loop overflowed past 64 stages).
    sat("pred p { some a, b: EReal | setEReal[a, 1.5] and setEReal[b, 4.0] and erealLT[a, b] }\nrun p for 2 EReal, 12 Int");
    unsat("pred p { some a, b: EReal | setEReal[a, 1.5] and setEReal[b, 4.0] and erealLT[b, a] }\nrun p for 2 EReal, 12 Int");
    // The reported crash shape: hoisted literal under wide lanes.
    sat("pred p { some a: EReal | setEReal[a, 3.14] and erealLT[a, 4.0] }\nrun p for 2 EReal, 12 Int");
}

#[test]
fn five_var_chain_no_arity_collapse() {
    // Regression: desugared lanes used the bare spelling `x.e`, which the
    // quantifier environment resolved to a same-named variable (`e`)
    // instead of the `EReal.e` relation once 5+ decls were in scope,
    // producing `!resolution error: join arity too low: 1 + 1 - 2 < 1`.
    // Lanes now lower qualified (`EReal.e`), so shadowing is impossible.
    // The issue's original model (well-formed chain) is SAT.
    sat("pred p { some a, b, c, d, e: EReal | setEReal[a, 1.5] and setEReal[b, 2.5] and erealAdd[c, a, b] and erealMul[d, c, 2.0] and erealAdd[e, d, 0.5] }\nrun p for 7 EReal");
    // Minimal shadowing trigger: one `setEReal` with 5 decls.
    sat("pred p { some a, b, c, d, e: EReal | setEReal[a, 1.5] }\nrun p for 5 EReal");
    // The other lane names shadow likewise when used as variables.
    sat("pred p { some m, p, k, a, b: EReal | setEReal[m, 1.5] and setEReal[p, 2.5] and erealAdd[a, m, p] }\nrun p for 7 EReal");
    // UNSAT direction, true interval semantics: the chain denotes
    // ~8.5, so `e < 0.0` (`hi_e < lo_0`) is genuinely false.
    unsat("pred p { some a, b, c, d, e: EReal | setEReal[a, 1.5] and setEReal[b, 2.5] and erealAdd[c, a, b] and erealMul[d, c, 2.0] and erealAdd[e, d, 0.5] and erealLT[e, 0.0] }\nrun p for 8 EReal");
}

#[test]
fn compose_ereal_binds_lanes() {
    // EReal stores the MSB exponent (`lsb = e-p+1`): 0.5 is (8,-1,4,0).
    sat("pred p { some x: EReal | x.composeEReal[8, -1, 4, 0] }\nrun p for 2 EReal");
    // Agrees with setEReal on all four lanes.
    sat("pred p { some x, y: EReal | x.composeEReal[8, -1, 4, 0] and setEReal[y, 0.5] and erealExactEq[x, y] }\nrun p for 2 EReal");
    // Out-of-range literals fail loudly.
    build_err(
        "pred p { some x: EReal | x.composeEReal[8, -1, 99, 0] }\nrun p for 2 EReal",
        "outside the p lane range",
    );
}
