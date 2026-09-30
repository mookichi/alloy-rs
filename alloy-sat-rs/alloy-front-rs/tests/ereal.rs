//! Builtin `EReal` in flat mode: the type domain is exactly the bit lanes
//! (`EReal = $M + $E + $P + $K`), so a value is the *set* of its lane
//! bits — there is no `EReal$i` value-atom pool and `for N EReal` is
//! rejected like `for N Real`. Values are held by `in`-sigs or holder
//! fields (`sig X in EReal {}`, `sig H { r: EReal }`); a scalar
//! `some x: EReal` can only hold a single bit, so the quantified-value
//! idiom is gone.
//!
//! `p`/`k` bits are the error interval, so an `EReal` value with any of
//! them reads as `c ± R`; a `Real`-rooted value has none and its `p`/`k`
//! read 0. `ereal*` operations desugar to lane constraints exactly as
//! before (mirrors `util/mepk.als`).

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
    match run(&m, 0) {
        Ok(_) => panic!("expected build error: {src}"),
        Err(err) => {
            let msg = format!("{err:?}");
            assert!(
                msg.contains(want),
                "error {msg:?} should mention {want:?} ({src})"
            );
        }
    }
}

#[test]
fn lane_reads_are_bitmask_values() {
    // x.m = 3 needs bits {M$0, M$1} (the top M bit weighs negative).
    sat("sig X in EReal {}\npred p { X.m = 3 }\nrun p");
    // One value per holder: two readings of the same lane must agree.
    unsat("sig X in EReal {}\npred p { X.m = 3 and X.m = 4 }\nrun p");
    // Exponent lanes read likewise (p = 5 needs {P$0, P$2}).
    sat("sig X in EReal {}\npred p { X.p = 5 }\nrun p");
    // Negative mantissa via two's complement.
    sat("sig X in EReal {}\npred p { X.m = -1 }\nrun p");
    // The error lanes are readable on a holder, and are free unless
    // constrained: a value's radius is not implied by its centre.
    sat("sig X in EReal {}\npred p { X.k = 0 }\nrun p");
}

#[test]
fn ereal_ops_are_satisfiable() {
    sat("sig A, B, C in EReal {}\npred p { erealAdd[C, A, B] }\nrun p");
    sat("sig A, B, C in EReal {}\npred p { erealSub[C, A, B] }\nrun p");
    sat("sig A, B, C in EReal {}\npred p { erealMul[C, A, B] }\nrun p");
    sat("sig A, B, C in EReal {}\npred p { erealDiv[C, A, B] }\nrun p");
}

#[test]
fn add_result_centre_is_pinned() {
    // Window-pin: 0.5+0.5 = 1.0, so `c < 0.0` is UNSAT. (With free
    // centres both directions were SAT.) Literals are constants needing
    // no witness atoms.
    unsat("sig A, B, C in EReal {}\npred p { setEReal[A, 0.5] and setEReal[B, 0.5] and erealAdd[C, A, B] and erealLT[C, 0.0] }\nrun p");
    // Control: the true direction stays SAT.
    sat("sig A, B, C in EReal {}\npred p { setEReal[A, 0.5] and setEReal[B, 0.5] and erealAdd[C, A, B] and erealLT[0.0, C] }\nrun p");
    // Subtraction likewise: 0.5-0.5 = 0.0 is not above 1.0.
    unsat("sig A, B, C in EReal {}\npred p { setEReal[A, 0.5] and setEReal[B, 0.5] and erealSub[C, A, B] and erealLT[1.0, C] }\nrun p");
    sat("sig A, B, C in EReal {}\npred p { setEReal[A, 1.5] and setEReal[B, 0.5] and erealSub[C, A, B] and erealLT[0.0, C] }\nrun p");
}

#[test]
fn div_guard_violation_is_unsat() {
    // k >= p denies the §5 precondition: no result exists (mirrors
    // `DivGuardUnsat` in mepk.als).
    unsat("sig A, B, C in EReal {}\npred p { B.k >= B.p and erealDiv[C, A, B] }\nrun p");
}

#[test]
fn mul_result_centre_is_pinned() {
    // Window-pin: 2.0*3.0 = 6.0 (oracle `6 ± 4`), so `c < 0.0` is UNSAT.
    unsat("sig A, C in EReal {}\npred p { setEReal[A, 2.0] and erealMul[C, A, 3.0] and erealLT[C, 0.0] }\nrun p");
    // Control: the true direction stays SAT.
    sat("sig A, C in EReal {}\npred p { setEReal[A, 2.0] and erealMul[C, A, 3.0] and erealLT[0.0, C] }\nrun p");
}

#[test]
fn div_result_centre_is_pinned() {
    // Window-pin: 3.0/0.5 = 6.0 (oracle `6 ± 4`).
    unsat("sig A, C in EReal {}\npred p { setEReal[A, 3.0] and erealDiv[C, A, 0.5] and erealLT[C, 0.0] }\nrun p");
    // Control (high precision, where the radius is tight): the true
    // direction stays SAT. At `max_p = 4` the sound radius (`R' = 8`
    // after the P0-1 Q-fix) genuinely cannot separate `6.0` from `0.0`,
    // so the control runs under `for 12 Int` (`R' = 0.5`).
    sat("sig A, C in EReal {}\npred p { setEReal[A, 3.0] and erealDiv[C, A, 0.5] and erealLT[0.0, C] }\nrun p for 12 Int");
}

#[test]
fn handmade_denormalized_lanes_rejected() {
    // m=1, p=4 is denormalized (|m| < 2^(p-1)) with k<p: div must reject
    // loudly (the `k < p` guard alone cannot exclude a zero-spanning
    // denominator here). Documents GIGO-as-UNSAT.
    unsat("sig A, B, C in EReal {}\npred p { B.m = 1 and B.p = 4 and B.k = 0 and erealWellformed[B] and erealDiv[C, A, B] }\nrun p");
    // Upper-bound edge: m=-16, p=4 has |m| = 2^p (not <): the §4 bound
    // `|c| < 2^(e+1)` fails, so mul rejects it too.
    unsat("sig A, B, C in EReal {}\npred p { A.m = -16 and A.p = 4 and A.k = 0 and A.e = 0 and erealWellformed[A] and erealMul[C, A, B] }\nrun p");
}

#[test]
fn div_zero_centre_is_unsat() {
    // rev2 §9.1(a): exact cancellation `b.m = 0` is out of domain even
    // when `k < p` holds (infinite relative error).
    unsat("sig A, B, C in EReal {}\npred p { B.m = 0 and B.k < B.p and erealWellformed[B] and erealDiv[C, A, B] }\nrun p");
}

#[test]
fn wellformed_rejects_bad_precision() {
    unsat("sig X in EReal {}\npred p { X.p = 0 and erealWellformed[X] }\nrun p");
    sat("sig X in EReal {}\npred p { erealWellformed[X] }\nrun p");
    sat("sig X in EReal {}\npred p { erealDivGuard[X] }\nrun p");
}

#[test]
fn valid_is_permanent_on_operands() {
    // Denormalized add/sub operands are UNSAT at the point of use
    // (previously only results and div denominators were pinned).
    unsat("sig A, B, C in EReal {}\npred p { A.m = 1 and A.p = 4 and A.k = 0 and erealWellformed[A] and erealAdd[C, A, B] }\nrun p");
    unsat("sig A, B, C in EReal {}\npred p { A.m = 1 and A.p = 4 and A.k = 0 and erealWellformed[A] and erealSub[C, A, B] }\nrun p");
    // Precision beyond the mantissa lane is rejected too
    // (default `for 4 Int` widths: m_width = 5, so p = 6 is out of range).
    unsat("sig A, B, C in EReal {}\npred p { A.m = 32 and A.p = 6 and A.k = 0 and erealWellformed[A] and erealAdd[C, A, B] }\nrun p");
    // Control: the normalized shape (m = 8 in [2^3, 2^4)) stays SAT.
    sat("sig A, B, C in EReal {}\npred p { A.m = 8 and A.p = 4 and A.k = 0 and erealWellformed[A] and erealAdd[C, A, B] }\nrun p");
}

#[test]
fn literals_need_no_witness_atoms() {
    // Constants: a decimal literal in an `ereal*` position is folded at
    // lowering, so it works in a model with no sigs at all (previously the
    // hoisted form needed `EReal` atoms and `for 0 EReal` was the way to
    // get none).
    sat("pred p { erealWellformed[0.5] }\nrun p");
    sat("pred p { erealValid[0.5] }\nrun p");
    sat("pred p { erealLT[0.25, 0.5] }\nrun p");
}

#[test]
fn ereal_valid_predicate() {
    // Strict goal-state Valid (core + k < p): converted literals satisfy it.
    sat("sig X in EReal {}\npred p { setEReal[X, 0.5] and erealValid[X] }\nrun p");
    // Precision loss (k >= p) fails the strict predicate but stays
    // representable for erealNeedsRefine.
    unsat("sig X in EReal {}\npred p { X.m = 8 and X.p = 4 and X.k = 4 and erealValid[X] }\nrun p");
    sat("sig X in EReal {}\npred p { X.m = 8 and X.p = 4 and X.k = 4 and erealWellformed[X] }\nrun p");
    // Denormalized lanes fail it too.
    unsat("sig X in EReal {}\npred p { X.m = 1 and X.p = 4 and X.k = 0 and erealValid[X] }\nrun p");
}

#[test]
fn ereal_in_user_sig_fields() {
    // User sigs may hold EReal values; the lane read projects the value's
    // bit set (`h.r & $M`), whatever the holder is.
    sat("sig A { x: EReal }\npred p { some a: A | a.x.m = 3 }\nrun p for 2 A");
    unsat("sig A { x: EReal }\npred p { some a: A | a.x.m = 3 and a.x.m = 4 }\nrun p for 2 A");
    // The same read through a nested holder.
    sat("sig H { r: EReal }\nsig A { h: one H }\npred p { some a: A | a.h.r.p = 5 }\nrun p");
    // `Real` holders carry no error bits, so their `p` reads 0.
    sat("sig A { x: Real }\npred p { some a: A | some $P and a.x.p = 0 }\nrun p for 2 A");
}

#[test]
fn in_ereal_accepted_extends_rejected() {
    sat("sig X in EReal {}\npred p { erealWellformed[X] }\nrun p");
    build_err("sig EReal {}\npred p { some EReal }\nrun p for 1", "reserved");
    // `extends EReal` would add value atoms outside the lane partition.
    build_err("sig X extends EReal {}\nrun {}", "cannot extend EReal");
    // `for N EReal` is rejected: the domain derives as `$M+$E+$P+$K`.
    build_err("pred p { some $P }\nrun p for 2 EReal", "not scoped in flat mode");
}

#[test]
fn flat_domain_bans_and_shape() {
    // The domain is exactly the four lane sigs, and they partition it.
    sat("pred p { EReal = $M + $E + $P + $K }\nrun p");
    sat("pred p { no ($M & $P) and some EReal }\nrun p");
    // The cardinality needs a bitwidth wide enough to count the domain.
    sat("pred p { #EReal = 32 }\nrun p for 8 $M, 8 $E, 8 $P, 8 $K");
    // `Real` is the same domain minus the error lanes.
    sat("pred p { Real = $M + $E and EReal = Real + $P + $K }\nrun p");
    // A value bit set outside the holder's domain is not a value.
    unsat("sig X in EReal {}\nfact { X in Real }\npred p { X = {M$0, P$2} }\nrun p");
    // … and an `in`-sig is a free subset, so two may hold the same value
    // (the value-sharing the reified `extends` form used to allow).
    sat("sig A, B in EReal {}\nfact { setEReal[A, 1.2] and setEReal[B, 1.2] }\npred p { A = B }\nrun p");
    unsat("sig A, B in EReal {}\nfact { setEReal[A, 1.2] and setEReal[B, 2.71] }\npred p { A = B }\nrun p");
}

#[test]
fn in_sig_mults_are_cardinalities() {
    // An `in`-sig's atoms are inherited, so its multiplicity is a
    // cardinality formula, not an exact bound (Java `BoundsComputer`).
    sat("one sig X in EReal {}\npred p { #X = 1 }\nrun p");
    unsat("one sig X in EReal {}\npred p { #X = 2 }\nrun p");
    // `lone` caps at one; `some` forces nonempty.
    unsat("lone sig X in EReal {}\npred p { #X = 2 }\nrun p");
    sat("lone sig X in EReal {}\nrun {}");
    unsat("some sig X in EReal {}\npred p { no X }\nrun p");
    // The multiplicity is about *atoms*, so a `one` holder is a single
    // lane bit — too small to hold a multi-bit value.
    unsat("one sig X in EReal {}\npred p { setEReal[X, 0.5] }\nrun p");
    sat("sig X in EReal {}\npred p { setEReal[X, 0.5] }\nrun p");
}

#[test]
fn models_without_ereal_are_unaffected() {
    // No EReal mention: no lane atoms, no lane sigs, plain reading.
    sat("sig A {}\npred p { some A }\nrun p for 2");
    // A lone user field named `m` keeps its Int reading while the lanes
    // stay unallocated.
    sat("sig S { m: Int }\npred p { some s: S | s.m = 3 }\nrun p for 2 S");
    sat("sig S { p: Int }\npred p { some s: S | s.p = 3 }\nrun p for 2 S");
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
    sat("sig X in EReal {}\npred p { setEReal[X, 0.5] }\nrun p");
    sat("sig X in EReal {}\npred p { setEReal[X, 3.1415926535898] }\nrun p");
    sat("sig X in EReal {}\npred p { setEReal[X, -0.5] }\nrun p");
    sat("sig X in EReal {}\npred p { setEReal[X, .5] }\nrun p");
    sat("sig X in EReal {}\npred p { setEReal[X, 1.5e-1] }\nrun p");
    // Bound lanes agree with the oracle conversion.
    let (m, e, p, k) = conv_lanes("0.5");
    sat(&format!(
        "sig X in EReal {{}}\npred p {{ setEReal[X, 0.5] and X.m = {m} and X.e = {e} and X.p = {p} and X.k = {k} }}\nrun p"
    ));
    // Contradicting any lane is UNSAT.
    unsat(&format!(
        "sig X in EReal {{}}\npred p {{ setEReal[X, 0.5] and X.m = {} }}\nrun p",
        m + 1
    ));
    // Non-dyadic rounding agrees too.
    let (m, e, p, k) = conv_lanes("0.1");
    sat(&format!(
        "sig X in EReal {{}}\npred p {{ setEReal[X, 0.1] and X.m = {m} and X.e = {e} and X.p = {p} and X.k = {k} }}\nrun p"
    ));
}

#[test]
fn set_ereal_rejects() {
    // Out of the i128 oracle range: loud lowering error, not UNSAT.
    // (Bare `1e100` is not a real literal — no decimal point — so the
    // dotted form is used here.)
    build_err(
        "sig X in EReal {}\npred p { setEReal[X, 1.0e100] }\nrun p",
        "cannot convert",
    );
    // Non-literal second argument.
    build_err(
        "sig X, Y in EReal {}\npred p { setEReal[X, Y] }\nrun p",
        "decimal literal",
    );
    // Decimal in integer lane position: explicit error, never silent zero.
    build_err(
        "sig X in EReal {}\npred p { X.m = 3.14 }\nrun p",
        "lane position",
    );
    // Decimal outside EReal value positions (`in` takes sets, and a
    // literal is not a set): explicit error.
    build_err("pred p { 3.14 in EReal }\nrun p", "EReal value positions");
}

#[test]
fn lane_widths_must_fit_bitwidth() {
    // `for 1 Int` gives E=2 circuits but rule widths need more (m=2,
    // w_exp=3): EReal must fail loudly instead of misreading lanes.
    build_err(
        "sig X in EReal {}\npred p { erealWellformed[X] }\nrun p for 1 Int",
        "exceeds problem bitwidth",
    );
}

// ---- Phase 1: decimal literals as EReal values ---------------------------
// `R = lit` reads as value equality (`setEReal`); `erealExactEq` is lane
// identity; literals fold in `ereal*` argument position. Integer/real
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
fn lit_eq_sugar_on_in_sigs() {
    // The motivating shape: `in`-sigs over `EReal` bound by value.
    sat("sig R1 in EReal {}\nfact { R1 = 1.2 }\nrun {}");
    sat("sig R2 in EReal {}\nfact { R2 = -1.3e1 }\nrun {}");
    // Value — not atom identity: two holders may share a value.
    sat("sig R1, R2 in EReal {}\nfact { R1 = 1.2 and R2 = 1.2 }\nrun {}");
    // A set denotes one value, so it cannot be two.
    unsat("sig R1 in EReal {}\nfact { R1 = 1.2 and R1 = 2.71 }\nrun {}");
    // `!=` is the negation.
    unsat("sig R1 in EReal {}\nfact { R1 = 1.2 and R1 != 1.2 }\nrun {}");
    sat("sig R1 in EReal {}\nfact { R1 = 1.2 and R1 != 2.71 }\nrun {}");
    // Literal-vs-literal folds at lowering.
    sat("sig R1 in EReal {}\nfact { R1 = 1.2 and 1.20 = 1.2 }\nrun {}");
    unsat("sig R1 in EReal {}\nfact { R1 = 1.2 and 1.2 = 2.71 }\nrun {}");
}

#[test]
fn exact_eq_is_lane_identity() {
    sat("sig A, B in EReal {}\npred p { setEReal[A, 0.5] and setEReal[B, 0.5] and erealExactEq[A, B] }\nrun p");
    unsat("sig A, B in EReal {}\npred p { setEReal[A, 0.5] and setEReal[B, 0.25] and erealExactEq[A, B] }\nrun p");
    // Reflexivity holds.
    sat("sig A in EReal {}\npred p { setEReal[A, 0.5] and erealExactEq[A, A] }\nrun p");
}

#[test]
fn lits_fold_in_ereal_args() {
    // `erealAdd[C, A, 0.5]` with a pinned addend is satisfiable.
    sat("sig A, C in EReal {}\npred p { setEReal[A, 0.25] and erealAdd[C, A, 0.5] }\nrun p");
    // Wellformedness of a literal value.
    sat("pred p { erealWellformed[0.5] }\nrun p");
    // Out-of-range literal in argument position still fails loudly.
    build_err(
        "sig A, C in EReal {}\npred p { erealAdd[C, A, 1.0e100] }\nrun p",
        "cannot convert",
    );
}

#[test]
fn bare_exponent_is_not_a_real() {
    // No decimal point: `1e3` lexes as integer + name, so `setEReal`
    // (which needs a decimal literal second arg) cannot even parse it.
    parse_err(
        "sig X in EReal {}\npred p { setEReal[X, 1e3] }\nrun p",
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
        "sig A, B in EReal {{}}\npred p {{ setEReal[A, {x}] and setEReal[B, {y}] and {}[A, B] }}\nrun p",
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
    // Literals fold in the predicates too.
    sat("sig R1 in EReal {}\nfact { R1 = 1.2 and erealLTE[R1, 8.0] }\nrun {}");
    unsat("sig R1 in EReal {}\nfact { R1 = 1.2 and erealLT[R1, 0.5] }\nrun {}");
    sat("sig R1 in EReal {}\nfact { R1 = 1.2 and erealGT[R1, 0.5] }\nrun {}");
    unsat("sig R1 in EReal {}\nfact { R1 = 1.2 and erealGTE[R1, 8.0] }\nrun {}");
    // Arity is checked.
    build_err("sig A in EReal {}\npred p { erealLT[A] }\nrun p", "expects 2 args");
    // The motivating end-to-end shape (predicates only; no infix yet).
    // NOTE (Phase 1 window-pin): R3 = 1.2 + (-13.0) denotes [-14, -10]
    // (oracle `1.25 ± 0.125` plus `-13 ± 0.5` round to `-12 ± 2`), which
    // overlaps R2 = [-13.5, -12.5] but is not above it: `erealLTE[R2, R3]`
    // (`hi_R2 <= lo_R3`) is genuinely false here, so the chained check
    // uses overlap (`erealMayEq`), which holds.
    sat("sig R1, R2, R3 in EReal {}\nfact { R1 = 1.2 and R2 = -1.3e1 and erealAdd[R3, R1, R2] and erealMayEq[R2, R3] }\nrun {}");
}

#[test]
fn interval_pred_wide_lanes() {
    // Regression: under `for 12 Int` the scaled-comparison barrel is
    // ~107 bits wide; circuit construction must not panic (the old
    // `1usize << i` shifter loop overflowed past 64 stages).
    sat("sig A, B in EReal {}\npred p { setEReal[A, 1.5] and setEReal[B, 4.0] and erealLT[A, B] }\nrun p for 12 Int");
    unsat("sig A, B in EReal {}\npred p { setEReal[A, 1.5] and setEReal[B, 4.0] and erealLT[B, A] }\nrun p for 12 Int");
    // The reported crash shape: folded literal under wide lanes.
    sat("sig A in EReal {}\npred p { setEReal[A, 3.14] and erealLT[A, 4.0] }\nrun p for 12 Int");
}

#[test]
fn five_holder_chain_no_arity_collapse() {
    // Regression: desugared lanes used the bare spelling `x.e`, which the
    // quantifier environment resolved to a same-named variable (`e`)
    // instead of the lane relation once 5+ decls were in scope,
    // producing `!resolution error: join arity too low: 1 + 1 - 2 < 1`.
    // Lanes now read `x & $E`, whose lane sig name can never be shadowed
    // (a `$` name cannot be declared), so the hazard is gone by
    // construction; the chain still has to solve.
    sat("sig A, B, C, D, E in EReal {}\npred p { setEReal[A, 1.5] and setEReal[B, 2.5] and erealAdd[C, A, B] and erealMul[D, C, 2.0] and erealAdd[E, D, 0.5] }\nrun p");
    // Holders named after the lanes themselves.
    sat("sig M, P, K, A, B in EReal {}\npred p { setEReal[M, 1.5] and setEReal[P, 2.5] and erealAdd[A, M, P] }\nrun p");
    // UNSAT direction, true interval semantics: the chain denotes
    // ~8.5, so `e < 0.0` (`hi_e < lo_0`) is genuinely false.
    unsat("sig A, B, C, D, E in EReal {}\npred p { setEReal[A, 1.5] and setEReal[B, 2.5] and erealAdd[C, A, B] and erealMul[D, C, 2.0] and erealAdd[E, D, 0.5] and erealLT[E, 0.0] }\nrun p");
}

#[test]
fn bit_singletons_spell_ereal_lanes() {
    // A `p` lane reads as a signed integer of its own group, so the bit
    // spelling and the integer spelling agree: 5 = {P$0, P$2}. (A lane
    // has no set reading: `X.p = {P$0, P$2}` is a category error.)
    sat("pred p { {P$0, P$2} = 5 }\nrun p");
    unsat("pred p { {P$0, P$2} = 6 }\nrun p");
    // A one-lane set is an integer, so a decimal literal (a *value*)
    // cannot be compared with it.
    build_err(
        "pred p { {P$0, P$2} = 0.5 }\nrun p",
        "single lane",
    );
    // Adding a second lane family makes it a value, and then it compares
    // as one: p=5 is not 0.5's value.
    unsat("pred p { {M$0, P$0, P$2} = 0.5 }\nrun p");
    build_err("pred p { {kbit[99]} = 1 }\nrun p", "outside the lane range");
}

#[test]
fn compose_ereal_binds_lanes() {
    // EReal stores the MSB exponent (`lsb = e-p+1`): 0.5 is (8,-1,4,0).
    sat("sig X in EReal {}\npred p { X.composeEReal[8, -1, 4, 0] }\nrun p");
    // Agrees with setEReal on all four lanes.
    sat("sig X, Y in EReal {}\npred p { X.composeEReal[8, -1, 4, 0] and setEReal[Y, 0.5] and erealExactEq[X, Y] }\nrun p");
    // Out-of-range literals fail loudly.
    build_err(
        "sig X in EReal {}\npred p { X.composeEReal[8, -1, 99, 0] }\nrun p",
        "outside the p lane range",
    );
}
