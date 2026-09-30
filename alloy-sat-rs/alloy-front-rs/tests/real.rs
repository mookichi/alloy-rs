//! Builtin `Real` in flat mode: `Real = $M + $E` as sets (no `Real$i`
//! value atoms; `for N Real` is rejected, the population derives from
//! `for N $M, M $E`). Values are bit sets held by `in`-sigs or holder
//! sigs (`sig R in Real {}`, `some sig H { r: Real }`); scalar
//! quantification (`some x: Real`) cannot hold `(m, e)` centres.
//! `EReal` is flat too (`EReal = $M + $E + $P + $K`), so `Real` is the
//! narrower domain of the two rather than a parent of it.

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
    // `R.m` reads the `$M` partition (redirected from the legacy join).
    sat("sig R in Real {}\nfact { R.m = 3 }\nrun {}");
    unsat("sig R in Real {}\nfact { R.m = 3 and R.m = 4 }\nrun {}");
    sat("sig R in Real {}\nfact { R.m = -1 }\nrun {}");
    sat("sig R in Real {}\nfact { R.e = -1 }\nrun {}");
}

#[test]
fn real_wellformed_rejects_even_mantissa() {
    // Odd mantissae are wellformed; even nonzero ones are not.
    sat("sig R in Real {}\nfact { R.m = 3 and realWellformed[R] }\nrun {}");
    unsat("sig R in Real {}\nfact { R.m = 6 and realWellformed[R] }\nrun {}");
    sat("sig R in Real {}\nfact { R.m = 0 and realWellformed[R] }\nrun {}");
}

#[test]
fn set_real_binds_dyadic_only() {
    sat("sig R in Real {}\nfact { setReal[R, 0.5] }\nrun {}");
    sat("sig R in Real {}\nfact { setReal[R, 3.0] }\nrun {}");
    sat("sig R in Real {}\nfact { setReal[R, -1.5] }\nrun {}");
    // Exact centre: 0.5 is (1, -1) after normalization.
    sat("sig R in Real {}\nfact { setReal[R, 0.5] and R.m = 1 and R.e = -1 }\nrun {}");
    // Plain non-dyadic literals are UNSAT (no dyadic centre equals
    // them; approximation needs the `(d)` spelling or the rounding
    // variants below).
    unsat("sig R in Real {}\nfact { setReal[R, 0.1] }\nrun {}");
    // Approximable spelling binds nearest.
    sat("sig A, B in Real {}\nfact { setReal[A, (0.1)] and setRealNearest[B, 0.1] and realEq[A, B] }\nrun {}");
}

#[test]
fn set_real_rounding_variants() {
    // Nearest/Down/Up all accept 0.1; results bracket the truth.
    sat("sig R in Real {}\nfact { setRealNearest[R, 0.1] }\nrun {}");
    sat("sig D, U in Real {}\nfact { setRealDown[D, 0.1] and setRealUp[U, 0.1] and realLT[D, U] }\nrun {}");
    unsat("sig D, U in Real {}\nfact { setRealDown[D, 0.1] and setRealUp[U, 0.1] and realEq[D, U] }\nrun {}");
    // Bracketing against dyadic bounds (inline dyadic literals are exact):
    // down(0.1) < 0.125 and 0.0625 < up(0.1).
    sat("sig D in Real {}\nfact { setRealDown[D, 0.1] and realLT[D, 0.125] }\nrun {}");
    sat("sig U in Real {}\nfact { setRealUp[U, 0.1] and realLT[0.0625, U] }\nrun {}");
    // Nearest coincides with one of the brackets.
    sat("sig D, U, N in Real {}\nfact { setRealDown[D, 0.1] and setRealUp[U, 0.1] and setRealNearest[N, 0.1] and (realEq[N, D] or realEq[N, U]) }\nrun {}");
    // Dyadic inputs are exact in every mode (same centre as setReal).
    sat("sig X, Y in Real {}\nfact { setRealNearest[X, 0.5] and setReal[Y, 0.5] and realEq[X, Y] }\nrun {}");
    sat("sig X, Y in Real {}\nfact { setRealDown[X, 0.5] and setReal[Y, 0.5] and realEq[X, Y] }\nrun {}");
    sat("sig X, Y in Real {}\nfact { setRealUp[X, 0.5] and setReal[Y, 0.5] and realEq[X, Y] }\nrun {}");
    // Second arg must still be a decimal literal.
    build_err(
        "sig X, Y in Real {}\nfact { setRealNearest[X, Y] }\nrun {}",
        "decimal literal",
    );
}

#[test]
fn approx_literal_paren_spelling() {
    // `(d)` in comparisons: bracket semantics (verdict-exact).
    sat("sig R in Real {}\nfact { setReal[R, 0.0625] and realLT[R, (0.1)] }\nrun {}");
    unsat("sig R in Real {}\nfact { setReal[R, 0.125] and realLT[R, (0.1)] }\nrun {}");
    sat("sig R in Real {}\nfact { setReal[R, 0.125] and realGT[R, (0.1)] }\nrun {}");
    // Plain non-dyadic in comparisons is UNSAT (no approximation).
    unsat("sig R in Real {}\nfact { setReal[R, 0.0625] and realLT[R, 0.1] }\nrun {}");
    // `(d)` in `=` binds nearest.
    sat("sig X, Y in Real {}\nfact { setReal[X, (0.5)] and setReal[Y, 0.5] and realEq[X, Y] }\nrun {}");
    sat("sig X, Y in Real {}\nfact { setReal[X, (0.1)] and setRealNearest[Y, 0.1] and realEq[X, Y] }\nrun {}");
    // Plain non-dyadic in exact positions is UNSAT (composable).
    unsat("sig A, B, C in Real {}\nfact { setReal[A, 0.5] and realAdd[C, A, 0.1] }\nrun {}");
    unsat("sig R in Real {}\nfact { setReal[R, 0.5] and R = 0.1 }\nrun {}");
    // `(d)` in `=` with no dyadic centre equal is likewise UNSAT.
    unsat("sig R in Real {}\nfact { setReal[R, 0.5] and R = (0.1) }\nrun {}");
    unsat("sig R in Real {}\nfact { R = 0.1 }\nrun {}");
    // Both-literal approximable equality: nearest-centre equality.
    sat("pred p { (0.1) = (0.1) }\nrun p");
}

#[test]
fn real_arith_is_exact() {
    // 0.5 + 0.5 = 1.0 exactly.
    sat("sig A, B, C in Real {}\nfact { setReal[A, 0.5] and setReal[B, 0.5] and realAdd[C, A, B] and realEq[C, 1.0] }\nrun {}");
    unsat("sig A, B, C in Real {}\nfact { setReal[A, 0.5] and setReal[B, 0.5] and realAdd[C, A, B] and realLT[1.0, C] }\nrun {}");
    // 1.5 - 0.5 = 1.0.
    sat("sig A, B, C in Real {}\nfact { setReal[A, 1.5] and setReal[B, 0.5] and realSub[C, A, B] and realEq[C, 1.0] }\nrun {}");
    // 1.5 * 2.0 = 3.0.
    sat("sig A, C in Real {}\nfact { setReal[A, 1.5] and realMul[C, A, 2.0] and realEq[C, 3.0] }\nrun {}");
    unsat("sig A, C in Real {}\nfact { setReal[A, 1.5] and realMul[C, A, 2.0] and realEq[C, 2.0] }\nrun {}");
    // 3.0 / 0.5 = 6.0 (cross-multiplied, exact).
    sat("sig A, C in Real {}\nfact { setReal[A, 3.0] and realDiv[C, A, 0.5] and realEq[C, 6.0] }\nrun {}");
    // Division by zero is UNSAT.
    unsat("sig A, B, C in Real {}\nfact { setReal[B, 0.0] and realDiv[C, A, B] }\nrun {}");
}

#[test]
fn real_comparisons() {
    sat("sig A, B in Real {}\nfact { setReal[A, 1.5] and setReal[B, 4.0] and realLT[A, B] }\nrun {}");
    unsat("sig A, B in Real {}\nfact { setReal[A, 1.5] and setReal[B, 4.0] and realLT[B, A] }\nrun {}");
    sat("sig A in Real {}\nfact { setReal[A, 1.5] and realLTE[A, 1.5] }\nrun {}");
    sat("sig A, B in Real {}\nfact { setReal[A, 0.5] and setReal[B, 0.5] and realEq[A, B] }\nrun {}");
    unsat("sig A, B in Real {}\nfact { setReal[A, 0.5] and setReal[B, 0.25] and realEq[A, B] }\nrun {}");
}

#[test]
fn real_value_equality_via_eq() {
    // Flat idiom: `sig R in Real` + `R = lit` binds the centre bit set.
    sat("sig R in Real {}\nfact { R = 0.5 }\nrun {}");
    unsat("sig R in Real {}\nfact { R = 0.5 and R = 1.5 }\nrun {}");
    sat("sig R in Real {}\nfact { R = 0.5 and R != 1.5 }\nrun {}");
}

#[test]
fn ereal_is_a_narrower_domain_not_a_parent() {
    // `Real` and `EReal` are two independent type domains over the lane
    // partition, and `Real` is the narrower one: an exact real is an
    // `EReal` with no error bits, so every `Real` value is a legal
    // `EReal` value, but not the other way round.
    sat("sig R in Real {}\npred p { some r: R | r in EReal }\nrun p");
    sat("sig R in EReal {}\npred p { some r: R | r in Real }\nrun p");
    // A `Real` value has no `p`/`k` bits, so those lanes read 0 (the
    // error lanes have to exist first: they are allocated on an explicit
    // `EReal`/`$P` mention, like `Int` atoms on `for N Int`).
    sat("sig R in Real {}\nfact { setReal[R, 0.5] }\npred p { some $P and R.p = 0 and R.k = 0 }\nrun p");
    // A `p`/`k` bit is out of the `Real` domain.
    unsat("sig R in Real {}\nfact { R = {M$0, P$2} }\nrun {}");
    // `for N EReal` is rejected like `for N Real`: the domain derives.
    build_err("pred p { some $P }\nrun p for 2 EReal", "not scoped in flat mode");
    build_err("sig X extends EReal {}\nrun {}", "cannot extend EReal");
    sat("sig X in EReal {}\nrun {}");
}

#[test]
fn flat_partition_bans_and_shape() {
    // `Real = $M + $E` as sets; the halves are disjoint and cover.
    sat("pred p { Real = $M + $E }\nrun p");
    sat("pred p { no ($M & $E) and some Real }\nrun p");
    // `Real` is exact: its population is the full lane set, so its
    // cardinality is M+E with no scope of its own.
    sat("pred p { #Real = 13 }\nrun p for 8 $M, 5 $E");
    // There is no lane relation any more, so no lane can warn.
    {
        let m = parse_module("sig X in Real {}\nfact { setReal[X, 0.5] }\nrun {}").expect("parse");
        let cnf = run(&m, 0).expect("run");
        assert!(
            cnf.warnings.iter().all(|w| !w.contains("Real.m") && !w.contains("Real.e")),
            "lane warnings leaked: {:?}",
            cnf.warnings
        );
    }
    // User `extends Real` would add atoms outside the partition.
    build_err("sig X extends Real {}\nrun {}", "cannot extend Real");
    // `for N Real` is rejected: the population derives as `$M + $E`.
    build_err("pred p { some $M }\nrun p for 2 Real", "not scoped in flat mode");
    // A lane is an integer, so it has no set reading: `Real.m` is the
    // whole domain's lane (loudly), and a lane read in a set position is
    // a category error rather than a silent join.
    build_err("pred p { Real.m = 3 }\nrun p", "whole `Real` domain");
    build_err("sig R in Real {}\npred p { R.m in R }\nrun p", "reads a bit lane");
}

#[test]
fn real_comparisons_gt_gte() {
    sat("sig A, B in Real {}\nfact { setReal[A, 1.5] and setReal[B, 4.0] and realGT[B, A] }\nrun {}");
    unsat("sig A, B in Real {}\nfact { setReal[A, 1.5] and setReal[B, 4.0] and realGT[A, B] }\nrun {}");
    unsat("sig A, B in Real {}\nfact { setReal[A, 0.5] and setReal[B, 0.5] and realGT[A, B] }\nrun {}");
    sat("sig A in Real {}\nfact { setReal[A, 1.5] and realGTE[A, 1.5] }\nrun {}");
    unsat("sig A, B in Real {}\nfact { setReal[A, 1.5] and setReal[B, 4.0] and realGTE[A, B] }\nrun {}");
}

#[test]
fn for_zero_real_with_literal_const() {
    // Literals are constants needing no atoms (no scope at all).
    sat("pred p { realEq[0.5, 0.5] }\nrun p");
    unsat("pred p { realEq[0.5, 1.5] }\nrun p");
}

#[test]
fn in_sig_value_uniqueness() {
    // Flat replacement for extender-collapse: two `in`-sigs pinned to
    // the same literal denote the same bit set (bitmask bijectivity).
    sat("sig A, B in Real {}\nfact { setReal[A, 0.5] and setReal[B, 0.5] }\npred p { A = B }\nrun p");
    unsat("sig A, B in Real {}\nfact { setReal[A, 0.5] and setReal[B, 1.5] }\npred p { A = B }\nrun p");
    sat("sig X in Real {}\nfact { setRealNearest[X, 1.2345] }\nrun {}");
}

#[test]
fn scalar_values_are_dead() {
    // Documents the flat verdict: a single atom cannot hold an (m, e)
    // centre, so scalar quantification over `Real` is UNSAT. Use
    // `sig R in Real` (bit sets) instead.
    unsat("pred p { some x: Real | setReal[x, 0.5] }\nrun p");
    unsat("pred p { some x: Real | x.composeReal[1, -1] }\nrun p");
}

#[test]
fn real_succ_pred() {
    // Successor is exact and minimal (default widths: succ(0.5) = 0.5625).
    sat("sig A, B in Real {}\nfact { setReal[A, 0.5] and realSucc[B, A] and realEq[B, 0.5625] }\nrun {}");
    unsat("sig A, B in Real {}\nfact { setReal[A, 0.5] and realSucc[B, A] and realEq[B, 1.5] }\nrun {}");
    // Predecessor mirrors (pred(0.5625) = 0.5).
    sat("sig A, B in Real {}\nfact { setReal[A, 0.5625] and realPred[B, A] and realEq[B, 0.5] }\nrun {}");
    // Negatives mirror through zero (succ(-0.5) = -pred(0.5)).
    sat("sig A, B in Real {}\nfact { setReal[A, -0.5] and realSucc[B, A] and realEq[B, -0.46875] }\nrun {}");
    unsat("sig A, B in Real {}\nfact { setReal[A, -0.5] and realSucc[B, A] and realEq[B, -0.5625] }\nrun {}");
    // Zero steps to ±(1, emin).
    sat("sig A, B in Real {}\nfact { setReal[A, 0.0] and realSucc[B, A] and realGT[B, 0.0] }\nrun {}");
    // Top of lane has no successor.
    unsat("sig A, B in Real {}\nfact { realSucc[B, A] and A.m = 15 and A.e = 7 }\nrun {}");
}

#[test]
fn real_succ_pred_is_the_only_form() {
    // A value is a set of lane bits, so there is no single atom to hold a
    // successor: the predicate form (over an `in`-sig) is the only one, and
    // the old `realUp[x]`/`realDown[x]` function form is gone from the
    // language.
    sat("sig A, B, C in Real {}\nfact { setReal[A, 0.5] and realSucc[B, A] and realPred[C, B] and realEq[A, C] }\nrun {}");
    unsat("sig A, B in Real {}\nfact { setReal[A, 0.5] and realSucc[B, A] and realEq[B, 1.5] }\nrun {}");
    // The removed names are rejected loudly rather than silently re-read.
    for name in ["realUp", "realDown"] {
        build_err(
            &format!(
                "fun f[]: one Real {{ {name}[0.5] }}\nsig S {{ x: one Real }}\nfact {{ S.x = f[] }}\nrun {{}}"
            ),
            "no longer exists",
        );
    }
}

#[test]
fn lane_sig_scope_controls_widths() {
    // Flat lane sigs: `for N $M` etc. set lane populations directly.
    sat("pred p { #$M = 8 }\nrun p for 8 $M, 5 $E");
    unsat("pred p { #$M = 8 }\nrun p for 4 $M, 5 $E");
    sat("pred p { #$E = 5 }\nrun p for 8 $M, 5 $E");
    // Lane atoms live inside the `Real` closure (`Real = $M + $E`).
    sat("pred p { $M in Real and $E in Real }\nrun p");
    // Omitted entries keep the `for W Int` rule behavior.
    sat("sig R in Real {}\nfact { setReal[R, 0.5] }\nrun {}");
}

#[test]
fn compose_real_binds_lanes() {
    // (1, -1) is 0.5, agreeing with setReal.
    sat("sig R in Real {}\nfact { R.composeReal[1, -1] }\nrun {}");
    sat("sig X, Y in Real {}\nfact { X.composeReal[1, -1] and setReal[Y, 0.5] and realEq[X, Y] }\nrun {}");
    // Even nonzero mantissae are ill-formed (UNSAT, not error).
    unsat("sig R in Real {}\nfact { R.composeReal[2, -1] }\nrun {}");
    // Lane-read args copy another value's centre.
    sat("sig X, Y in Real {}\nfact { setReal[X, 1.5] and Y.composeReal[X.m, X.e] and realEq[X, Y] }\nrun {}");
    // Out-of-range literals fail loudly (m at default widths: [-16, 15]).
    build_err(
        "sig R in Real {}\nfact { R.composeReal[16, 0] }\nrun {}",
        "outside the m lane range",
    );
    // Quantified variables are rejected loudly, never misread.
    build_err(
        "sig R in Real {}\nfact { all mm: Int | R.composeReal[mm, 0] }\nrun {}",
        "integer literal or lane read",
    );
    // User fun derivatives work (args substitute pre-lowering; the fun
    // returns a bit set directly since comprehensions range over atoms).
    sat("fun mkHalf[]: Real { mbit[0] + ebit[0] + ebit[1] + ebit[2] + ebit[3] }\nsig Y in Real {}\nfact { setReal[Y, 0.5] }\npred p { realEq[mkHalf[], Y] }\nrun p");
}

#[test]
fn holder_sig_idiom() {
    // The user's proposed shape: holders carry values as `r` bit sets.
    sat("some sig H { r: Real }\nfact { setReal[H.r, 0.5] }\nrun {}");
    sat("some sig H { r: Real }\nfact { setReal[H.r, 0.5] }\npred p { H.r = 0.5 }\nrun p");
    unsat("some sig H { r: Real }\nfact { setReal[H.r, 0.5] }\npred p { H.r = 1.5 }\nrun p");
}

#[test]
fn bit_singletons_spell_lane_sets() {
    // Exact set identity with bits: 0.5 is {M$0} + {-1 as E bits}.
    sat("sig R in Real {}\nfact { R = mbit[0] + ebit[0] + ebit[1] + ebit[2] + ebit[3] }\nrun {}");
    unsat("sig R in Real {}\nfact { R = mbit[0] + ebit[0] + ebit[1] + ebit[2] + ebit[3] and realEq[R, 1.5] }\nrun {}");
    // Integer readings agree with the bit spelling.
    sat("sig R in Real {}\nfact { R.m = 3 }\npred p { R = mbit[0] + mbit[1] + ebit[0] + ebit[1] + ebit[2] + ebit[3] }\nrun p");
    // Out-of-range positions fail loudly (M=5 at default widths). A
    // lane is an integer, so the check belongs on the singleton itself.
    build_err("pred p { {mbit[7]} = 1 }\nrun p", "outside the lane range");
    // … and reading a lane in a set position is a category error, not a
    // join against an unresolvable label.
    build_err(
        "sig R in Real {}\nfact { R.m = 3 }\npred p { R.m in Real }\nrun p",
        "reads a bit lane",
    );
    // `$M` is a builtin domain: always exactly the full bit set.
    sat("pred p { #$M = 5 }\nrun p for 5 $M");
    sat("pred p { some $M }\nrun p for 5 $M");
}

#[test]
fn query_find_real_arith_oracle() {
    // `{r in Real | r.realAdd[a, b]}` answers via the exact-centre
    // oracle and presents a lane-bit *set* — find-forms denote sets.
    // The `:`-form stays purely enumerative (atom population): the same
    // body yields `{}` there. No shape-dependent magic.
    use alloy_front_rs::{display::decode_bitset, effective_int_count, query_value, QueryValue};
    use alloy_kodkod_rs::mepk::MepkWidths;
    use alloy_kodkod_rs::real::{
        decimal_to_real_rounded, real_add, real_div, real_mul, RealCenter, RealRound,
    };
    // Assert a find-form query yields the lane-bit set of `expect`.
    fn assert_bitset(
        m: &alloy_front_rs::Module,
        scope: &alloy_front_rs::Scope,
        cnf: &alloy_front_rs::Cnf,
        inst: &alloy_front_rs::Instance,
        src: &str,
        expect: RealCenter,
    ) {
        match query_value(m, scope, cnf, src, inst).expect("query arith find-form") {
            QueryValue::Set(arity, ts) => {
                assert_eq!(arity, 1, "{src}");
                let idxs: Vec<u32> = ts.index_view().iter().map(|i| i as u32).collect();
                let text = decode_bitset(inst.universe(), &idxs).expect("decodes as Real");
                assert_eq!(
                    text,
                    format!("{} [m={} e={}]", expect.centre_short(), expect.m, expect.e),
                    "{src}"
                );
            }
            QueryValue::Real(..) => panic!("expected lane-bit set for {src}"),
            QueryValue::Int(..) | QueryValue::Bool(..) => panic!("expected set for {src}"),
        }
    }
    let src = "sig A, B in Real {}\nfact { A = (1.2) and B = (-3.6) }\nrun {} for 10 Int";
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("run");
    let inst = solve(&cnf).expect("solve").expect("SAT");
    let scope = &m.commands[0].scope;
    let w = MepkWidths::from_env(effective_int_count(scope)).expect("widths");
    let a = decimal_to_real_rounded("1.2", Some(w.m_width), RealRound::Nearest).expect("a");
    let b = decimal_to_real_rounded("-3.6", Some(w.m_width), RealRound::Nearest).expect("b");
    let sum = real_add(&a, &b, 1).expect("sum");
    assert!(sum.is_valid(Some(w.m_width)));
    // User case, incl. `set`-stripped domain and selectors (all agree on
    // the unique value).
    for src in [
        "{x in Real | x.realAdd[A, B]}",
        "{x in set Real | x.realAdd[A, B]}",
        "{min x in Real | x.realAdd[A, B]}",
        "{max x in Real | x.realAdd[A, B]}",
        "{any x in Real | x.realAdd[A, B]}",
    ] {
        assert_bitset(&m, scope, &cnf, &inst, src, sum);
    }
    // `:`-form purity: the same body enumerates lane atoms, none of which
    // satisfies the whole-value constraint.
    match query_value(&m, scope, &cnf, "{x: Real | x.realAdd[A, B]}", &inst)
        .expect("query colon form")
    {
        QueryValue::Set(arity, ts) => {
            assert_eq!(arity, 1);
            assert_eq!(ts.len(), 0);
        }
        QueryValue::Real(..) | QueryValue::Int(..) | QueryValue::Bool(..) => {
            panic!("expected (empty) set for colon form")
        }
    }
    // Overflowing `A - B`: lane circuits wrap (solver parity, 1229 mod
    // 2^11 = -819); enumeration finds the wrapped value.
    let wrapped = RealCenter::new(-819, -8).expect("wrapped");
    assert_bitset(&m, scope, &cnf, &inst, "{x in Real | x.realSub[A, B]}", wrapped);
    // Sub/mul/div on exactly representable small values (wide enough
    // lanes that results stay in range).
    let src2 = "sig A, B in Real {}\nfact { A = 1.5 and B = 0.5 }\nrun {} for 8 Int";
    let m2 = parse_module(src2).expect("parse");
    let cnf2 = run(&m2, 0).expect("run");
    let inst2 = solve(&cnf2).expect("solve").expect("SAT");
    let scope2 = &m2.commands[0].scope;
    let w2 = MepkWidths::from_env(effective_int_count(scope2)).expect("widths");
    let a2 = decimal_to_real_rounded("1.5", Some(w2.m_width), RealRound::Nearest).unwrap();
    let b2 = decimal_to_real_rounded("0.5", Some(w2.m_width), RealRound::Nearest).unwrap();
    for (src, expect) in [
        ("{x in Real | x.realSub[A, B]}", real_add(&a2, &b2, -1).unwrap()),
        ("{x in Real | x.realMul[A, B]}", real_mul(&a2, &b2).unwrap()),
        ("{x in Real | x.realDiv[A, B]}", real_div(&a2, &b2).unwrap()),
        // Backward: solve for an input side (`A = x + B`).
        ("{x in Real | A.realAdd[x, B]}", real_add(&a2, &b2, -1).unwrap()),
    ] {
        assert_bitset(&m2, scope2, &cnf2, &inst2, src, expect);
    }
    // Scaled exact zero carries `E` bits: presented as a set.
    let src4 = "sig A, B in Real {}\nfact { A = (0.5) and B = (0.5) }\nrun {} for 8 Int";
    let m4 = parse_module(src4).expect("parse");
    let cnf4 = run(&m4, 0).expect("run");
    let inst4 = solve(&cnf4).expect("solve").expect("SAT");
    let scope4 = &m4.commands[0].scope;
    let w4 = MepkWidths::from_env(effective_int_count(scope4)).expect("widths");
    let a4 = decimal_to_real_rounded("0.5", Some(w4.m_width), RealRound::Nearest).unwrap();
    let zero_scaled = real_add(&a4, &a4, -1).unwrap();
    assert_eq!(zero_scaled.m, 0);
    assert_bitset(&m4, scope4, &cnf4, &inst4, "{x in Real | x.realSub[A, B]}", zero_scaled);
    // Bit-free exact zero has no lane bits: the `Real` reading is kept so
    // the value stays displayable instead of collapsing to `{}`.
    let src3 = "sig A, B in Real {}\nfact { A = 1.0 and B = 1.0 }\nrun {} for 8 Int";
    let m3 = parse_module(src3).expect("parse");
    let cnf3 = run(&m3, 0).expect("run");
    let inst3 = solve(&cnf3).expect("solve").expect("SAT");
    let scope3 = &m3.commands[0].scope;
    match query_value(&m3, scope3, &cnf3, "{x in Real | x.realSub[A, B]}", &inst3)
        .expect("query zero diff")
    {
        QueryValue::Real(v) => assert_eq!(v.m, 0),
        QueryValue::Set(..) => panic!("expected Real reading for bit-free exact zero"),
        QueryValue::Int(..) | QueryValue::Bool(..) => panic!("expected Real for zero"),
    }
}
