//! Builtin `Real` in flat mode: `Real = $M + $E` as sets (no `Real$i`
//! value atoms; `for N Real` is rejected, the population derives from
//! `for N $M, M $E`). Values are bit sets held by `in`-sigs or holder
//! sigs (`sig R in Real {}`, `some sig H { r: Real }`); scalar
//! quantification (`some x: Real`) cannot hold `(m, e)` centres.
//! `EReal` stays reified as the control group.

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
fn ereal_models_still_use_ereal_reading() {
    // `EReal`-rooted `= lit` keeps the legacy lane-exact reading (control).
    sat("one sig R1 extends EReal {}\nfact { R1 = 0.5 }\nrun {} for 2 EReal");
    unsat("one sig R1 extends EReal {}\nfact { R1 = 0.5 and R1 = 1.5 }\nrun {} for 2 EReal");
}

#[test]
fn flat_partition_bans_and_shape() {
    // `Real = $M + $E` as sets; the halves are disjoint and cover.
    sat("pred p { Real = $M + $E }\nrun p");
    sat("pred p { no ($M & $E) and some Real }\nrun p");
    // User `extends Real` would add atoms outside the partition.
    build_err("sig X extends Real {}\nrun {}", "cannot extend Real");
    // `for N Real` is rejected: the population derives as `$M + $E`.
    build_err("pred p { some $M }\nrun p for 2 Real", "not scoped in flat mode");
    // Scope guard survives: EReal cannot exceed the derived Real budget.
    build_err(
        "pred p { some x: EReal, y: Real | erealWellformed[x] and realWellformed[y] }\nrun p for 1 $M, 1 $E",
        "exceeds",
    );
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
fn real_up_down_pred_forms() {
    // `realSucc`/`realPred` pred forms (the `realUp[x]` function form
    // needs a scalar witness and has no flat reading).
    sat("sig A, B, C in Real {}\nfact { setReal[A, 0.5] and realSucc[B, A] and realPred[C, B] and realEq[A, C] }\nrun {}");
    unsat("sig A, B in Real {}\nfact { setReal[A, 0.5] and realSucc[B, A] and realEq[B, 1.5] }\nrun {}");
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
    // Out-of-range positions fail loudly (M=5 at default widths).
    build_err(
        "sig R in Real {}\nfact { R.m = mbit[7] }\nrun {}",
        "outside the lane range",
    );
    // `$M` is a builtin domain: always exactly the full bit set.
    sat("pred p { #$M = 5 }\nrun p for 5 $M");
    sat("pred p { some $M }\nrun p for 5 $M");
}

#[test]
#[ignore = "item 5 hold: REPL lane-oracle reads reified Real.m/e instance tuples"]
fn query_real_up_down_uses_oracle() {
    // Reported REPL case: with `one sig X extends Real`, `Real = {X$0}`,
    // so the desugared `{ $r: Real | realSucc[$r, X] }` enumerates to
    // `{}`; `:query realUp[X]` must answer via the lane oracle instead.
    use alloy_front_rs::{effective_int_count, query_value, QueryValue};
    use alloy_kodkod_rs::mepk::MepkWidths;
    use alloy_kodkod_rs::real::{decimal_to_real_rounded, next_down, next_up, RealRound};
    let src = "one sig X extends Real {}\nfact { X.setRealNearest[0.13] }\nrun {} for 12 Int";
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("run");
    let inst = solve(&cnf).expect("solve").expect("SAT");
    let scope = &m.commands[0].scope;
    let w = MepkWidths::from_env(effective_int_count(scope)).expect("widths");
    let x = decimal_to_real_rounded("0.13", Some(w.m_width), RealRound::Nearest).expect("0.13");
    let expect_up = next_up(&x, w.m_width, w.e_width).expect("succ");
    let expect_down = next_down(&x, w.m_width, w.e_width).expect("pred");
    match query_value(&m, scope, &cnf, "realUp[X]", &inst).expect("query realUp[X]") {
        QueryValue::Real(v) => assert_eq!(v, expect_up),
        QueryValue::Set(..) => panic!("expected computed Real"),
        QueryValue::Int(..) => panic!("expected computed Real"),
        QueryValue::Bool(..) => panic!("expected computed Real"),
    }
    match query_value(&m, scope, &cnf, "realDown[X]", &inst).expect("query realDown[X]") {
        QueryValue::Real(v) => assert_eq!(v, expect_down),
        QueryValue::Set(..) => panic!("expected computed Real"),
        QueryValue::Int(..) => panic!("expected computed Real"),
        QueryValue::Bool(..) => panic!("expected computed Real"),
    }
    // Literal argument folds without an instance atom.
    match query_value(&m, scope, &cnf, "realUp[0.5]", &inst).expect("query realUp[0.5]") {
        QueryValue::Real(v) => {
            let half = decimal_to_real_rounded("0.5", Some(w.m_width), RealRound::Nearest).unwrap();
            assert_eq!(v, next_up(&half, w.m_width, w.e_width).unwrap());
        }
        QueryValue::Set(..) => panic!("expected computed Real"),
        QueryValue::Int(..) => panic!("expected computed Real"),
        QueryValue::Bool(..) => panic!("expected computed Real"),
    }
    // Predicate-shaped comprehension over the full `Real` type answers
    // through the same oracle (both orientations).
    for (src, expect) in [
        ("{x: Real | x.realSucc[X]}", expect_up),
        ("{x: Real | x.realPred[X]}", expect_down),
        ("{x: Real | X.realSucc[x]}", expect_down),
        ("{x: Real | X.realPred[x]}", expect_up),
    ] {
        match query_value(&m, scope, &cnf, src, &inst).expect("query succ comprehension") {
            QueryValue::Real(v) => assert_eq!(v, expect, "{src}"),
            QueryValue::Set(..) => panic!("expected computed Real for {src}"),
            QueryValue::Int(..) => panic!("expected computed Real for {src}"),
            QueryValue::Bool(..) => panic!("expected computed Real for {src}"),
        }
    }
}
