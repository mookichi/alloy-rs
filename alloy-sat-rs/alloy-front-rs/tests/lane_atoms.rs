//! Members of the exact builtin domains as model-text constants: the bit
//! lanes (`M$0`, `E$1`, `P$2`, `K$0`) and the temporal step positions
//! (`Step$0`). Their positions are fixed by the scope, so they are
//! compile-time values rather than solver outputs, and they resolve in
//! models exactly like the `Int` atoms `0`..`W-1` already did. Value
//! atoms (`A$0`) stay query-only (Java parity).
//!
//! A set of lane bits carries its own sort, which decides how an
//! `=` against it reads:
//!
//! | set                              | sort           | `= 3` means |
//! |----------------------------------|----------------|-------------|
//! | one lane (`{M$0, M$1}`)          | `Signed(M)`    | the lane's signed integer |
//! | `m` + `e` (`{M$0, E$0}`)         | `Real`         | centre-value equality |
//! | a `p`/`k` bit present            | `EReal`        | `c ± R` value equality |
//! | lane bits mixed with other atoms | `Mixed`        | — (error) |
//! | no lane bits (`{0, 1}`)          | `Other`        | the ordinary bitmask |

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

fn build_err(src: &str) -> String {
    let m = parse_module(src).expect("parse");
    match run(&m, 0) {
        Ok(_) => panic!("expected build error: {src}"),
        Err(err) => format!("{err:?}"),
    }
}

fn build_err_mentioning(src: &str, want: &str) {
    let msg = build_err(src);
    assert!(msg.contains(want), "error {msg:?} should mention {want:?} ({src})");
}

fn parse_err_mentioning(src: &str, want: &str) {
    let msg = match parse_module(src) {
        Ok(_) => panic!("expected parse error: {src}"),
        Err(e) => format!("{e:?}"),
    };
    assert!(msg.contains(want), "error {msg:?} should mention {want:?} ({src})");
}

#[test]
fn single_lane_set_reads_as_that_lanes_signed_integer() {
    // Same reading as `x.m`: two's complement with the top bit negative,
    // here the `M$4` MSB at `for 4 Int` (m_width 5). Only in-range
    // literals are used below: the circuit is modular, so an out-of-range
    // literal wraps (`{M$4} = 16` and `= -16` are the same bit pattern)
    // and cannot pin a sign.
    sat("pred p { {M$0, M$1} = 3 }\nrun p");
    unsat("pred p { {M$0, M$1} = 4 }\nrun p");
    // The top bit is set, so the lane is not zero …
    unsat("pred p { {M$4} = 0 }\nrun p");
    // … and it weighs -16, making all five bits -1.
    unsat("pred p { {M$0, M$1, M$2, M$3, M$4} = 1 }\nrun p");
    sat("pred p { {M$0, M$1, M$2, M$3, M$4} = -1 }\nrun p");
    // A wider lane only moves the sign bit up; the low bits still read 3.
    sat("pred p { {M$0, M$1} = 3 }\nrun p for 8 $M, 4 $E");
    unsat("pred p { {M$7} = 0 }\nrun p for 8 $M, 4 $E");
    // Each lane is its own int-bound group: the same bits read 3 in `e`
    // and denote a different set.
    sat("pred p { {E$0, E$1} = 3 }\nrun p");
    unsat("pred p { {M$0, M$1} = {E$0, E$1} }\nrun p");
}

#[test]
fn int_atom_reading_is_untouched() {
    // The pre-existing exemption: `Int` atoms are written without `$`.
    sat("pred p { {0, 1} = 3 }\nrun p");
    sat("pred p { {0, 2} = 5 }\nrun p");
    unsat("pred p { {0, 2} = 3 }\nrun p");
}

#[test]
fn integer_and_decimal_spellings_of_a_value_agree() {
    // `{M$0, E$0}` is m=1, e=1 at the default widths, i.e. the value 2.
    // An integer in value position is that value without the decimal
    // point, so both spellings must agree — the mantissa normalisation
    // (2 = 1*2^1) is what makes `2` and `2.0` the same lane pair.
    sat("pred p { {M$0, E$0} = 2.0 }\nrun p");
    sat("pred p { {M$0, E$0} = 2 }\nrun p");
    unsat("pred p { {M$0, E$0} = 3 }\nrun p");
    unsat("pred p { {M$0, E$0} = 2.5 }\nrun p");
    // Negative values normalize the same way.
    sat("pred p { {M$0, M$1, M$2, M$3, M$4} = -1 }\nrun p");
    // `!=` is the negation of the same reading.
    unsat("pred p { {M$0, E$0} != 2.0 }\nrun p");
    sat("pred p { {M$0, E$0} != 2.5 }\nrun p");
}

#[test]
fn multi_lane_set_with_an_error_bit_is_an_ereal_value() {
    // 0.5 converts to (m=8, e=-1, p=4, k=0) at the default widths, so
    // its bit set is M$3, all four E bits, and P$2 — the same lanes
    // `erealSet[x, 0.5]` pins on a real `EReal` value.
    const HALF: &str = "{M$3, E$0, E$1, E$2, E$3, P$2}";
    sat(&format!("pred p {{ {HALF} = 0.5 }}\nrun p"));
    unsat(&format!("pred p {{ {HALF} = 0.75 }}\nrun p"));
    unsat(&format!("pred p {{ {HALF} != 0.5 }}\nrun p"));
    // Dropping the error bits changes the sort: `m`+`e` alone is a `Real`
    // centre, and 0.5 as a centre is (1, -1), not (8, -1).
    unsat("pred p { {M$3, E$0, E$1, E$2, E$3} = 0.5 }\nrun p");
    sat("pred p { {M$0, E$0, E$1, E$2, E$3} = 0.5 }\nrun p");
    // The error tracks the scale, so the zero value carries an exponent.
    sat("pred p { {E$0, E$1, P$2} = 0 }\nrun p");
    sat("pred p { {E$0, E$1, P$2} = 0.0 }\nrun p");
    // A `k` bit without a `p` bit is ill-formed: `p` reads 0, which
    // `erealWellformed` rejects, so no conversion can match it.
    unsat("pred p { {M$0, K$0} = 0.5 }\nrun p");
}

#[test]
fn lane_bit_spelling_matches_the_mbit_calls() {
    // `pbit[0] + pbit[2]` is the old spelling of `{P$0, P$2}`; the two
    // must denote the same lane value.
    sat("pred p { {pbit[0], pbit[2]} = 5 }\nrun p");
    unsat("pred p { {pbit[0], pbit[2]} = 6 }\nrun p");
    sat("pred p { {P$0, P$2} = 5 }\nrun p");
    unsat("pred p { {P$0, P$2} = 6 }\nrun p");
    sat("pred p { {mbit[0], mbit[1]} = 3 }\nrun p");
    // A value spelled with the calls, compared as a value.
    sat("pred p { {mbit[3], ebit[0], ebit[1], ebit[2], ebit[3], pbit[2]} = 0.5 }\nrun p");
}

#[test]
fn writing_a_lane_atom_allocates_its_lane() {
    // No `for` clause: mentioning `M$0` must bring the lane into being
    // (the `Int` atoms behave the same way), or the name would not
    // resolve at all.
    sat("pred p { {M$0, M$1} = 3 }\nrun p");
    sat("pred p { {P$0, P$2} = 5 }\nrun p");
    sat("pred p { some $M }\nrun p");
}

#[test]
fn a_lane_bit_set_denotes_a_value_as_a_whole() {
    // A value is its bit set, so the same text reads as a set against
    // another set and as a value against a literal.
    sat("sig R in Real {}\nfact { R = {M$0, E$0} }\npred p { R = {M$0, E$0} }\nrun p");
    sat("sig R in Real {}\nfact { R = {M$0, E$0} }\npred p { R = 2.0 }\nrun p");
    unsat("sig R in Real {}\nfact { R = {M$0, E$0} }\npred p { R = 1.0 }\nrun p");
    // Different lane groups are different sets even when both read 3.
    unsat("pred p { {M$0, M$1} = {E$0, E$1} }\nrun p");
    sat("pred p { {M$0, M$1} in $M and {E$0, E$1} in $E }\nrun p");
}

#[test]
fn unexpected_atom_combinations_are_rejected() {
    build_err_mentioning("pred p { {0, M$0} = 3 }\nrun p", "mixing lane bits");
    build_err_mentioning(
        "pred p { {M$0, M$1} = 0.5 }\nrun p",
        "holds bits of a single lane",
    );
    build_err_mentioning(
        "pred p { {M$0, E$0} > 3 }\nrun p",
        "not an integer",
    );
    // A right-hand side that is not a literal cannot be read as a value.
    build_err_mentioning(
        "sig I {}\npred p { some n: Int | {M$0, E$0} = n + 1 }\nrun p for 4 Int",
        "not an integer",
    );
}

#[test]
fn an_integer_beyond_the_lanes_fails_like_its_decimal_spelling() {
    // Out of range means the same thing either way, because the integer
    // is converted through the decimal path rather than re-implemented.
    let via_set = build_err("pred p { {M$0, E$0} = 100 }\nrun p");
    let via_decimal = build_err("sig X in Real {}\nfact { X = 100.0 }\nrun {}");
    assert!(
        via_set.contains("100.0") && via_decimal.contains("100.0"),
        "both spellings should report the same converted literal: {via_set:?} / {via_decimal:?}"
    );
}

#[test]
fn step_atoms_resolve_in_models() {
    // A step position is a named element of the exact `Step` domain,
    // fixed by `for N steps`, so it is a constant like the lane bits.
    sat("sig A {}\nrun { always (some A) and #Step$0 = 1 } for 2 steps");
    unsat("sig A {}\nrun { always (some A) and #Step$0 = 2 } for 2 steps");
    unsat("sig A {}\nrun { always (some A) and Step$0 = Step$1 } for 2 steps");
    unsat("sig A {}\nrun { always (some A) and no Step$1 } for 2 steps");
    sat("sig A {}\nrun { always (some A) and some Step$1 } for 2 steps");
}

#[test]
fn value_atoms_stay_query_only() {
    // `A$0` is a solver output, not a compile-time constant: the
    // Java-parity rejection stays (lowering-time, since the name parses).
    build_err_mentioning(
        "sig A {}\npred p { some A$0 }\nrun p for 1 A",
        "cannot contain the '$'",
    );
    // So does the ban on declaring a name with `$`, which is what keeps
    // the lane bits unshadowable.
    parse_err_mentioning("sig M$0 {}\nrun {}", "cannot contain the '$'");
    parse_err_mentioning(
        "sig S {}\npred p { all M$1: S | some M$1 }\nrun p",
        "cannot contain the '$'",
    );
}

/// A bare integer beside a *value* set is the same comparison as the
/// decimal literal: the literal is synthesized (`"3"` -> `"3.0"`) and
/// handed to the decimal path, so the two spellings cannot drift. This
/// covers the three operand shapes that carry a value sort — a value
/// sig, a holder field, and a lane-bit set — plus the guards that keep
/// the rewrite from swallowing integer comparisons.
#[test]
fn int_literal_compares_as_value() {
    // A `Real` sig, both operand orders.
    sat("sig A in Real {}\npred p { A = 3 }\nrun p");
    sat("sig A in Real {}\npred p { 3 = A }\nrun p");
    // Same value, so the lanes must agree with the decimal spelling.
    sat("sig A in Real {}\npred p { A = 3 and A.m = 3 and A.e = 0 }\nrun p");
    unsat("sig A in Real {}\npred p { A = 3 and A.m = 4 }\nrun p");
    // `!=` negates the same body, in both orders.
    sat("sig A in Real {}\npred p { A != 3 and A = 4.0 }\nrun p");
    unsat("sig A in Real {}\npred p { A = 3 and 3 != A }\nrun p");
    unsat("sig A in Real {}\npred p { A = 3 and A != 3 }\nrun p");

    // An `EReal` sig pins `p`/`k` just as the decimal literal does.
    sat("sig A in EReal {}\npred p { A = 3.0 and A.p = 4 and A.k = 0 }\nrun p");
    unsat("sig A in EReal {}\npred p { A = 3.0 and A.p = 2 }\nrun p");

    // A holder field, qualified per owner and whole-relation.
    sat("sig S { x: set Real }\nfact { all o: S | o.x = 2 }\nrun {} for exactly 2 S");
    sat("sig S { x: set EReal, y: set EReal }\nfact { all o: S | o.x = 2 and o.y = 3 }\nrun {} for exactly 2 S");
    // Two pins on one field conflict.
    unsat("sig S { x: set EReal }\nfact { S.x = 3.0 and S.x = 4.0 }\nrun {} for exactly 1 S");
}

#[test]
fn int_comparison_guards_survive() {
    // An `Int`/`Signed` set keeps the bitmask reading: `A = 3` selects
    // the atom `3`, it is not a value comparison.
    sat("sig A in Int {}\npred p { A = 3 }\nrun p");
    sat("sig A in Signed {}\npred p { A = 3 }\nrun p");
    // A lane read is an integer, not a value.
    sat("sig A in Real {}\npred p { A.m = 3 }\nrun p");
    unsat("sig A in Real {}\npred p { A.m = 3 and A.m = 4 }\nrun p");
    // A single lane's bit set is an integer too.
    sat("sig A in Real {}\npred p { {M$0, M$1} = 3 }\nrun p");
    // A plain relation has no value sort, so the mismatch is reported
    // rather than silently reinterpreted.
    build_err_mentioning(
        "sig S {}\npred p { S = 3 }\nrun p",
        "integer comparison/arithmetic",
    );
}
