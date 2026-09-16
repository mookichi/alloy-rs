//! Bit-vector Int model: unsigned atoms, bitset `=`, `Signed`, `MSB`.
//!
//! - `for W Int` gives W atoms `{0, .., W-1}` (default W = 4).
//! - Integer literals stay integers; `7 = {0, 1, 2}` holds since
//!   `bits(7)` is `{0, 1, 2}`.
//! - `{MSB}` is the top-atom singleton (`{3}` at W = 4).
//! - `sig X in Signed` / `v: Signed` mirror `Int` over the same atoms.

use alloy_front_rs::{parse_module, query_value, run, solve, QueryValue};

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
fn seven_eq_bitset() {
    sat("pred p { 7 = {0, 1, 2} }\nrun p for 4 Int");
    // default scope (W = 4) materializes via the bitset itself
    sat("pred p { 7 = {0, 1, 2} }\nrun p for 3");
}

#[test]
fn seven_ne_wrong_bitset() {
    unsat("pred p { 7 = {0, 1, 3} }\nrun p for 4 Int");
    unsat("pred p { 7 != {0, 1, 2} }\nrun p for 4 Int");
}

#[test]
fn plus_union_matches_braces() {
    // Brace unions compare as sets: `7 = {0}+{1}+{2}` agrees with `{0,1,2}`.
    // (Bare `0+1+2` in int position is arithmetic = 10, not a set.)
    sat("pred p { 7 = {0} + {1} + {2} }\nrun p for 4 Int");
}

#[test]
fn brace_set_int_arithmetic() {
    // A braced set in integer position reads as its bit-vector value
    // (`{0, 1}` is 3 = 2^0 + 2^1), so integer operators apply.
    sat("pred p { {0, 1} * 2 = 3 * 2 }\nrun p for 4 Int");
    sat("pred p { {0, 1} * 2 = 6 }\nrun p for 4 Int");
    sat("pred p { 2 * {0, 1} = 6 }\nrun p for 4 Int");
    sat("pred p { {0, 1} * 2 != 7 }\nrun p for 4 Int");
    unsat("pred p { {0, 1} * 2 != 6 }\nrun p for 4 Int");
    sat("pred p { {0, 1} < 4 }\nrun p for 4 Int");
    // Unlike `sum e` (Σ atom values: `sum {0, 1}` is 1), the bare set
    // reads Σ 2^value.
    sat("pred p { sum {0, 1} = 1 }\nrun p for 4 Int");
}

#[test]
fn brace_set_keeps_set_reading() {
    // `+`/`-` over brace sets keep the legacy set reading (rewound from
    // the int-first attempt): union, difference, and bare singletons.
    sat("pred p { {0} + {1} = {0, 1} }\nrun p for 4 Int");
    sat("pred p { ({0, 1} - {0}) = {1} }\nrun p for 4 Int");
    // Non-ground brace sets rewind too: `{A} = {B}` is set equality,
    // so disjoint forced singletons are UNSAT (an int commit of 0 = 0
    // would wrongly report SAT).
    unsat("sig A {} sig B {} pred p { some A and some B and {A} = {B} }\nrun p for 1");
    sat("sig A {} sig B {} pred p { some A and some B and {A} = {A} }\nrun p for 1");
}

#[test]
fn msb_is_top_atom() {
    sat("pred p { {MSB} = {3} }\nrun p for 4 Int");
    sat("pred p { MSB = 3 }\nrun p for 4 Int");
    // MSB in int position sums the singleton: sum {MSB} = 3.
    sat("pred p { sum {MSB} = 3 }\nrun p for 4 Int");
}

#[test]
fn int_atoms_count() {
    sat("run { #Int = 4 } for 4 Int");
    unsat("run { #Int = 5 } for 4 Int");
    // overall scope does not affect Int; default W = 4.
    sat("sig A {}\nrun { #Int = 4 } for 3");
}

#[test]
fn int_atom_values() {
    // atoms are exactly 0..W-1: 3 is in Int, 4 is out of scope.
    sat("pred p { 3 in Int }\nrun p for 4 Int");
    let m = parse_module("pred p { 4 in Int }\nrun p for 4 Int").expect("parse");
    assert!(run(&m, 0).is_err(), "atom 4 out of scope at W = 4");
}

#[test]
fn sig_in_signed() {
    sat("sig X in Signed {}\npred p { some X }\nrun p for 4 Int");
    // Signed shares Int's atoms.
    sat("sig X in Signed {}\npred p { X in Int }\nrun p for 4 Int");
}

#[test]
fn field_typed_signed() {
    sat("some sig Y { v: Signed }\nrun {} for 4 Int");
    sat("some sig Y { v: Signed }\npred p { some y: Y | y.v in Int }\nrun p for 4 Int");
}

#[test]
fn set_idiom_preserved() {
    // `x = 5` with a non-literal side stays a singleton set equality,
    // including field = constant.
    sat("sig A { x: Int }\npred p { some a: A | a.x = 5 }\nrun p for 8 Int");
    sat("sig A { x: Int }\npred p { some a: A | a.x = {5} }\nrun p for 8 Int");
    // membership keeps singleton semantics.
    sat("sig A { x: Int }\npred p { some a: A | a.x in {5} }\nrun p for 8 Int");
    sat("sig A { x: Int }\npred p { some a: A | 5 in a.x }\nrun p for 8 Int");
}

#[test]
fn int_w_rejected() {
    // `Int[w]` is gone: `Int[8]` is the join `8.Int` (arity 1 vs 1).
    assert!(
        parse_module("sig A { x: Int[8] }\nrun {} for 3").is_err()
            || run(
                &parse_module("sig A { x: Int[8] }\nrun {} for 3").expect("parse"),
                0
            )
            .is_err()
    );
}

#[test]
fn int_queries_see_unsigned_atoms() {
    let src = "sig A {}\nrun { some A } for 1, 8 Int";
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("run");
    assert_eq!(cnf.bitwidth, 8);
    let inst = solve(&cnf).expect("solve").expect("SAT");
    let scope = &m.commands[0].scope;
    match query_value(&m, scope, &cnf, "#Int", &inst).expect("query #Int") {
        QueryValue::Int(v) => assert_eq!(v, 8),
        QueryValue::Set(..) => panic!("expected Int"),
        QueryValue::Bool(..) => panic!("expected Int"),
        QueryValue::Bool(..) => panic!("expected Int"),
    }
}
