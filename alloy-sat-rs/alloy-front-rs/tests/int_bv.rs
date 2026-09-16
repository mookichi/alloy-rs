//! Bit-vector `Int`: unsigned atoms + lazy int-atom allocation.
//!
//! - `for W Int` gives W atoms `{0, .., W-1}` and W-bit circuits capped at
//!   30 (`E = min(W, 30)`); bare `Int` keeps the command default (else 4).
//! - `Int[w]` per-occurrence widths are gone: `Int[8]` is the join `8.Int`
//!   (arity 1 vs 1) and fails.
//! - Int atoms exist in the universe/bounds only when Int is used as a
//!   set (or an explicit `for N Int` scope requests them); Int-free
//!   models pay zero universe cost.

use alloy_front_rs::{
    effective_bitwidth, effective_int_count, module_needs_int_atoms, parse_module, query_value,
    run, solve, QueryValue,
};

fn scope_of(src: &str) -> alloy_front_rs::Scope {
    let m = parse_module(src).expect("parse");
    m.commands[0].scope.clone()
}

#[test]
fn int_brackets_rejected() {
    // `Int[8]` is the join `8.Int` (arity 1 vs 1): an error, either at
    // parse time or at lowering.
    for src in [
        "sig A { x: Int[8] }\nrun {} for 3",
        "sig A { x: int[5] }\nrun {} for 3",
        "sig A { x: Int[0] }\nrun {} for 3",
        "sig A { x: Int[33] }\nrun {} for 3",
        "sig A { x: Int[x] }\nrun {} for 3",
    ] {
        let parsed = parse_module(src);
        assert!(
            parsed.is_err() || parsed.map(|m| run(&m, 0)).expect("parse").is_err(),
            "Int[...] must fail: {src}"
        );
    }

    // bare Int still defaults to the command scope (else 4 atoms)
    let m = parse_module("sig A { x: Int }\nrun {} for 3").expect("parse bare Int");
    let scope = &m.commands[0].scope;
    assert_eq!(effective_bitwidth(&m, scope), 4);
    assert_eq!(effective_int_count(scope), 4);
    assert!(module_needs_int_atoms(&m, scope));
}

#[test]
fn scope_sets_width_and_atoms() {
    let m = parse_module("sig A { x: Int }\nrun {} for 3, 4 Int").expect("parse");
    assert_eq!(effective_bitwidth(&m, &m.commands[0].scope), 4);
    assert_eq!(effective_int_count(&m.commands[0].scope), 4);
    let cnf = run(&m, 0).expect("build");
    assert_eq!(cnf.bitwidth, 4);

    let m = parse_module("sig A { x: Int }\nrun {} for 3, 8 Int").expect("parse");
    assert_eq!(effective_bitwidth(&m, &m.commands[0].scope), 8);
    assert_eq!(effective_int_count(&m.commands[0].scope), 8);

    // quantified domains observe the same scope
    let m = parse_module("pred p { all x: Int | x = x }\nrun p for 3, 6 Int").expect("parse");
    assert_eq!(effective_bitwidth(&m, &m.commands[0].scope), 6);
}

#[test]
fn lazy_no_atoms_when_int_free() {
    // Int-free model: universe holds only the 3 user atoms.
    let m = parse_module("sig A {}\nrun {} for 3").expect("parse");
    let scope = m.commands[0].scope.clone();
    assert!(!module_needs_int_atoms(&m, &scope));
    let cnf = run(&m, 0).expect("build");
    assert_eq!(cnf.bitwidth, 4, "circuits still default to 4");
    assert_eq!(cnf.bounds.universe().size(), 3);
    assert_eq!(cnf.bounds.int_bounds().count(), 0);
}

#[test]
fn pure_int_arithmetic_needs_no_atoms() {
    // `#A` / literals / comparisons are pure BV circuits: no atoms.
    let m = parse_module("sig A {}\nrun { #A = 2 } for 3").expect("parse");
    let scope = m.commands[0].scope.clone();
    assert!(!module_needs_int_atoms(&m, &scope));
    let cnf = run(&m, 0).expect("build");
    assert_eq!(cnf.bounds.universe().size(), 3);
    let inst = solve(&cnf).expect("solve").expect("SAT");
    match query_value(&m, &scope, &cnf, "#A", &inst).expect("query #A") {
        QueryValue::Int(v) => assert_eq!(v, 2),
        QueryValue::Set(..) => panic!("expected Int"),
        QueryValue::Bool(..) => panic!("expected Int"),
        QueryValue::Bool(..) => panic!("expected Int"),
    }
}

#[test]
fn atoms_materialize_on_use() {
    // explicit scope always materializes W atoms
    let m = parse_module("sig A {}\nrun {} for 3, 4 Int").expect("parse");
    let cnf = run(&m, 0).expect("build");
    assert_eq!(cnf.bounds.universe().size(), 3 + 4);
    assert_eq!(cnf.bounds.int_bounds().count(), 4);

    // `sig in Int` materializes at the default count
    let m = parse_module("sig X in Int {}\nrun {} for 3").expect("parse");
    let cnf = run(&m, 0).expect("build");
    assert_eq!(cnf.bounds.int_bounds().count(), 4);

    // set-position literals materialize
    let m = parse_module("sig A {}\nrun { 5 in A } for 3").expect("parse");
    let scope = m.commands[0].scope.clone();
    assert!(module_needs_int_atoms(&m, &scope));
}

#[test]
fn int_field_solves_unsigned() {
    let src = "sig C { v: Int }\nrun { some C and some C.v } for 3, 8 Int";
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("build");
    assert_eq!(cnf.bitwidth, 8);
    assert_eq!(cnf.bounds.int_bounds().count(), 8);
    let inst = solve(&cnf).expect("solve").expect("SAT");
    let scope = &m.commands[0].scope;
    match query_value(&m, scope, &cnf, "#Int", &inst).expect("query #Int") {
        QueryValue::Int(v) => assert_eq!(v, 8),
        QueryValue::Set(..) => panic!("expected Int"),
        QueryValue::Bool(..) => panic!("expected Int"),
        QueryValue::Bool(..) => panic!("expected Int"),
    }
    // out-of-range literals wrap at the circuit width 8: 300 -> 44
    match query_value(&m, scope, &cnf, "300", &inst).expect("query 300") {
        QueryValue::Int(v) => assert_eq!(v, 44),
        QueryValue::Set(..) => panic!("expected Int"),
        QueryValue::Bool(..) => panic!("expected Int"),
        QueryValue::Bool(..) => panic!("expected Int"),
    }
}

#[test]
fn int_in_arrow_type() {
    // `Int` works on the right of `->` in field declarations.
    let src = "sig B {}\nsig A { f: B -> Int }\nrun { some f } for 3, 8 Int";
    let m = parse_module(src).expect("parse");
    let scope = m.commands[0].scope.clone();
    assert_eq!(effective_bitwidth(&m, &scope), 8);
    assert!(module_needs_int_atoms(&m, &scope));
    let cnf = run(&m, 0).expect("build");
    assert_eq!(cnf.bitwidth, 8);
    assert!(solve(&cnf).expect("solve").is_some());
}

#[test]
fn scope_clause_forms_unchanged() {
    // pre-existing `for N Int` spellings keep working
    for src in [
        "sig A {}\nrun {} for 8 Int",
        "sig A {}\nrun {} for Int 8",
        "sig A {}\nrun {} for exactly 8 Int",
    ] {
        let m = parse_module(src).expect("parse scope form");
        let scope = scope_of(src);
        assert_eq!(effective_bitwidth(&m, &scope), 8);
        assert_eq!(effective_int_count(&scope), 8);
        assert!(module_needs_int_atoms(&m, &scope));
    }
}
