//! A-plan Phase 1: parameterized `Int[w]` + lazy int-atom allocation.
//!
//! - `Int[8]` / `int[8]` parse to a sized `Int` type; bare `Int` keeps the
//!   command default (`for N Int`, else 4).
//! - The effective bitwidth is `max(default, every Int[w])`.
//! - Int atoms exist in the universe/bounds only when Int is used as a
//!   set (or an explicit `for N Int` scope requests them); Int-free
//!   models pay zero universe cost.

use alloy_front_rs::{
    effective_bitwidth, module_needs_int_atoms, parse_module, query_value, run, solve, QueryValue,
};

fn scope_of(src: &str) -> alloy_front_rs::Scope {
    let m = parse_module(src).expect("parse");
    m.commands[0].scope.clone()
}

#[test]
fn parse_sized_int() {
    let m = parse_module("sig A { x: Int[8] }\nrun {} for 3").expect("parse Int[8]");
    let scope = &m.commands[0].scope;
    assert_eq!(effective_bitwidth(&m, scope), 8);
    assert!(module_needs_int_atoms(&m, scope));

    let m = parse_module("sig A { x: int[5] }\nrun {} for 3").expect("parse int[5]");
    let scope = &m.commands[0].scope;
    assert_eq!(effective_bitwidth(&m, scope), 5);

    // bare Int still defaults to the command scope (else 4)
    let m = parse_module("sig A { x: Int }\nrun {} for 3").expect("parse bare Int");
    let scope = &m.commands[0].scope;
    assert_eq!(effective_bitwidth(&m, scope), 4);
    assert!(module_needs_int_atoms(&m, scope));

    // malformed widths are parse errors, not downstream join failures
    assert!(parse_module("sig A { x: Int[0] }\nrun {} for 3").is_err());
    assert!(parse_module("sig A { x: Int[33] }\nrun {} for 3").is_err());
    assert!(parse_module("sig A { x: Int[x] }\nrun {} for 3").is_err());
}

#[test]
fn effective_width_is_max_of_scope_and_decls() {
    // decl width wins over a narrower scope default
    let m = parse_module("sig A { x: Int[8] }\nrun {} for 3, 4 Int").expect("parse");
    assert_eq!(effective_bitwidth(&m, &m.commands[0].scope), 8);
    let cnf = run(&m, 0).expect("build");
    assert_eq!(cnf.bitwidth, 8);

    // scope wins over narrower decls
    let m = parse_module("sig A { x: Int[4] }\nrun {} for 3, 8 Int").expect("parse");
    assert_eq!(effective_bitwidth(&m, &m.commands[0].scope), 8);

    // quantified domains count too
    let m = parse_module("pred p { all x: Int[6] | x = x }\nrun p for 3").expect("parse");
    assert_eq!(effective_bitwidth(&m, &m.commands[0].scope), 6);
}

#[test]
fn lazy_no_atoms_when_int_free() {
    // Int-free model: universe holds only the 3 user atoms (was 3+16).
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
    }
}

#[test]
fn atoms_materialize_on_use() {
    // explicit scope always materializes
    let m = parse_module("sig A {}\nrun {} for 3, 4 Int").expect("parse");
    let cnf = run(&m, 0).expect("build");
    assert_eq!(cnf.bounds.universe().size(), 3 + 16);
    assert_eq!(cnf.bounds.int_bounds().count(), 16);

    // `sig in Int` materializes at the effective width
    let m = parse_module("sig X in Int {}\nrun {} for 3").expect("parse");
    let cnf = run(&m, 0).expect("build");
    assert_eq!(cnf.bounds.int_bounds().count(), 16);

    // set-position literals materialize
    let m = parse_module("sig A {}\nrun { 5 in A } for 3").expect("parse");
    let scope = m.commands[0].scope.clone();
    assert!(module_needs_int_atoms(&m, &scope));
}

#[test]
fn sized_int_field_solves() {
    let src = "sig C { v: Int[8] }\nrun { some C and some C.v } for 3";
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("build");
    assert_eq!(cnf.bitwidth, 8);
    assert_eq!(cnf.bounds.int_bounds().count(), 256);
    let inst = solve(&cnf).expect("solve").expect("SAT");
    let scope = &m.commands[0].scope;
    match query_value(&m, scope, &cnf, "#Int", &inst).expect("query #Int") {
        QueryValue::Int(v) => assert_eq!(v, 256),
        QueryValue::Set(..) => panic!("expected Int"),
    }
    // out-of-range literals wrap at the effective width 8: 300 -> 44
    match query_value(&m, scope, &cnf, "300", &inst).expect("query 300") {
        QueryValue::Int(v) => assert_eq!(v, 44),
        QueryValue::Set(..) => panic!("expected Int"),
    }
}

#[test]
fn sized_int_in_arrow_type() {
    // `Int[w]` also works on the right of `->` in field declarations.
    let src = "sig B {}\nsig A { f: B -> Int[8] }\nrun { some f } for 3";
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
    // pre-existing `for N Int` spellings keep working alongside `Int[w]`
    for src in [
        "sig A {}\nrun {} for 8 Int",
        "sig A {}\nrun {} for Int 8",
        "sig A {}\nrun {} for exactly 8 Int",
    ] {
        let m = parse_module(src).expect("parse scope form");
        let scope = scope_of(src);
        assert_eq!(effective_bitwidth(&m, &scope), 8);
        assert!(module_needs_int_atoms(&m, &scope));
    }
}
