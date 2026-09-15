//! Scope-clause parsing: overall/exact entries plus `Int` bitwidth forms.
//!
//! Alloy spells the bitwidth `for 8 Int`; this frontend additionally
//! accepts `for Int 8` and both `exactly` orders (mirroring the existing
//! comma/`but` entry style, which is `Int`-first).

use alloy_front_rs::{parse_module, query_value, run, solve, QueryValue};

fn int_scope_of(src: &str) -> (Option<u32>, Option<u32>) {
    let m = parse_module(src).expect("parse");
    let scope = &m.commands[0].scope;
    (scope.int_scope, scope.overall)
}

#[test]
fn bitwidth_bare_forms() {
    assert_eq!(int_scope_of("sig A {}\nrun {} for 8 Int"), (Some(8), None));
    assert_eq!(int_scope_of("sig A {}\nrun {} for Int 8"), (Some(8), None));
    assert_eq!(
        int_scope_of("sig A {}\nrun {} for exactly 8 Int"),
        (Some(8), None)
    );
    assert_eq!(
        int_scope_of("sig A {}\nrun {} for exactly Int 8"),
        (Some(8), None)
    );
    // lowercase `int` works too (no sig can be named `int`)
    assert_eq!(int_scope_of("sig A {}\nrun {} for 8 int"), (Some(8), None));
}

#[test]
fn bitwidth_combines_with_entries() {
    let m = parse_module("sig A {}\nsig B {}\nrun {} for 2, 8 Int").expect("parse");
    let scope = &m.commands[0].scope;
    assert_eq!(scope.int_scope, Some(8));
    assert_eq!(scope.overall, Some(2));
    // pre-existing comma/`but` Int-first forms keep working
    let m = parse_module("sig A {}\nrun {} for 2, Int 8").expect("parse");
    assert_eq!(m.commands[0].scope.int_scope, Some(8));
}

#[test]
fn bitwidth_takes_effect() {
    // bitwidth 8 admits 100 and covers 256 int atoms.
    let src = "sig A {}\nrun { some A } for 1, 8 Int";
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("run");
    assert_eq!(cnf.bitwidth, 8);
    let inst = solve(&cnf).expect("solve").expect("SAT");
    let scope = &m.commands[0].scope;
    match query_value(&m, scope, &cnf, "#Int", &inst).expect("query #Int") {
        QueryValue::Int(v) => assert_eq!(v, 256),
        QueryValue::Set(..) => panic!("expected Int"),
    }
    match query_value(&m, scope, &cnf, "100", &inst).expect("query 100") {
        QueryValue::Int(v) => assert_eq!(v, 100),
        QueryValue::Set(..) => panic!("expected Int"),
    }
}
