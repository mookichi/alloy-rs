//! Compiler-style warnings for unconstrained relations: bounded but never
//! referenced by the command formula.

use alloy_front_rs::{parse_module, run};

#[test]
fn empty_body_warns_with_counts() {
    let m = parse_module("sig A {}\nrun {} for 3").expect("parse");
    let cnf = run(&m, 0).expect("build");
    assert_eq!(cnf.warnings.len(), 1, "warnings: {:?}", cnf.warnings);
    assert_eq!(
        cnf.warnings[0],
        "warning: 'A' is unconstrained: 3 free tuples -> 8 models"
    );
}

#[test]
fn mentioned_relation_does_not_warn() {
    let m = parse_module("sig A {}\nrun { some A } for 3").expect("parse");
    let cnf = run(&m, 0).expect("build");
    assert!(cnf.warnings.is_empty(), "warnings: {:?}", cnf.warnings);
}

#[test]
fn fixed_relation_does_not_warn() {
    // `exactly` pins A to its lower bound: no free tuples, no warning.
    let m = parse_module("sig A {}\nrun { A = A } for exactly 1").expect("parse");
    let cnf = run(&m, 0).expect("build");
    assert!(cnf.warnings.is_empty(), "warnings: {:?}", cnf.warnings);
}

#[test]
fn warning_counts_scale() {
    let m = parse_module("sig A {}\nrun {} for 5").expect("parse");
    let cnf = run(&m, 0).expect("build");
    assert_eq!(
        cnf.warnings,
        vec!["warning: 'A' is unconstrained: 5 free tuples -> 32 models"]
    );
}
