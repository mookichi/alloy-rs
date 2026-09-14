//! Tests for the REPL split API: `run`/`check` -> `Cnf`, `solve` -> `Option<Instance>`,
//! `validate` -> instance as-is | none.

use alloy_front_rs::{check, parse_module, run, solve, validate};

#[test]
fn run_sat_yields_example() {
    let src = r#"
        module toy
        sig A {}
        pred someA { some A }
        run someA for 3
    "#;
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("run builds Cnf");
    assert!(cnf.is_run());
    assert!(cnf.num_vars > 0);
    assert!(!cnf.clauses.is_empty());
    let inst = solve(&cnf).expect("solve").expect("SAT => Some(instance)");
    // Example contains at least one A atom.
    let found = inst.find_relation_by_name("A").and_then(|r| inst.tuples(r));
    assert!(found.is_some(), "instance should contain A, got: {inst}");
    assert!(found.unwrap().len() >= 1);
}

#[test]
fn run_unsat_yields_none_empty() {
    let src = r#"
        module t
        sig A {}
        fact { no A }
        run {} for exactly 2
    "#;
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("run builds Cnf");
    assert_eq!(solve(&cnf).expect("solve").is_none(), true);
}

#[test]
fn check_holds_yields_none_empty() {
    // Assertion holds: no counterexample => None.
    let src = r#"
        module t
        sig A {}
        fact { no A }
        assert noA { no A }
        check noA for 3
    "#;
    let m = parse_module(src).expect("parse");
    let cnf = check(&m, 0).expect("check builds Cnf");
    assert!(cnf.is_check());
    assert!(solve(&cnf).expect("solve").is_none());
}

#[test]
fn check_violated_yields_counterexample() {
    // Assertion violated: SAT under negation => Some(counterexample).
    let src = r#"
        module t
        sig A {}
        assert someA { some A }
        check someA for 3
    "#;
    let m = parse_module(src).expect("parse");
    let cnf = check(&m, 0).expect("check builds Cnf");
    let inst = solve(&cnf)
        .expect("solve")
        .expect("violated assert => Some(counterexample)");
    let a = inst
        .find_relation_by_name("A")
        .and_then(|r| inst.tuples(r))
        .expect("counterexample has A");
    assert_eq!(a.len(), 0, "counterexample pins A empty, got: {inst}");
}

#[test]
fn kind_mismatch_rejected() {
    let src = r#"
        module t
        sig A {}
        pred p { some A }
        assert q { some A }
        run p for 2
        check q for 2
    "#;
    let m = parse_module(src).expect("parse");
    assert!(check(&m, 0).is_err(), "run cmd via check() must fail");
    assert!(run(&m, 1).is_err(), "check cmd via run() must fail");
}

#[test]
fn validate_accepts_solved_example_as_is() {
    let src = r#"
        module toy
        sig A {}
        pred someA { some A }
        run someA for 3
    "#;
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("run builds Cnf");
    let inst = solve(&cnf).expect("solve").expect("SAT");
    let back = validate(&cnf, &inst).expect("solved instance is a model");
    assert_eq!(format!("{inst}"), format!("{back}"), "validate returns instance as-is");
}

#[test]
fn validate_rejects_emptied_instance() {
    // Emptied A still respects (empty) bounds but falsifies `some A`.
    use alloy_kodkod_rs::tupleset::TupleSet;
    let src = r#"
        module toy
        sig A {}
        pred someA { some A }
        run someA for 3
    "#;
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("run builds Cnf");
    let inst = solve(&cnf).expect("solve").expect("SAT");
    let r = inst.find_relation_by_name("A").expect("A in instance");
    let empty = TupleSet::new(inst.universe(), 1).expect("empty set");
    let mut bad = inst.clone();
    bad.add(r, &empty).expect("replace A");
    assert!(validate(&cnf, &bad).is_none(), "emptied instance is no model");
}

#[test]
fn validate_rejects_out_of_upper_tuple() {
    // A tuple from outside A's upper bound violates bounds containment.
    let src = r#"
        module t
        sig A {}
        sig B {}
        run {} for 2
    "#;
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("run builds Cnf");
    let inst = solve(&cnf).expect("solve").expect("SAT");
    let r = inst.find_relation_by_name("A").expect("A in instance");
    let upper = cnf.bounds.upper_bound(r).expect("A has upper bound");
    let size = inst.universe().size() as i64;
    let foreign = (0..size)
        .find(|i| !upper.index_view().contains(*i))
        .expect("universe larger than A upper");
    let mut ts = inst.tuples(r).expect("A tuples").clone();
    ts.insert_index(foreign);
    let mut bad = inst.clone();
    bad.add(r, &ts).expect("replace A");
    assert!(validate(&cnf, &bad).is_none(), "out-of-upper instance is no model");
}

#[test]
fn validate_accepts_check_counterexample() {
    let src = r#"
        module t
        sig A {}
        assert someA { some A }
        check someA for 3
    "#;
    let m = parse_module(src).expect("parse");
    let cnf = check(&m, 0).expect("check builds Cnf");
    let ce = solve(&cnf).expect("solve").expect("counterexample");
    assert!(validate(&cnf, &ce).is_some(), "counterexample is a model of check Cnf");
}

#[test]
fn validate_rejects_foreign_universe_instance() {
    // An instance over a different universe is no model of this Cnf.
    let src_a = r#"
        module a
        sig A {}
        run {} for exactly 2
    "#;
    let src_b = r#"
        module b
        sig A {}
        run {} for exactly 1
    "#;
    let ma = parse_module(src_a).expect("parse a");
    let mb = parse_module(src_b).expect("parse b");
    let cnf_a = run(&ma, 0).expect("run a");
    let cnf_b = run(&mb, 0).expect("run b");
    let inst_b = solve(&cnf_b).expect("solve b").expect("SAT");
    assert!(validate(&cnf_a, &inst_b).is_none(), "foreign instance is no model");
}
