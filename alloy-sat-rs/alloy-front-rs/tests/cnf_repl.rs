//! Tests for the REPL split API: `run`/`check` -> `Cnf`, `solve` -> `Option<Instance>`,
//! `validate` -> instance as-is | none.

use alloy_front_rs::{
    check, parse_module, run, solve, solve_temporal, validate, validate_temporal,
};

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

#[test]
fn temporal_run_builds_cnf_and_solves_trace() {
    // The REPL repro: initially/always + `for 5 steps` used to fail with
    // "temporal commands are not supported by run/check Cnf yet".
    let src = r#"
        module t
        var sig A {}
        fact { initially (some A) }
        fact { always (A' != A or no A) }
        run for 5 steps
    "#;
    let m = parse_module(src).expect("parse");
    assert!(m.is_temporal_command(0));
    let cnf = run(&m, 0).expect("temporal run builds Cnf");
    assert!(cnf.is_temporal);
    assert_eq!(cnf.steps, 5);
    let ti = solve_temporal(&cnf)
        .expect("solve_temporal")
        .expect("SAT => Some(trace)");
    assert_eq!(ti.len(), 5);
    assert!(validate_temporal(&cnf, &ti).is_some());
    // Compat path returns the first state.
    let first = solve(&cnf).expect("solve").expect("SAT");
    assert_eq!(
        format!("{first}"),
        format!("{}", ti.states()[0]),
        "solve returns states[0]"
    );
    // Single-state validation is meaningless for temporal Cnfs.
    assert!(validate(&cnf, &first).is_none());
}

#[test]
fn temporal_run_unsat_yields_none() {
    let src = r#"
        module t
        sig A {}
        run { always (some A and no A) } for 3 but A 1
    "#;
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("temporal run builds Cnf");
    assert!(solve_temporal(&cnf).expect("solve").is_none());
}

#[test]
fn temporal_check_violated_yields_counterexample_trace() {
    // `check` searches the negated assertion: a trace with some
    // empty-`A` state violates `always (some A)`.
    let src = r#"
        module t
        var sig A {}
        assert someA { always (some A) }
        check someA for 3 steps but A 1
    "#;
    let m = parse_module(src).expect("parse");
    assert!(m.is_temporal_command(0));
    let cnf = check(&m, 0).expect("temporal check builds Cnf");
    assert!(cnf.is_temporal);
    assert!(cnf.is_check());
    assert!(!cnf.skolemize);
    let ti = solve_temporal(&cnf)
        .expect("solve_temporal")
        .expect("violated assert => Some(counterexample trace)");
    assert_eq!(ti.len(), 3);
    assert!(validate_temporal(&cnf, &ti).is_some());
}

#[test]
fn temporal_check_holds_yields_none() {
    let src = r#"
        module t
        var sig A {}
        fact { always (some A) }
        assert someA { always (some A) }
        check someA for 3 steps but A 1
    "#;
    let m = parse_module(src).expect("parse");
    let cnf = check(&m, 0).expect("temporal check builds Cnf");
    assert!(solve_temporal(&cnf).expect("solve").is_none());
}

#[test]
fn solve_temporal_rejects_static_cnf() {
    let src = r#"
        module toy
        sig A {}
        run {} for 2
    "#;
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("run builds Cnf");
    assert!(!cnf.is_temporal);
    assert!(solve_temporal(&cnf).is_err());
}

/// Bitmask value of unary set `A` in a state: Σ 2^v over int atoms
/// named `v`, with the top atom carrying `-2^(W-1)`.
fn mask_of(state: &alloy_front_rs::Instance) -> i64 {
    let mut vals: Vec<i64> = Vec::new();
    let mut present: Vec<i64> = Vec::new();
    for i in 0..state.universe().size() {
        if let Ok(name) = state.universe().atom(i) {
            if let Ok(v) = name.parse::<i64>() {
                vals.push(v);
            }
        }
    }
    let top = vals.iter().copied().max().unwrap_or(-1);
    let r = state.find_relation_by_name("A").expect("A");
    let ts = state.tuples(r).expect("A tuples");
    for idx in ts.index_view().iter() {
        let name = state.universe().atom(idx as usize).expect("atom");
        let v: i64 = name.parse().expect("int atom");
        present.push(if v == top {
            -(1i64 << top)
        } else {
            1i64 << v
        });
    }
    present.iter().sum()
}

#[test]
fn temporal_int_minus_is_bitmask_arithmetic() {
    // `A' = 0 - A` reads `A` as its bitmask value: -1, 1, -1, 1, -1
    // (set-difference reading would give -1, 0, 1, 0, 1).
    let src = r#"
        module t
        var sig A in Signed
        fact {A = -1}
        run for 5 steps, 3 int
        fact {always {A' = 0 - A}}
    "#;
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("temporal run builds Cnf");
    assert!(cnf.is_temporal);
    let ti = solve_temporal(&cnf)
        .expect("solve_temporal")
        .expect("SAT");
    let got: Vec<i64> = ti.states().iter().map(mask_of).collect();
    assert_eq!(got, vec![-1, 1, -1, 1, -1], "trace values");
    assert!(validate_temporal(&cnf, &ti).is_some());
}
