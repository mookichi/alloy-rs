//! Tests for the REPL snippet API: fragments, bare expressions, eval, query.

use alloy_front_rs::{eval, fragment_keys, parse_expr, query, run, solve};

const DEMO: &str = r#"
    module demo
    sig A { f: lone B }
    sig B {}
    pred someA { some A }
    fun fa: set A { A }
    run someA for 3
"#;

#[test]
fn fragment_keys_single_named_decls() {
    assert_eq!(fragment_keys("sig X {}").unwrap(), vec!["sig:X"]);
    assert_eq!(
        fragment_keys("pred p { some A }").unwrap(),
        vec!["para:p"]
    );
    assert_eq!(
        fragment_keys("fun f: set A { A }").unwrap(),
        vec!["para:f"]
    );
    assert_eq!(
        fragment_keys("fact named { some A }").unwrap(),
        vec!["fact:named"]
    );
}

#[test]
fn fragment_keys_append_only() {
    assert!(fragment_keys("fact { some A }").unwrap().is_empty());
    assert!(fragment_keys("run someA for 3").unwrap().is_empty());
    assert!(fragment_keys("sig X {} sig Y {}").unwrap().is_empty());
    assert!(fragment_keys("open util/ordering[A] as ord").unwrap().is_empty());
}

#[test]
fn fragment_keys_rejects_garbage() {
    assert!(fragment_keys("sig {").is_err());
}

#[test]
fn parse_expr_accepts_let() {
    parse_expr("A").expect("bare name");
    parse_expr("let x = A | x + B").expect("let binding");
    parse_expr("A.f").expect("join");
    assert!(parse_expr("A +").is_err());
    assert!(parse_expr("").is_err());
    // formulas are not expressions
    assert!(parse_expr("some A").is_err());
    alloy_front_rs::parse_formula("some A").expect("formula entry");
}

#[test]
fn eval_checks_formula() {
    let sat = eval(DEMO, "some A").expect("eval");
    assert!(sat.satisfiable);
    assert!(sat.instance.is_some());
    let unsat = eval(DEMO, "no A and some A").expect("eval");
    assert!(!unsat.satisfiable);
}

#[test]
fn eval_lifts_bare_expression() {
    // `A` alone lifts to `some (A)`: satisfiable here.
    let sat = eval(DEMO, "A").expect("eval");
    assert!(sat.satisfiable);
    // garbage is a clean error
    assert!(eval(DEMO, "A +").is_err());
}

fn solved_demo() -> (alloy_front_rs::Module, alloy_front_rs::Cnf, alloy_front_rs::Instance) {
    let m = alloy_front_rs::parse_module(DEMO).expect("parse");
    let cnf = run(&m, 0).expect("run");
    let inst = solve(&cnf).expect("solve").expect("SAT");
    (m, cnf, inst)
}

#[test]
fn query_reads_against_instance() {
    let (m, cnf, inst) = solved_demo();
    let scope = &m.commands[0].scope;
    let (arity, ts) = query(&m, scope, &cnf, "A", &inst).expect("query A");
    assert_eq!(arity, 1);
    let r = inst.find_relation_by_name("A").unwrap();
    assert_eq!(ts.len(), inst.tuples(r).unwrap().len());
    assert!(ts.len() >= 1);
    // let-bound expression over the instance
    let (arity2, ts2) = query(&m, scope, &cnf, "let x = A | x", &inst).expect("query let");
    assert_eq!(arity2, 1);
    assert_eq!(ts2.len(), ts.len());
    // join through a field
    let (arity3, _) = query(&m, scope, &cnf, "A.f", &inst).expect("query join");
    assert_eq!(arity3, 1);
    // unknown name is a clean error, not a panic
    assert!(query(&m, scope, &cnf, "Nope", &inst).is_err());
}

#[test]
fn query_zero_arg_fun_matches_sig() {
    let (m, cnf, inst) = solved_demo();
    let scope = &m.commands[0].scope;
    let (_, ts_fun) = query(&m, scope, &cnf, "fa", &inst).expect("query fun");
    let (_, ts_sig) = query(&m, scope, &cnf, "A", &inst).expect("query sig");
    assert_eq!(ts_fun.len(), ts_sig.len());
}

#[test]
fn query_stable_across_runs() {
    // Relation-ID alignment must not depend on HashMap order: repeat the
    // whole build+solve+query cycle and require identical results.
    let mut lens = Vec::new();
    for _ in 0..3 {
        let (m, cnf, inst) = solved_demo();
        let scope = &m.commands[0].scope;
        let (_, ts) = query(&m, scope, &cnf, "A", &inst).expect("query A");
        lens.push(ts.len());
    }
    assert!(lens.iter().all(|&n| n >= 1), "all runs non-empty: {lens:?}");
    assert_eq!(lens[0], lens[1]);
    assert_eq!(lens[1], lens[2]);
}

#[test]
fn let_separator_parity_with_java() {
    // Java Alloy accepts `|` and rejects `in` in both positions.
    alloy_front_rs::parse_expr("let x = A | x").expect("expr bar");
    assert!(alloy_front_rs::parse_expr("let x = A in x").is_err());
    alloy_front_rs::parse_formula("let x = A | some x").expect("formula bar");
    assert!(alloy_front_rs::parse_formula("let x = A in some x").is_err());
    // End-to-end through eval.
    let sat = eval(DEMO, "let x = A | some x").expect("eval let");
    assert!(sat.satisfiable);
}
