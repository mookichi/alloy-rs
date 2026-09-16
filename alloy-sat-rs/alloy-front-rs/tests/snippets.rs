//! Tests for the REPL snippet API: fragments, bare expressions, eval, query.

use alloy_front_rs::{
    eval, fragment_keys, parse_expr, parse_int_expr, query, query_value, run, solve, QueryValue,
};

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

/// DEMO variant with Int atoms materialized (explicit `4 Int` scope):
/// A-plan allocates int atoms lazily, so set-position Int queries
/// (`Int`, `{x: Int}`, `{1+1}`, `5 + A`) need this model.
const DEMO_INT: &str = r#"
    module demo
    sig A { f: lone B }
    sig B {}
    pred someA { some A }
    fun fa: set A { A }
    run someA for 3, 4 Int
"#;

fn solved_demo_int() -> (
    alloy_front_rs::Module,
    alloy_front_rs::Cnf,
    alloy_front_rs::Instance,
) {
    let m = alloy_front_rs::parse_module(DEMO_INT).expect("parse");
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
fn query_int_cardinality() {
    let (m, cnf, inst) = solved_demo();
    let scope = &m.commands[0].scope;
    let r = inst.find_relation_by_name("A").unwrap();
    let n = inst.tuples(r).unwrap().len() as i64;
    assert!(parse_int_expr("#A").is_ok());
    match query_value(&m, scope, &cnf, "#A", &inst).expect("query #A") {
        QueryValue::Int(v) => assert_eq!(v, n),
        QueryValue::Set(..) => panic!("expected Int"),
        QueryValue::Bool(..) => panic!("expected Int"),
    }
    // integer arithmetic over a query
    match query_value(&m, scope, &cnf, "#A + 1", &inst).expect("query #A + 1") {
        QueryValue::Int(v) => assert_eq!(v, n + 1),
        QueryValue::Set(..) => panic!("expected Int"),
        QueryValue::Bool(..) => panic!("expected Int"),
    }
    // relational input still yields a set through query_value
    match query_value(&m, scope, &cnf, "A", &inst).expect("query A") {
        QueryValue::Set(arity, ts) => {
            assert_eq!(arity, 1);
            assert_eq!(ts.len() as i64, n);
        }
        QueryValue::Int(..) => panic!("expected Set"),
        QueryValue::Bool(..) => panic!("expected Set"),
    }
    // garbage reports the relational parse error, not the int one
    assert!(query_value(&m, scope, &cnf, "A +", &inst).is_err());
    // the set-only entry point stays set-only
    assert!(query(&m, scope, &cnf, "#A", &inst).is_err());
}

#[test]
fn query_int_universe() {
    // `Int` (and `int`) denote every in-scope integer: default W = 4
    // covers {0, 1, 2, 3} (explicit scope materializes the atoms).
    let (m, cnf, inst) = solved_demo_int();
    let scope = &m.commands[0].scope;
    for src in ["Int", "int"] {
        match query_value(&m, scope, &cnf, src, &inst).expect("query Int") {
            QueryValue::Set(arity, ts) => {
                assert_eq!(arity, 1);
                assert_eq!(ts.len(), 4, "W = 4 covers 0..3");
            }
            QueryValue::Int(..) => panic!("expected Set"),
        QueryValue::Bool(..) => panic!("expected Set"),
        }
    }
    // the set-only entry point accepts it too
    let (_, ts) = query(&m, scope, &cnf, "Int", &inst).expect("query Int");
    assert_eq!(ts.len(), 4);
}

#[test]
fn query_int_universe_lazy_when_unused() {
    // A-plan lazy allocation: an Int-free model materializes no int
    // atoms, so `Int` denotes the empty set there (use `for N Int` or
    // mention Int to get the range).
    let (m, cnf, inst) = solved_demo();
    let scope = &m.commands[0].scope;
    match query_value(&m, scope, &cnf, "Int", &inst).expect("query Int") {
        QueryValue::Set(arity, ts) => {
            assert_eq!(arity, 1);
            assert_eq!(ts.len(), 0, "Int-free model has no int atoms");
        }
        QueryValue::Int(..) => panic!("expected Set"),
        QueryValue::Bool(..) => panic!("expected Set"),
    }
    // `#Int` is likewise 0 without materialized atoms.
    match query_value(&m, scope, &cnf, "#Int", &inst).expect("query #Int") {
        QueryValue::Int(v) => assert_eq!(v, 0),
        QueryValue::Set(..) => panic!("expected Int"),
        QueryValue::Bool(..) => panic!("expected Int"),
    }
}

#[test]
fn query_int_literal_wraps_like_java() {
    let (m, cnf, inst) = solved_demo();
    let scope = &m.commands[0].scope;
    // in-range literals (unary minus folds at parse time)
    match query_value(&m, scope, &cnf, "-8", &inst).expect("query -8") {
        QueryValue::Int(v) => assert_eq!(v, -8),
        QueryValue::Set(..) => panic!("expected Int"),
        QueryValue::Bool(..) => panic!("expected Int"),
    }
    match query_value(&m, scope, &cnf, "7", &inst).expect("query 7") {
        QueryValue::Int(v) => assert_eq!(v, 7),
        QueryValue::Set(..) => panic!("expected Int"),
        QueryValue::Bool(..) => panic!("expected Int"),
    }
    // out-of-range literals wrap (two's complement truncation at the
    // query Cnf's bitwidth 4), matching Java's evaluator: 100 -> 4,
    // -9 -> 7.
    match query_value(&m, scope, &cnf, "100", &inst).expect("query 100") {
        QueryValue::Int(v) => assert_eq!(v, 4),
        QueryValue::Set(..) => panic!("expected Int"),
        QueryValue::Bool(..) => panic!("expected Int"),
    }
    match query_value(&m, scope, &cnf, "-9", &inst).expect("query -9") {
        QueryValue::Int(v) => assert_eq!(v, 7),
        QueryValue::Set(..) => panic!("expected Int"),
        QueryValue::Bool(..) => panic!("expected Int"),
    }
    let r = inst.find_relation_by_name("A").unwrap();
    let n = inst.tuples(r).unwrap().len() as i64;
    match query_value(&m, scope, &cnf, "#A + 100", &inst).expect("query #A + 100") {
        QueryValue::Int(v) => assert_eq!(v, n + 4),
        QueryValue::Set(..) => panic!("expected Int"),
        QueryValue::Bool(..) => panic!("expected Int"),
    }
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

/// Reported REPL session: with X pinned to three int atoms, a filtered
/// comprehension query returns the qualifying subset.
#[test]
fn query_comprehension_int_filter() {
    let src = r#"
        module demo
        sig X in Int {}
        fact pin { X = 0 + 1 + 2 }
        run {} for 3, 8 Int
    "#;
    let m = alloy_front_rs::parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("build cnf");
    let inst = solve(&cnf).expect("solve").expect("SAT instance");
    let scope = &m.commands[0].scope;
    match query_value(&m, scope, &cnf, "{x: X | x < 2}", &inst).expect("query") {
        QueryValue::Set(arity, ts) => {
            assert_eq!(arity, 1);
            assert_eq!(ts.len(), 2);
        }
        QueryValue::Int(..) => panic!("expected Set"),
        QueryValue::Bool(..) => panic!("expected Set"),
    }
    // unfiltered, the whole pinned set comes back
    let (_, all) = query(&m, scope, &cnf, "X", &inst).expect("query X");
    assert_eq!(all.len(), 3);
}

/// Reported case: `:query {x: X}` enumerates the whole domain.
#[test]
fn query_bare_comprehension() {
    let src = r#"
        module demo
        sig X in Int {}
        fact pin { X = 0 + 1 + 2 }
        run {} for 3, 8 Int
    "#;
    let m = alloy_front_rs::parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("build cnf");
    let inst = solve(&cnf).expect("solve").expect("SAT instance");
    let scope = &m.commands[0].scope;
    let (_, ts) = query(&m, scope, &cnf, "{x: X}", &inst).expect("query {x: X}");
    assert_eq!(ts.len(), 3);
}

/// `{A, B, ...}` set literal (extension: Java rejects it) equals `A + B`.
#[test]
fn query_set_literal() {
    let (m, cnf, inst) = solved_demo();
    let scope = &m.commands[0].scope;
    let (_, plus) = query(&m, scope, &cnf, "A + B", &inst).expect("query A + B");
    let (_, lit) = query(&m, scope, &cnf, "{A, B}", &inst).expect("query {A, B}");
    assert_eq!(lit.len(), plus.len());
    // single-element and nested forms
    let (_, one) = query(&m, scope, &cnf, "{A}", &inst).expect("query {A}");
    let (_, a) = query(&m, scope, &cnf, "A", &inst).expect("query A");
    assert_eq!(one.len(), a.len());
    // multi-decl comprehension still wins over literal reading
    let (_, all) = query(&m, scope, &cnf, "{x: A}", &inst).expect("query {x: A}");
    assert_eq!(all.len(), a.len());
}

/// Purely integer-shaped input queries as an integer: `1+1` is `2`
/// (arithmetic), not the `{1}` union.
#[test]
fn query_arith_over_literals() {
    let (m, cnf, inst) = solved_demo();
    let scope = &m.commands[0].scope;
    match query_value(&m, scope, &cnf, "1+1", &inst).expect("query 1+1") {
        QueryValue::Int(v) => assert_eq!(v, 2),
        QueryValue::Set(..) => panic!("expected Int"),
        QueryValue::Bool(..) => panic!("expected Int"),
    }
    // mixed set/int stays relational: `3 + A` is the union set
    // (needs materialized atoms, so it is covered on the Int model).
    let (mi, cnfi, insti) = solved_demo_int();
    let scopei = &mi.commands[0].scope;
    match query_value(&mi, scopei, &cnfi, "3 + A", &insti).expect("query 3 + A") {
        QueryValue::Set(..) => {}
        QueryValue::Int(..) => panic!("expected Set"),
        QueryValue::Bool(..) => panic!("expected Set"),
    }
    // on the Int-free model the set-position literal is out of scope
    assert!(query_value(&m, scope, &cnf, "5 + A", &inst).is_err());
}

/// `{1+1}` folds pure literal arithmetic: `{2}`, not the `{1}` union.
/// (Set-position literals need materialized Int atoms.)
#[test]
fn query_set_literal_folds_arith() {
    let (m, cnf, inst) = solved_demo_int();
    let scope = &m.commands[0].scope;
    let (_, two) = query(&m, scope, &cnf, "{1+1}", &inst).expect("query {1+1}");
    assert_eq!(two.len(), 1);
    let (_, sum) = query(&m, scope, &cnf, "{1+1, 3}", &inst).expect("query {1+1, 3}");
    assert_eq!(sum.len(), 2);
}

/// `{x : 1+2}` binds the folded domain `{3}`, not `{1, 2}`.
/// (Set-position literals need materialized Int atoms.)
#[test]
fn query_domain_fold() {
    let (m, cnf, inst) = solved_demo_int();
    let scope = &m.commands[0].scope;
    let (_, ts) = query(&m, scope, &cnf, "{x : 1+2}", &inst).expect("query {x : 1+2}");
    assert_eq!(ts.len(), 1);
}

/// `:query (sum X)` evaluates the set form.
#[test]
fn query_sum_of_set() {
    let src = r#"
        module demo
        sig X in Int {}
        fact pin { X = 1 + 2 + 3 }
        run {} for 3
    "#;
    let m = alloy_front_rs::parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("build cnf");
    let inst = solve(&cnf).expect("solve").expect("SAT instance");
    let scope = &m.commands[0].scope;
    match query_value(&m, scope, &cnf, "sum X", &inst).expect("query sum X") {
        QueryValue::Int(v) => assert_eq!(v, 6),
        QueryValue::Set(..) => panic!("expected Int"),
        QueryValue::Bool(..) => panic!("expected Int"),
    }
}

/// `$` names are rejected in declarations (Java parity: atoms are solver
/// outputs, not language terms), at every binding site.
#[test]
fn dollar_names_rejected_in_decls() {
    for src in [
        "sig A$0 {}",
        "sig A { f$0: lone B }\nsig B {}",
        "sig A {}\nsig B {}\npred p[x$0: A] { some x$0 }",
        "sig A {}\nfact f$1 { some A }",
        "sig A {}\nassert a$2 { some A }",
        "sig A {}\nrun { all x$3: A | some x$3 } for 3",
        "sig A {}\nrun { let y$4 = A | some y$4 } for 3",
    ] {
        let err = match alloy_front_rs::parse_module(src) {
            Ok(_) => panic!("`$` accepted: {src}"),
            Err(e) => e,
        };
        assert!(
            err.to_string().contains('$'),
            "error should mention `$`: {err}"
        );
    }
}

/// `$` references are rejected in model formulas, even when the atom
/// exists in the universe.
#[test]
fn dollar_refs_rejected_in_models() {
    // parse succeeds (references are not bindings)...
    let src = "sig A {}\nrun { some A$0 } for 3";
    let m = alloy_front_rs::parse_module(src).expect("parse");
    // ...but lowering the model fails with Java's `$` error.
    let err = run(&m, 0).expect_err("model atom ref built");
    assert!(
        err.to_string().contains('$'),
        "error should mention `$`: {err}"
    );
    // Same through the `:eval` path (`run { ... }` wrapper).
    let err = eval("sig A {}\nrun {} for 3", "some A$0").expect_err("eval atom ref built");
    assert!(
        err.to_string().contains('$'),
        "error should mention `$`: {err}"
    );
}

/// `:query` keeps atom references: solve-after evaluation may name
/// universe atoms (Java's `frame.a2k` equivalent).
#[test]
fn query_atom_literal_allowed() {
    let (m, cnf, inst) = solved_demo_int();
    let scope = &m.commands[0].scope;
    match query_value(&m, scope, &cnf, "A$0", &inst).expect("query A$0") {
        QueryValue::Set(arity, ts) => {
            assert_eq!(arity, 1);
            assert_eq!(ts.len(), 1, "one atom singleton");
        }
        QueryValue::Int(..) => panic!("expected Set"),
        QueryValue::Bool(..) => panic!("expected Set"),
    }
    // atoms compose in larger set expressions too
    let (_, ts) = query(&m, scope, &cnf, "{A$0}", &inst).expect("query {A$0}");
    assert_eq!(ts.len(), 1);
}

/// Reported case: `:query` evaluates closed formulas (`=`, `>`, ...) to
/// booleans against the solved instance.
#[test]
fn query_closed_formulas() {
    let (m, cnf, inst) = solved_demo_int();
    let scope = &m.commands[0].scope;
    for (src, want) in [
        ("1 = 1", true),
        ("1 = 2", false),
        ("1 > 0", true),
        ("1 > 2", false),
        ("A = A", true),
        ("some A", true),
        ("no A", false),
        ("#A = #A", true),
        ("7 = {0, 1, 2}", true),
        ("7 = {0, 1, 3}", false),
        ("{MSB} = {3}", true),
    ] {
        match query_value(&m, scope, &cnf, src, &inst)
            .unwrap_or_else(|e| panic!("query {src}: {e}"))
        {
            QueryValue::Bool(v) => assert_eq!(v, want, "{src}"),
            QueryValue::Set(..) => panic!("expected Bool for {src}"),
            QueryValue::Int(..) => panic!("expected Bool for {src}"),
        }
    }
    // garbage still reports the expression-parse error, not a formula one
    assert!(query_value(&m, scope, &cnf, "A +", &inst).is_err());
}

/// Reported case: `:query {x: Int}` enumerates every in-scope integer.
/// (Needs materialized Int atoms: explicit scope here.)
#[test]
fn query_brace_set_routing() {
    // Bare `{...}` keeps the set reading in `:query` (mirrors the
    // `=`/`!=` rewind rule); `*`/`/` trees read as integers.
    let (m, cnf, inst) = solved_demo_int();
    let scope = &m.commands[0].scope;
    let (_, ts) = query(&m, scope, &cnf, "{A, B}", &inst).expect("query {A, B}");
    let (_, plus) = query(&m, scope, &cnf, "A + B", &inst).expect("query A + B");
    assert_eq!(ts.len(), plus.len());
    match query_value(&m, scope, &cnf, "{0, 1} * 2", &inst).expect("query {0,1} * 2") {
        QueryValue::Int(v) => assert_eq!(v, 6),
        QueryValue::Set(..) => panic!("expected Int"),
        QueryValue::Bool(..) => panic!("expected Int"),
    }
}
#[test]
fn query_comprehension_over_int() {
    let (m, cnf, inst) = solved_demo_int();
    let scope = &m.commands[0].scope;
    let (_, ts) = query(&m, scope, &cnf, "{x: Int}", &inst).expect("query {x: Int}");
    assert_eq!(ts.len(), 4, "W = 4 covers 0..3");
    // `Int` inside larger set expressions routes through the evaluator too
    let (_, union) = query(&m, scope, &cnf, "none + Int", &inst).expect("query none + Int");
    assert_eq!(union.len(), 4);
}
