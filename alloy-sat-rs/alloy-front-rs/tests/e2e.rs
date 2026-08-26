//! End-to-end tests: parse -> resolve/lower -> solve entirely in Rust.

use alloy_front_rs::{parse_module, run_command};

fn outcome(src: &str, cmd: usize) -> String {
    let m = match parse_module(src) {
        Ok(m) => m,
        Err(e) => return format!("parse-error: {e}"),
    };
    match run_command(&m, cmd) {
        Ok(sol) => {
            if sol.satisfiable {
                "SAT".into()
            } else {
                "UNSAT".into()
            }
        }
        Err(e) => format!("error: {e}"),
    }
}

#[test]
fn toy_sat() {
    let src = r#"
        module toy
        sig A {}
        pred someA { some A }
        run someA for 3
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn toy_flexible_bounds_vacuous_fact() {
    // Plain sigs are flexible up to scope, so `no Book` is satisfiable by
    // choosing zero books; the per-book field multiplicity goes vacuous.
    let src = r#"
        module t
        sig Book { names: some Name }
        sig Name {}
        fact { no Book }
        run {} for 3
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn toy_exactly_scope_conflicts_fact() {
    // `for exactly 3` pins the population; `no A` then contradicts it.
    let src = r#"
        module t
        sig A {}
        fact { no A }
        run {} for exactly 2
    "#;
    assert_eq!(outcome(src, 0), "UNSAT");
}

#[test]
fn toy_join_and_closure() {
    // a 3-cycle must exist in r for SAT
    let src = r#"
        module cyc
        sig N { r: set N }
        pred three_cycle { some iden & ^r }
        run three_cycle for 3
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn toy_int_cardinality_unsat() {
    let src = r#"
        module cnt
        sig A {}
        pred two { #A = 4 }
        run two for 3
    "#;
    // scope gives exactly 3 atoms; #A=4 impossible
    assert_eq!(outcome(src, 0), "UNSAT");
}

#[test]
fn toy_lone_field_allows_empty() {
    let src = r#"
        module lf
        sig B { f: lone X }
        sig X {}
        pred ok { no f }
        run ok for 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn toy_arrow_mult_some_forces_existence() {
    // `g: Group` field where each book has SOME g: then any book implies a group
    let src = r#"
        module am
        sig Book { g: some G }
        sig G {}
        pred book_exists { one Book }
        run book_exists for 3
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn toy_ternary_trailing_mult() {
    // addr: names -> some Target inside Book (addressBook pattern)
    let src = r#"
        module ternary
        sig Book { addr: N -> some T }
        sig N {}
        sig T {}
        pred has_pair { some Book and (some Book.addr) }
        run has_pair for 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn check_negates_and_cardinality_java_parity() {
    // Verified against the Java engine: SAT / UNSAT / UNSAT.
    let src = r#"
        module count
        sig A {}
        pred exactly2 { #A = 2 }
        run exactly2 for 3
        pred tooMany { #A = 4 }
        run tooMany for 3
        check card_range { #A <= 3 } for 3
    "#;
    assert_eq!(outcome(src, 0), "SAT");
    assert_eq!(outcome(src, 1), "UNSAT");
    // `check` negates its assertion: no counterexample within scope
    assert_eq!(outcome(src, 2), "UNSAT");
}

#[test]
fn parse_real_models_smoke() {
    let base = "../../org.alloytools.alloy.extra/extra/models";
    let files = [
        "book/appendixA/ring.als",
        "book/appendixA/spanning.als",
        "book/appendixA/closure.als",
        "examples/tutorial/farmer.als",
        "examples/toys/ceilingsAndFloors.als",
    ];
    let mut failures = Vec::new();
    for f in files {
        let path = format!("{base}/{f}");
        let text = match std::fs::read_to_string(&path) {
            Ok(t) => t,
            Err(e) => {
                failures.push(format!("{f}: read: {e}"));
                continue;
            }
        };
        if let Err(e) = parse_module(&text) {
            failures.push(format!("{f}: {e}"));
        }
    }
    assert!(
        failures.is_empty(),
        "parse failures:\n{}",
        failures.join("\n")
    );
}

#[test]
fn sig_in_subset_sat() {
    // sig Student in Person: Student atoms are a subset of Person atoms
    let src = r#"
        module t
        sig Person {}
        sig Student in Person {}
        pred some_student { some Student }
        run some_student for 3
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn sig_in_basic() {
    // simplest test: sig in with no fields
    let src = r#"
        module t
        sig A {}
        sig B in A {}
        run { some B } for 2
    "#;
    let m = parse_module(src).unwrap();
    for sd in &m.sigs {
        eprintln!(
            "sig {:?}: extends={:?}, rel={:?}",
            sd.names, sd.extends, sd.rel
        );
    }
    let r = run_command(&m, 0);
    eprintln!(
        "result: {:?}",
        r.as_ref().map(|s| (s.satisfiable, s.instance.is_some()))
    );
    if let Err(ref e) = r {
        eprintln!("error: {e}");
    }
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn sig_extends_basic() {
    // extends should work (existing feature)
    let src = r#"
        module t
        sig A {}
        sig B extends A {}
        run { some B } for 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn sig_in_subset_unsat() {
    // Student must be subset of Person; asking for Student but no Person is UNSAT
    let src = r#"
        module t
        sig Person {}
        sig Student in Person {}
        pred impossible { some Student and no Person }
        run impossible for 3
    "#;
    assert_eq!(outcome(src, 0), "UNSAT");
}

#[test]
fn sig_in_with_fields() {
    // sig in can have its own fields
    let src = r#"
        module t
        sig Person { age: Int }
        sig Student in Person { gpa: Int }
        pred ok { some Student }
        run ok for 3
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn sig_in_chain() {
    // chain: A in B in C
    let src = r#"
        module t
        sig Top {}
        sig Mid in Top {}
        sig Bot in Mid {}
        pred nonempty { some Bot }
        run nonempty for 3
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn int_field_declaration() {
    // sig with Int field type
    let src = r#"
        module t
        sig Person { age: Int }
        pred has_age { some Person.age }
        run has_age for 3
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}
