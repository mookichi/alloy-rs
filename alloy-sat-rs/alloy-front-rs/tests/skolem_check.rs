use alloy_front_rs::{parse_module, run_command};

fn outcome(src: &str, cmd: usize) -> String {
    let m = parse_module(src).unwrap();
    match run_command(&m, cmd) {
        Ok(s) => if s.satisfiable { "SAT" } else { "UNSAT" }.into(),
        Err(e) => format!("error: {e}"),
    }
}

/// Regression: skolemize must enforce `one` multiplicity on witnesses.
/// `some disj x,y: S | no y` should be UNSAT (y is forced to be a singleton, so no y is false).
#[test]
fn skolem_one_multiplicity() {
    let src = r#"
        module t
        sig S {}
        pred p { some disj x, y: S | no y }
        run p for exactly 2
    "#;
    assert_eq!(outcome(src, 0), "UNSAT");
}

/// `some x: S | no x` with implicit one multiplicity should be UNSAT.
#[test]
fn skolem_one_multiplicity_simple() {
    let src = r#"
        module t
        sig S {}
        pred p { some x: S | no x }
        run p for exactly 1
    "#;
    assert_eq!(outcome(src, 0), "UNSAT");
}

/// `some disj x,y: S | no y` with 3 atoms: still UNSAT because y is forced to be nonempty.
#[test]
fn skolem_one_multiplicity_three_atoms() {
    let src = r#"
        module t
        sig S {}
        pred p { some disj x, y: S | no y }
        run p for exactly 3
    "#;
    assert_eq!(outcome(src, 0), "UNSAT");
}

/// `some x: S | x = x` should still be SAT.
#[test]
fn skolem_one_multiplicity_sat() {
    let src = r#"
        module t
        sig S {}
        pred p { some x: S | x = x }
        run p for exactly 1
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

/// `some disj x,y: S | x != y` should be SAT with 2+ atoms.
#[test]
fn skolem_disj_sat() {
    let src = r#"
        module t
        sig S {}
        pred p { some disj x, y: S | x != y }
        run p for exactly 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

/// `some disj x,y: S | x != y` should be UNSAT with exactly 1 atom.
#[test]
fn skolem_disj_unsat_single() {
    let src = r#"
        module t
        sig S {}
        pred p { some disj x, y: S | x != y }
        run p for exactly 1
    "#;
    assert_eq!(outcome(src, 0), "UNSAT");
}
