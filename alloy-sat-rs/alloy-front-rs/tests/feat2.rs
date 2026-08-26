//! Task-2 features: `disj` quantifiers and function calls in expressions.

use alloy_front_rs::{parse_module, run_command};

fn outcome(src: &str, cmd: usize) -> String {
    let m = parse_module(src).unwrap();
    match run_command(&m, cmd) {
        Ok(s) => if s.satisfiable { "SAT" } else { "UNSAT" }.into(),
        Err(e) => format!("error: {e}"),
    }
}

#[test]
fn fun_call_in_expression() {
    let src = r#"
        module t
        sig Node { next: lone Node }
        one sig Root { edge: set Node }
        fun reach: set Node { Root.edge.*next }
        pred nonempty { #reach = 2 }
        run nonempty for exactly 3 Node
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}
#[test]
fn fun_call_with_args() {
    let src = r#"
        module t
        sig A {}
        fun pick[a: A]: set A { a + A }
        pred check_size { #pick[A] = 1 }
        run check_size for 1
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn disj_some_quantifier() {
    // two DISTINCT nodes required
    let src = r#"
        module t
        sig S {}
        pred two_distinct { some disj x, y: S | no y }
        pred needs_three { all disj x, y: S | x in y }
        pred impossible3 { some disj a, b, c: S | a = b }
        run two_distinct for exactly 2
        run needs_three for exactly 2
        run impossible3 for exactly 2
    "#;
    assert_eq!(outcome(src, 0), "UNSAT");
    assert_eq!(outcome(src, 1), "UNSAT");
    assert_eq!(outcome(src, 2), "UNSAT");
}

#[test]
fn disj_all_quantifier() {
    // all disj x,y | f(x)=f(y) fails when a third element exists? Here:
    // all distinct pairs equal => at most... with 3 atoms, pairs must be
    // "equal" via trivially-true body, so SAT regardless.
    let src = r#"
        module t
        sig S {}
        pred p { all disj x, y: S | some S }
        run p for exactly 3
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn disj_comprehension() {
    let src = r#"
        module t
        sig S {}
        pred p { #{ x, y: S | x = y } >= 0 }
        run p for exactly 2
        pred q { #{ disj x, y: S | x = x } = 2 }
        run q for exactly 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
    assert_eq!(outcome(src, 1), "SAT");
}
