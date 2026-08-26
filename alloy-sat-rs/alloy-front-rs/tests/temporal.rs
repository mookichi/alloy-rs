//! Tests for temporal (LTL) frontend support.

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

// ---------------------------------------------------------------------------
// Unit tests: individual temporal operators
// ---------------------------------------------------------------------------

#[test]
fn temporal_always_basic() {
    let src = r#"
        module t
        sig A {}
        run { always (some A) } for 3 but A 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn temporal_always_unsat() {
    let src = r#"
        module t
        sig A {}
        run { always (some A and no A) } for 3 but A 2
    "#;
    assert_eq!(outcome(src, 0), "UNSAT");
}

#[test]
fn temporal_eventually_basic() {
    let src = r#"
        module t
        sig A {}
        run { eventually (some A) } for 3 but A 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn temporal_prime_basic() {
    let src = r#"
        module t
        var sig A {}
        run { always (A' = A) } for 3 but A 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn temporal_always_and_eventually() {
    let src = r#"
        module t
        sig A {}
        run { always eventually (some A) } for 3 but A 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn temporal_var_field() {
    let src = r#"
        module t
        sig A { var f: one A }
        run { always (f' = f) } for 3 but A 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn temporal_var_field_change() {
    let src = r#"
        module t
        sig A { var f: one A }
        run { eventually (f' != f) } for 3 but A 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn temporal_static_field_no_prime() {
    let src = r#"
        module t
        sig A { g: one A }
        run { always (g' = g) } for 3 but A 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn temporal_steps_keyword() {
    let src = r#"
        module t
        sig A {}
        run { always (some A) } for 3 steps but A 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn temporal_steps_with_scope() {
    let src = r#"
        module t
        var sig A {}
        run { eventually (some A) } for 5 steps but A 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

// ---------------------------------------------------------------------------
// Integration tests: meaningful temporal models
// ---------------------------------------------------------------------------

#[test]
fn integration_counter_stays_bounded() {
    // var field stays constant: val' = val always holds
    let src = r#"
        module t
        sig State { var val: Int }
        run { always (State.val' = State.val) } for 3 but State 1, Int 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn integration_process_reaches_goal() {
    // A process eventually reaches a non-empty state
    let src = r#"
        module t
        var sig Process { target: set Process }
        run { eventually (some Process.target) } for 4 steps but Process 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn integration_prime_chain_swap() {
    // a' = b and b' = a (swap every step)
    let src = r#"
        module t
        var sig A {}
        var sig B {}
        run { always (A' = B and B' = A) }
        for 4 steps but A 1, B 1
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn integration_always_not_unsat() {
    // always (some A and no A) is unsatisfiable
    let src = r#"
        module t
        sig A {}
        run { always (some A and no A) } for 3 but A 1
    "#;
    assert_eq!(outcome(src, 0), "UNSAT");
}

#[test]
fn integration_eventually_always() {
    // eventually always P: P becomes true and stays true
    let src = r#"
        module t
        var sig A {}
        run { eventually always (some A) } for 4 steps but A 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn integration_ring_invariant() {
    // A ring topology that never changes
    let src = r#"
        module t
        sig Node { var next: one Node }
        run { always (all n: Node | n.next' = n.next) }
        for 3 steps but Node 3
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn integration_alt_negation() {
    // always not (some A and no A) — same as always_not_unsat but via not
    let src = r#"
        module t
        sig A {}
        run { always not (some A and no A) } for 3 but A 1
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn integration_var_sig_multiple_fields() {
    // Multiple var fields on same sig
    let src = r#"
        module t
        sig A { var x: one A, var y: one A }
        run { always (x' = x and y' = y) } for 3 but A 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

// ---------------------------------------------------------------------------
// Phase 2: Pardinus-specific operators
// ---------------------------------------------------------------------------

#[test]
fn temporal_initially_basic() {
    // initially P: P holds at state 0
    let src = r#"
        module t
        sig A {}
        run { initially (some A) } for 3 but A 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn temporal_initially_unsat() {
    // initially (some A and no A) is unsatisfiable
    let src = r#"
        module t
        sig A {}
        run { initially (some A and no A) } for 3 but A 2
    "#;
    assert_eq!(outcome(src, 0), "UNSAT");
}

#[test]
fn temporal_goal_basic() {
    // goal P: P holds at the last state (N)
    let src = r#"
        module t
        sig A {}
        run { goal (some A) } for 3 but A 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn temporal_restore_basic() {
    // restore P: P holds at the loop state (L)
    let src = r#"
        module t
        sig A {}
        run { restore (some A) } for 3 but A 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn temporal_keeping_basic() {
    // keeping P: P holds at all states except last
    let src = r#"
        module t
        sig A {}
        run { keeping (some A) } for 3 but A 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn temporal_consistently_basic() {
    // consistently P: P holds at all states from loop onwards
    let src = r#"
        module t
        sig A {}
        run { consistently (some A) } for 3 but A 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn temporal_regularly_basic() {
    // regularly P: P holds at some state from loop onwards
    let src = r#"
        module t
        sig A {}
        run { regularly (some A) } for 3 but A 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

// ---------------------------------------------------------------------------
// Phase 1: Past-time LTL operators
// ---------------------------------------------------------------------------

#[test]
fn temporal_historically_basic() {
    // historically P: P held at all past states (including current)
    let src = r#"
        module t
        sig A {}
        run { historically (some A) } for 3 but A 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn temporal_once_basic() {
    // once P: P held at some past state (including current)
    let src = r#"
        module t
        sig A {}
        run { once (some A) } for 3 but A 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn temporal_before_basic() {
    // before P: P held at the previous state
    let src = r#"
        module t
        var sig A {}
        run { before (some A) } for 4 steps but A 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn temporal_since_basic() {
    // a since b: b held at some past state and a held continuously since
    let src = r#"
        module t
        var sig A {}
        run { some A since some A } for 3 but A 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn temporal_triggered_basic() {
    // a triggered b: whenever a held, b also held since then
    let src = r#"
        module t
        var sig A {}
        run { some A triggered some A } for 3 but A 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

// ---------------------------------------------------------------------------
// Integration tests: combined operators
// ---------------------------------------------------------------------------

#[test]
fn integration_initially_then_always() {
    // initially P and always P: P from start to end
    let src = r#"
        module t
        sig A {}
        run { initially (some A) and always (some A) } for 3 but A 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn integration_goal_and_consistently() {
    // goal P and consistently P: P in cycle and at end
    let src = r#"
        module t
        sig A {}
        run { goal (some A) and consistently (some A) } for 3 but A 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}
