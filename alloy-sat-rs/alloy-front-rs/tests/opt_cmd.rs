//! Optimization command tests (Iter 13 grammar): parse + lower +
//! optimize for `maximize`/`minimize` in Int and weights forms.
//! Plus AlloyMax surface (`maxsome` / `minsome` / `soft fact`).

use alloy_front_rs::{
    command_needs_opt, parse_module, run_command, run_opt_command, CommandKind, OptSpec,
};

fn kinds(src: &str) -> Vec<CommandKind> {
    parse_module(src)
        .expect("parse")
        .commands
        .iter()
        .map(|c| c.kind.clone())
        .collect()
}

#[test]
fn parse_maximize_int_forms() {
    let src = "sig A {}\nmaximize : #A for 3";
    let k = kinds(src);
    assert_eq!(k.len(), 1);
    assert!(matches!(k[0], CommandKind::Maximize { ref objective, .. }
        if matches!(objective, OptSpec::Int(_))));

    let src = "sig A {}\nminimize { some A } : #A for 3";
    let k = kinds(src);
    assert!(matches!(k[0], CommandKind::Minimize { ref objective, .. }
        if matches!(objective, OptSpec::Int(_))));

    let src = "sig A {}\npred p { some A }\nmaximize p : #A for 3";
    let k = kinds(src);
    assert!(matches!(k[0], CommandKind::Maximize { ref objective, .. }
        if matches!(objective, OptSpec::Int(_))));
}

#[test]
fn parse_weights_forms() {
    let src = "sig A {}\nmaximize weights { A: 2 } for 3";
    let k = kinds(src);
    assert!(matches!(k[0], CommandKind::Maximize { ref objective, .. }
        if matches!(objective, OptSpec::Weights(w) if w == &vec![("A".to_string(), 2)])));

    let src = "sig A {}\nminimize weights { A: 1, B: -2 } { some A } for 3";
    let m = parse_module(src).expect("parse");
    assert!(matches!(m.commands[0].kind,
        CommandKind::Minimize { ref objective, .. }
        if matches!(objective, OptSpec::Weights(w) if w.len() == 2)));

    // weights-first with body after.
    let src = "sig A {}\nmaximize weights { A: 1 } { some A } for 3";
    let k = kinds(src);
    assert!(matches!(k[0], CommandKind::Maximize { ref objective, .. }
        if matches!(objective, OptSpec::Weights(_))));
}

#[test]
fn parse_errors() {
    // No objective at all.
    assert!(parse_module("sig A {}\nmaximize for 3").is_err());
    // Empty weights.
    assert!(parse_module("sig A {}\nmaximize weights {} for 3").is_err());
    // Unknown relation surfaces at lower time, not parse time.
    let m = parse_module("sig A {}\nmaximize weights { Nope: 1 } for 3").expect("parse");
    assert!(run_opt_command(&m, 0).is_err());
}

#[test]
fn opt_max_cardinality_end_to_end() {
    let m = parse_module("sig A {}\nfact { some A }\nmaximize : #A for 3").expect("parse");
    let sol = run_opt_command(&m, 0).expect("solve");
    assert!(sol.satisfiable);
    assert_eq!(sol.cost, Some(3));
}

#[test]
fn opt_min_weights_end_to_end() {
    let m = parse_module("sig A {}\nminimize weights { A: 1 } { some A } for 3").expect("parse");
    let sol = run_opt_command(&m, 0).expect("solve");
    assert!(sol.satisfiable);
    assert_eq!(sol.cost, Some(1));
}

#[test]
fn opt_two_relations_flaky_shape() {
    // Regression: must be 4 (A full at w=2, B empty at w=-1), never 3.
    let m = parse_module("sig A {}\nsig B {}\nmaximize weights { A: 2, B: -1 } for 2")
        .expect("parse");
    let sol = run_opt_command(&m, 0).expect("solve");
    assert!(sol.satisfiable);
    assert_eq!(sol.cost, Some(4));
}

#[test]
fn parse_maxsome_forms() {
    // Bare expression form parses.
    let m = parse_module("sig A {}\nrun { maxsome A } for 2").expect("parse");
    assert!(command_needs_opt(&m, 0));
    // minsome parses too.
    let m = parse_module("sig A {}\nrun { minsome A } for 2").expect("parse");
    assert!(command_needs_opt(&m, 0));
    // Plain run without softs stays on the SAT path.
    let m = parse_module("sig A {}\nrun { some A } for 2").expect("parse");
    assert!(!command_needs_opt(&m, 0));
    // soft fact parses and routes to optimize.
    let m = parse_module("sig A {}\nsoft fact { some A }\nrun {} for 2").expect("parse");
    assert!(command_needs_opt(&m, 0));
}

#[test]
fn parse_maxsome_rejections() {
    // Declaration form parses (sibling-friendly) but fails at lowering
    // with a clear per-command error (both entry points agree).
    let m = parse_module("sig A {}\nrun { maxsome x: A | some x } for 2").expect("parse");
    let e1 = run_opt_command(&m, 0).expect_err("decl form must fail");
    let e2 = run_command(&m, 0).expect_err("decl form must fail");
    for e in [e1, e2] {
        assert!(e.to_string().contains("declaration form"), "got: {e}");
    }
    // Priorities are a parse error.
    assert!(parse_module("sig A {}\nrun { maxsome[1] A } for 2").is_err());
}

#[test]
fn opt_maxsome_end_to_end() {
    // maxsome A over 3 atoms → all three (cost 3).
    let m = parse_module("sig A {}\nrun { maxsome A } for 3").expect("parse");
    let sol = run_opt_command(&m, 0).expect("solve");
    assert!(sol.satisfiable);
    assert_eq!(sol.cost, Some(3));
    // minsome A unconstrained → empty (cost 0).
    let m = parse_module("sig A {}\nrun { minsome A } for 3").expect("parse");
    let sol = run_opt_command(&m, 0).expect("solve");
    assert!(sol.satisfiable);
    assert_eq!(sol.cost, Some(0));
    // minsome with a lower bound: `some A` forces exactly one.
    let m = parse_module("sig A {}\nrun { some A and minsome A } for 3").expect("parse");
    let sol = run_opt_command(&m, 0).expect("solve");
    assert!(sol.satisfiable);
    assert_eq!(sol.cost, Some(1));
}

#[test]
fn opt_soft_fact_end_to_end() {
    // soft fact prefers empty A, but the hard fact forces non-empty:
    // optimum violates the soft fact (cost 0), still SAT.
    let m = parse_module("sig A {}\nfact { some A }\nsoft fact { no A }\nrun {} for 2")
        .expect("parse");
    let sol = run_opt_command(&m, 0).expect("solve");
    assert!(sol.satisfiable);
    assert_eq!(sol.cost, Some(0));
    // Without the hard fact, the soft fact is satisfiable (cost 1).
    let m = parse_module("sig A {}\nsoft fact { no A }\nrun {} for 2").expect("parse");
    let sol = run_opt_command(&m, 0).expect("solve");
    assert!(sol.satisfiable);
    assert_eq!(sol.cost, Some(1));
}

#[test]
fn run_command_rejects_soft() {
    // Plain SAT entry points refuse soft-bearing problems loudly
    // instead of silently dropping the softs.
    let m = parse_module("sig A {}\nrun { maxsome A } for 2").expect("parse");
    assert!(run_command(&m, 0).is_err());
}

// ---------------------------------------------------------------------------
// Temporal optimization via a static mirror (`goal Aopt = A`): the
// objective must reference static relations only (var is uniformly
// excluded); softs + temporal is uniformly rejected.
// ---------------------------------------------------------------------------

const TEMP_MIRROR: &str = "module t
var sig A in Signed
sig Aopt in Signed
fact {always {A' = 0 - A}}
fact {goal Aopt = A}
";

#[test]
fn temporal_opt_maximize_static_mirror() {
    // A(0) free; dynamics force A(2k) = A(0), A(2k+1) = -A(0).
    // Last state (4) mirrors A(0); max bitmask over W=3 subsets is 3
    // ({0, 1}: -3's negation {0, 2} stays representable, unlike -4's 4).
    let src = format!("{TEMP_MIRROR}maximize: Aopt for 5 steps, 3 int");
    let m = parse_module(&src).expect("parse");
    let sol = run_opt_command(&m, 0).expect("solve");
    assert!(sol.satisfiable);
    assert_eq!(sol.cost, Some(3));
    let ti = sol.temporal.expect("temporal trace attached");
    assert_eq!(ti.len(), 5);
    // Aopt is static: identical in every state, equal to the last A.
    let vals: Vec<i64> = ti
        .states()
        .iter()
        .map(|st| {
            let r = st.find_relation_by_name("Aopt").expect("Aopt");
            let ts = st.tuples(r).expect("tuples");
            ts.index_view()
                .iter()
                .map(|idx| {
                    let v: i64 = st.universe().atom(idx as usize).expect("atom").parse().expect("int");
                    if v == 2 { -(1i64 << 2) } else { 1i64 << v }
                })
                .sum()
        })
        .collect();
    assert_eq!(vals, vec![3, 3, 3, 3, 3]);
}

#[test]
fn temporal_opt_minimize_static_mirror() {
    // Min bitmask: -4 ({2}) is infeasible since -(−4) = 4 is
    // unrepresentable at W=3; optimum is -3 ({0, 2}).
    let src = format!("{TEMP_MIRROR}minimize: Aopt for 5 steps, 3 int");
    let m = parse_module(&src).expect("parse");
    let sol = run_opt_command(&m, 0).expect("solve");
    assert!(sol.satisfiable);
    assert_eq!(sol.cost, Some(-3));
    assert!(sol.temporal.is_some());
}

#[test]
fn temporal_opt_rejects_var_objective() {
    // Direct var reference: explicit error naming the relation.
    let src = "module t
var sig A in Signed
fact {always {A' = 0 - A}}
maximize: A for 5 steps, 3 int";
    let m = parse_module(src).expect("parse");
    let e = run_opt_command(&m, 0).expect_err("var objective must fail");
    assert!(e.to_string().contains("static relations only"), "got: {e}");
    assert!(e.to_string().contains('A'), "got: {e}");
}

#[test]
fn temporal_opt_rejects_var_weights() {
    let src = "module t
var sig A {}
sig B {}
maximize weights { A: 1 } for 3 steps but A 1, B 1";
    let m = parse_module(src).expect("parse");
    let e = run_opt_command(&m, 0).expect_err("var weights must fail");
    assert!(e.to_string().contains("static relations only"), "got: {e}");
}

#[test]
fn temporal_opt_rejects_softs() {
    let src = "module t
var sig A {}
sig Aopt in Signed
fact {always (some A)}
fact {goal Aopt = A}
fact { maxsome Aopt }
maximize: Aopt for 3 steps but A 1";
    let m = parse_module(src).expect("parse");
    let e = run_opt_command(&m, 0).expect_err("softs+temporal must fail");
    assert!(e.to_string().contains("soft"), "got: {e}");
}

// ---------------------------------------------------------------------------
// In-body markers `maximize <intexpr>` / `minimize <intexpr>`:
//   pred mp { goal (maximize A) }   run { mp } for 5 steps, 3 int
// The marker is hard `true`; its target becomes the command's objective,
// evaluated at the state pinned by the innermost `initially` (first) /
// `goal` (last) / `restore` (loop) operator. Without temporal operators
// the target is evaluated statically.
// ---------------------------------------------------------------------------

#[test]
fn parse_in_body_markers() {
    let m = parse_module("sig A {}\npred mp { maximize #A }\nrun { mp } for 3").expect("parse");
    assert!(m.paras.iter().any(|p| p.body.has_opt_marker()));
    // Routes to the optimizer even though the command is a plain `run`.
    assert!(command_needs_opt(&m, 0));
    // `minimize` and the optional `:` form parse too.
    let m = parse_module("sig A {}\npred mp { minimize: #A }\nrun { mp } for 3").expect("parse");
    assert!(m.paras.iter().any(|p| p.body.has_opt_marker()));
    // `maxsome` is not a marker.
    let m = parse_module("sig A {}\npred mp { maxsome A }\nrun { mp } for 3").expect("parse");
    assert!(!m.paras.iter().any(|p| p.body.has_opt_marker()));
    // The command `weights` block stays command-only.
    assert!(
        parse_module("sig A {}\npred mp { maximize weights { A: 1 } }\nrun { mp } for 3").is_err()
    );
    // A marker whose target fails to lower still routes to the optimizer
    // (shallow scan fallback), so the type error surfaces there.
    let m = parse_module("sig A {}\npred mp { maximize A }\nrun { mp } for 3").expect("parse");
    assert!(command_needs_opt(&m, 0));
    assert!(run_opt_command(&m, 0).is_err());
}

#[test]
fn marker_static_end_to_end() {
    // Single marker: exact single-objective path.
    let m = parse_module("sig A {}\npred mp { maximize #A }\nrun { mp } for 3").expect("parse");
    let sol = run_opt_command(&m, 0).expect("solve");
    assert!(sol.satisfiable);
    assert_eq!(sol.cost, Some(3));

    // Hard conjuncts in the same body stay hard.
    let m = parse_module("sig A {}\nsig B {}\npred mp { maximize #A }\nrun { mp and #B = 2 } for 3")
        .expect("parse");
    let sol = run_opt_command(&m, 0).expect("solve");
    assert_eq!(sol.cost, Some(3));

    // Two markers pool their bit softs (maximize #A = 3, minimize #B = 0).
    let m = parse_module(
        "sig A {}\nsig B {}\npred mp { maximize #A and minimize #B }\nrun { mp } for 3",
    )
    .expect("parse");
    let sol = run_opt_command(&m, 0).expect("solve");
    assert!(sol.satisfiable);
    assert_eq!(sol.cost, Some(3));
}

#[test]
fn marker_rejected_on_plain_paths() {
    let m = parse_module("sig A {}\npred mp { maximize #A }\nrun { mp } for 3").expect("parse");
    let e = run_command(&m, 0).expect_err("plain run must refuse a marker");
    assert!(e.to_string().contains("optimization target"), "got: {e}");
    // Cnf building (`:run` / `:check` in the REPL) refuses too.
    let e = alloy_front_rs::run(&m, 0).expect_err("Cnf build must refuse a marker");
    assert!(e.to_string().contains("optimization target"), "got: {e}");
}

#[test]
fn marker_temporal_goal_matches_static_mirror() {
    // Same model as TEMP_MIRROR, but the goal state is reached directly by
    // the marker (no mirror sig, no `fact {goal Aopt = A}`).
    let src = "module t\nvar sig A in Signed\nfact {always {A' = 0 - A}}\n\
               pred mp { goal (maximize A) }\nrun { mp } for 5 steps, 3 int";
    let m = parse_module(src).expect("parse");
    let sol = run_opt_command(&m, 0).expect("solve");
    assert!(sol.satisfiable);
    assert_eq!(sol.cost, Some(3));
    let ti = sol.temporal.expect("temporal trace attached");
    assert_eq!(ti.len(), 5);
}

#[test]
fn marker_temporal_initially_vs_goal() {
    // All states after the first are forced to {0} (bitmask 1); the
    // first state is free (max bitmask 3 = {0, 1}).
    let head = "module t\nvar sig A in Signed\nfact {always {A' = {0}}}\n";
    let src = format!("{head}pred mp {{ initially (maximize A) }}\nrun {{ mp }} for 5 steps, 3 int");
    let m = parse_module(&src).expect("parse");
    let sol = run_opt_command(&m, 0).expect("solve");
    assert!(sol.satisfiable);
    assert_eq!(sol.cost, Some(3), "initially: A(0) is free");

    let src = format!("{head}pred mp {{ goal (maximize A) }}\nrun {{ mp }} for 5 steps, 3 int");
    let m = parse_module(&src).expect("parse");
    let sol = run_opt_command(&m, 0).expect("solve");
    assert!(sol.satisfiable);
    assert_eq!(sol.cost, Some(1), "goal: A(4) = {{0}} = 1");

    // Minimizing the goal-state value is feasible too (A(4) = {0} = 1).
    let src = format!("{head}pred mp {{ goal (minimize A) }}\nrun {{ mp }} for 5 steps, 3 int");
    let m = parse_module(&src).expect("parse");
    let sol = run_opt_command(&m, 0).expect("solve");
    assert_eq!(sol.cost, Some(1));

    // `restore` pins the loop state, whose A is forced to {0} by the
    // last state's `A' = {0}`.
    let src = format!("{head}pred mp {{ restore (maximize A) }}\nrun {{ mp }} for 5 steps, 3 int");
    let m = parse_module(&src).expect("parse");
    let sol = run_opt_command(&m, 0).expect("solve");
    assert_eq!(sol.cost, Some(1), "restore: loop state A = {{0}}");

    // A `check` negates its body, so a marker there is rejected loudly.
    let src = format!("{head}pred mp {{ goal (maximize A) }}\ncheck {{ mp }} for 5 steps, 3 int");
    let m = parse_module(&src).expect("parse");
    let e = run_opt_command(&m, 0).expect_err("check + marker must fail");
    assert!(e.to_string().contains("`check` negates"), "got: {e}");
}

#[test]
fn marker_temporal_static_target_under_goal() {
    // A static target under `goal` (the manual-mirror case, written with a
    // marker instead of a `maximize:` command).
    let src = "module t\nvar sig A in Signed\nsig Aopt in Signed\nfact {always {A' = {0}}}\n\
               fact {goal Aopt = A}\npred mp { goal (maximize Aopt) }\nrun { mp } for 5 steps, 3 int";
    let m = parse_module(src).expect("parse");
    let sol = run_opt_command(&m, 0).expect("solve");
    assert!(sol.satisfiable);
    assert_eq!(sol.cost, Some(1));
}

#[test]
fn marker_temporal_initially_keeping_fun_pattern() {
    // The user-facing pattern: a transition function `F` drives the var sig
    // `X` each step, `initially` pins X(0) = 0 (the empty set reads as 0),
    // and the goal state's X is maximized. No mirror sig is needed.
    let src = "module t\nvar sig X in Signed\nfun F : Signed { {1} }\n\
               fact {\n  initially (X = 0)\n  keeping (X' = F)\n}\n\
               pred mp { goal (maximize X) }\nrun { mp } for 5 steps, 3 int";
    let m = parse_module(src).expect("parse");
    let sol = run_opt_command(&m, 0).expect("solve");
    assert!(sol.satisfiable);
    assert_eq!(sol.cost, Some(2), "X(0) = 0, then {{1}} = 2 from state 1 on");
    let ti = sol.temporal.expect("temporal trace attached");
    assert_eq!(ti.len(), 5);
}

#[test]
fn marker_temporal_needs_a_trace_state() {
    let src = "module t\nvar sig A in Signed\nfact {always {A' = {0}}}\n\
               pred mp { maximize A }\nrun { mp } for 3 steps, 3 int";
    let m = parse_module(src).expect("parse");
    let e = run_opt_command(&m, 0).expect_err("temporal marker needs a state");
    assert!(e.to_string().contains("needs a trace state"), "got: {e}");
}

#[test]
fn marker_conflicts_with_command_objective() {
    let src = "sig A {}\npred mp { maximize #A }\nmaximize { mp } : #A for 2";
    let m = parse_module(src).expect("parse");
    let e = run_opt_command(&m, 0).expect_err("mixing both forms must fail");
    assert!(e.to_string().contains("in-body"), "got: {e}");
}
