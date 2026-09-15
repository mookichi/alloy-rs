//! AST-level partial instances: `partial` blocks + `pin`/`avoid`.
//!
//! - `=` is exact, `L in R` is lower, `R in S` is upper; all desugar to
//!   an existential over gensym label variables (diagram method).
//! - `avoid P` is `Not(pin P)`.
//! - Labels (`Sig$tag`) are block-local; same-prefix labels are distinct.

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

fn outcome_is(src: &str, prefix: &str) -> bool {
    outcome(src, 0).starts_with(prefix)
}

#[test]
fn pin_exact_basic() {
    let src = r#"
        module t
        sig A {}
        partial p1 { A = A$x + A$y }
        run { pin p1 } for 3
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn pin_exact_forces_cardinality() {
    // `#A = 2` is compatible with a 2-label exact pin...
    let sat = r#"
        module t
        sig A {}
        partial p1 { A = A$x + A$y }
        run { pin p1 and #A = 2 } for 3
    "#;
    assert_eq!(outcome(sat, 0), "SAT");
    // ...but not with `#A = 3` (exactness proof).
    let unsat = r#"
        module t
        sig A {}
        partial p1 { A = A$x + A$y }
        run { pin p1 and #A = 3 } for 3
    "#;
    assert_eq!(outcome(unsat, 0), "UNSAT");
}

#[test]
fn pin_lower_allows_extra() {
    // `x in A` is a lower bound only: extra atoms are fine.
    let src = r#"
        module t
        sig A {}
        partial p1 { A$x in A }
        run { pin p1 and #A = 3 } for 3
    "#;
    assert_eq!(outcome(src, 0), "SAT");
    // `some A` is all it takes on its own.
    let src2 = r#"
        module t
        sig A {}
        partial p1 { A$x in A }
        run { pin p1 } for 3
    "#;
    assert_eq!(outcome(src2, 0), "SAT");
}

#[test]
fn pin_upper_bounds_cardinality() {
    // `A in {x}` caps the size: `#A = 2` is out.
    let unsat = r#"
        module t
        sig A {}
        partial p1 { A in A$x }
        run { pin p1 and #A = 2 } for 3
    "#;
    assert_eq!(outcome(unsat, 0), "UNSAT");
    let sat = r#"
        module t
        sig A {}
        partial p1 { A in A$x }
        run { pin p1 and #A = 1 } for 3
    "#;
    assert_eq!(outcome(sat, 0), "SAT");
}

#[test]
fn pin_exact_empty() {
    let src = r#"
        module t
        sig A {}
        partial p0 { A = {} }
        run { pin p0 } for 3
    "#;
    assert_eq!(outcome(src, 0), "SAT");
    let unsat = r#"
        module t
        sig A {}
        partial p0 { A = {} }
        run { pin p0 and some A } for 3
    "#;
    assert_eq!(outcome(unsat, 0), "UNSAT");
}

#[test]
fn avoid_is_dual() {
    // `avoid {A={x,y}}` rules out exactly-2; other sizes survive.
    let sat = r#"
        module t
        sig A {}
        partial p1 { A = A$x + A$y }
        run { avoid p1 and #A = 3 } for 3
    "#;
    assert_eq!(outcome(sat, 0), "SAT");
    // ...but combined with `#A = 2` nothing is left.
    let unsat = r#"
        module t
        sig A {}
        partial p1 { A = A$x + A$y }
        run { avoid p1 and #A = 2 } for 3
    "#;
    assert_eq!(outcome(unsat, 0), "UNSAT");
    // degenerate lower-avoid: `avoid {x in A}` is `A = {}`.
    let empty = r#"
        module t
        sig A {}
        partial p1 { A$x in A }
        run { avoid p1 and some A } for 3
    "#;
    assert_eq!(outcome(empty, 0), "UNSAT");
}

#[test]
fn labels_shared_across_entries() {
    // The same label in two entries is the same atom: join structure.
    // (Bare `f` names the binary field relation; `B.f` would be its
    // unary join image.)
    let src = r#"
        module t
        sig A {} sig B { f: A }
        partial p1 { A$x in A, B$z -> A$x in f }
        run { pin p1 } for 3
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn distinct_labels_are_distinct_atoms() {
    // Same-prefix labels are pairwise distinct: one atom cannot serve both.
    let src = r#"
        module t
        one sig A {}
        partial p1 { A = A$x + A$y }
        run { pin p1 } for 3
    "#;
    assert_eq!(outcome(src, 0), "UNSAT");
}

#[test]
fn pin_is_idempotent_and_defs_independent() {
    // `pin P and pin P` ≡ `pin P`.
    let src = r#"
        module t
        sig A {}
        partial p1 { A = A$x + A$y }
        run { pin p1 and pin p1 and #A = 2 } for 3
    "#;
    assert_eq!(outcome(src, 0), "SAT");
    // Different definitions use independent variables.
    let src2 = r#"
        module t
        sig A {}
        partial p1 { A = A$x }
        partial p2 { A = A$x }
        run { pin p1 and pin p2 } for 3
    "#;
    assert_eq!(outcome(src2, 0), "SAT");
}

#[test]
fn mixed_entry_kinds() {
    let src = r#"
        module t
        sig A {} sig B { f: A }
        partial p1 { A$x in A, f = B$z -> A$x }
        run { pin p1 } for 3
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn unknown_partial_is_error() {
    let src = r#"
        module t
        sig A {}
        run { pin nope } for 3
    "#;
    assert!(outcome_is(src, "error:"));
}

#[test]
fn partial_rejects_bad_entries() {
    // `!=` / `not in` are not entries (use `avoid`).
    for entry in ["A != A$x", "A$x not in A"] {
        let src = format!("module t\nsig A {{}}\npartial p1 {{ {entry} }}\nrun {{}} for 3");
        assert!(
            outcome_is(&src, "parse-error:"),
            "accepted bad entry: {entry}"
        );
    }
    // Both sides relations: an ordinary formula, not a diagram row.
    // (Unused partials never lower, so `pin` must reference it.)
    let src = "module t\nsig A {} sig B {}\npartial p1 { A in B }\nrun { pin p1 } for 3";
    assert!(outcome_is(src, "error:"));
    // Both sides labels: nothing to constrain.
    let src = "module t\nsig A {}\npartial p1 { A$x = A$y }\nrun { pin p1 } for 3";
    assert!(outcome_is(src, "error:"));
    // Neither side labels: write it outside the block.
    let src = "module t\nsig A {} sig B {}\npartial p1 { A = B }\nrun { pin p1 } for 3";
    assert!(outcome_is(src, "error:"));
    // Duplicate block names.
    let src = "module t\nsig A {}\npartial p1 { A = {} }\npartial p1 { A = {} }\nrun {} for 3";
    assert!(outcome_is(src, "parse-error:"));
    // Empty block.
    let src = "module t\nsig A {}\npartial p1 { }\nrun {} for 3";
    assert!(outcome_is(src, "parse-error:"));
}

#[test]
fn partial_rejects_non_label_shapes() {
    // Dotted references are fine on the relation side, but label-
    // carrying joins, comprehensions, and bare `Int` are not label sets.
    let ok = "module t\nsig A {}\npartial p1 { A = A$x }\nrun { pin p1 } for 3";
    assert_eq!(outcome(ok, 0), "SAT");
    for entry in ["A$x.f = A", "A = {x: A}", "A = Int"] {
        let src = format!("module t\nsig A {{ f: A }}\npartial p1 {{ {entry} }}\nrun {{}} for 3");
        assert!(
            outcome_is(&src, "parse-error:"),
            "accepted bad shape: {entry}"
        );
    }
    // Unknown sig prefix and malformed tags fail at lowering.
    for entry in ["A = Q$x", "A = A$"] {
        let src = format!("module t\nsig A {{}}\npartial p1 {{ {entry} }}\nrun {{ pin p1 }} for 3");
        assert!(
            outcome_is(&src, "error:"),
            "accepted bad label: {entry}"
        );
    }
    // `Int` prefix is not a sig.
    let src = "module t\nsig A {}\npartial p1 { A = Int$x }\nrun { pin p1 } for 3";
    assert!(outcome_is(src, "error:"));
}

#[test]
fn partial_name_with_dollar_rejected() {
    let src = "module t\nsig A {}\npartial p$1 { A = {} }\nrun {} for 3";
    assert!(outcome_is(src, "parse-error:"));
}
