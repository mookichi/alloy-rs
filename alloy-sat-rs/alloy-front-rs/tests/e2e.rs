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

// --- New expression forms ---

/// `some sig` constrains a sig to have at least one atom.
#[test]
fn some_sig_basic() {
    let src = r#"
        module t
        some sig A {}
        run {} for 3
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

/// `some sig` with exactly 1 scope — must be non-empty → SAT (exactly 1).
#[test]
fn some_sig_exactly_one() {
    let src = r#"
        module t
        some sig A {}
        run {} for exactly 1
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

/// `some sig` with a fact that forces empty — UNSAT.
#[test]
fn some_sig_with_fact_forces_empty() {
    let src = r#"
        module t
        some sig A {}
        fact { no A }
        run {} for 3
    "#;
    assert_eq!(outcome(src, 0), "UNSAT");
}

/// Sig fact block: `sig A {} { some A }` is equivalent to a global fact.
#[test]
fn sig_fact_block_basic() {
    let src = r#"
        module t
        sig A {} { some A }
        run {} for 3
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

/// Sig fact block constrains: `sig A {} { #A > 1 }` with exactly 1 → UNSAT.
#[test]
fn sig_fact_block_unsat() {
    let src = r#"
        module t
        sig A {} { #A > 1 }
        run {} for exactly 1
    "#;
    assert_eq!(outcome(src, 0), "UNSAT");
}

/// Let binding in expression position: `let x = A | some x`
/// (Java parity: `|` separator; `in` is rejected).
#[test]
fn let_expr_position() {
    let src = r#"
        module t
        sig A {}
        pred p { some (let x = A | x) }
        run p for exactly 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

/// Let binding with multiple bindings.
#[test]
fn let_expr_multi_bind() {
    let src = r#"
        module t
        sig A {}
        pred p { some (let x = A, y = A | x + y) }
        run p for exactly 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

/// `sig X in Int` parses (Java parity: accepted, `extends Int` rejected).
#[test]
fn sig_in_int_parses() {
    let m = parse_module("sig X in Int {}\nrun {} for 3").unwrap();
    assert_eq!(m.sigs.len(), 1);
    assert_eq!(m.sigs[0].extends.as_deref(), Some("Int"));
}

/// `sig X in Int` is a subset of the builtin Int: nonempty is SAT.
#[test]
fn sig_in_int_some_sat() {
    let src = r#"
        module t
        sig X in Int {}
        run { some X } for 3
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

/// `sig X in Int` is flexible: empty is SAT too.
#[test]
fn sig_in_int_empty_sat() {
    let src = r#"
        module t
        sig X in Int {}
        run { no X } for 3
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

/// X is a subset of the int atoms: it is disjoint from any plain sig,
// so `some (X & A)` is UNSAT. (Cardinality literals would wrap at the
// default bitwidth 4, so intersection is used instead.)
#[test]
fn sig_in_int_subset_holds() {
    let src = r#"
        module t
        sig A {}
        sig X in Int {}
        run { some (X & A) } for 3
    "#;
    assert_eq!(outcome(src, 0), "UNSAT");
}

/// Transitive subset through an Int subset: `sig Y in X`, `X in Int`.
#[test]
fn sig_in_int_transitive() {
    let src = r#"
        module t
        sig X in Int {}
        sig Y in X {}
        run { some Y } for 3
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

/// Java parity: `sig X extends Int` is rejected with a builtin error.
#[test]
fn sig_extends_int_rejected() {
    let src = r#"
        module t
        sig X extends Int {}
        run {} for 3
    "#;
    let out = outcome(src, 0);
    assert!(
        out.contains("cannot extend the builtin \"Int\" signature"),
        "unexpected: {out}"
    );
}

/// Java parity: a set-typed operand in integer position lowers via the SUM
/// cast (`typecheck_as_int`), so `{x: X | x < -126}` parses as `IntCmp`.
#[test]
fn int_var_lt_parses_as_int_cmp() {
    let f = alloy_front_rs::parse_formula("all x: X | x < -126").expect("parse");
    let dbg = format!("{f:?}");
    assert!(dbg.contains("IntCmp"), "got: {dbg}");
    assert!(dbg.contains("Val"), "got: {dbg}");
}

/// `=` with an int right side takes the bitmask route (`x = 5` is
/// `bitmask(x) = 5`); `A = B` stays relational; `#A = 4` stays IntCmp.
#[test]
fn int_eq_stays_relational() {
    let f = alloy_front_rs::parse_formula("x = 5").expect("parse");
    assert!(format!("{f:?}").contains("IntCmp"), "got: {f:?}");
    assert!(format!("{f:?}").contains("BitsVal"), "got: {f:?}");
    let f = alloy_front_rs::parse_formula("A = B").expect("parse");
    assert!(format!("{f:?}").starts_with("Cmp("), "got: {f:?}");
    // genuinely int-typed `=` keeps the int route (`#A` is cardinality)
    let f = alloy_front_rs::parse_formula("#A = 4").expect("parse");
    assert!(format!("{f:?}").contains("IntCmp"), "got: {f:?}");
}

/// Integer literal in set position: `some 5` (the `{5}` singleton).
/// Bit-vector model: atom 5 needs `for 8 Int` (default W = 4 covers 0..3).
#[test]
fn int_literal_singleton_some() {
    let src = r#"
        module t
        sig A {}
        run { some 5 } for 3, 8 Int
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

/// Bitmask values of scalar Int atoms are positive powers of two
/// (`2^v`), except the MSB atom (`-2^(w-1)`), so `x < 0` is SAT as well
/// (satisfied by x = the MSB atom).
#[test]
fn int_var_lt_some_sat() {
    let src = r#"
        module t
        sig X in Int {}
        run { some x: X | x < 2 } for 3
    "#;
    assert_eq!(outcome(src, 0), "SAT");
    let src2 = r#"
        module t
        sig X in Int {}
        run { some x: X | x < 0 } for 3
    "#;
    assert_eq!(outcome(src2, 0), "SAT");
}

/// Above the bitwidth-4 maximum (7), no X atom qualifies: UNSAT.
#[test]
fn int_var_gt_unsat() {
    let src = r#"
        module t
        sig X in Int {}
        run { some x: X | x > 7 } for 3
    "#;
    assert_eq!(outcome(src, 0), "UNSAT");
}

/// Exact atom matching goes through braces: `x = {0}` is SAT, while
/// `x = 0` (bitmask read: 2^v = 0 is impossible) is UNSAT.
#[test]
fn int_var_eq_zero_sat() {
    let sat_src = r#"
        module t
        sig X in Int {}
        run { some x: X | x = {0} } for 3
    "#;
    assert_eq!(outcome(sat_src, 0), "SAT");
    let unsat_src = r#"
        module t
        sig X in Int {}
        run { some x: X | x = 0 } for 3
    "#;
    assert_eq!(outcome(unsat_src, 0), "UNSAT");
}

/// Java parity: `{x: X}` without `| body` enumerates the whole domain.
#[test]
fn comprehension_without_filter() {
    let src = r#"
        module t
        sig X in Int {}
        fact pin { X = {1} + {2} + {3} }
        pred p { {x: X} = X }
        run p for 3
    "#;
    assert_eq!(outcome(src, 0), "SAT");
    let src2 = r#"
        module t
        sig A {}
        run { some {x: A} } for 3
    "#;
    assert_eq!(outcome(src2, 0), "SAT");
}

/// `{A, B}` set literal in formula position.
#[test]
fn set_literal_formula() {
    let src = r#"
        module t
        sig A {} sig B {}
        pred p { {A, B} = (A + B) }
        run p for 3
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

/// `{}` is the empty set literal (same as `none`).
#[test]
fn set_literal_empty() {
    let src = r#"
        module t
        sig A {}
        pred p { {} = none and no {} }
        run p for 3
    "#;
    assert_eq!(outcome(src, 0), "SAT");
    let src2 = r#"
        module t
        sig A {}
        pred p { some {} }
        run p for 3
    "#;
    assert_eq!(outcome(src2, 0), "UNSAT");
}

/// `{1+1}` is `{2}` (folded), not `{1}`.
#[test]
fn set_literal_fold_eq() {
    let sat = r#"
        module t
        sig A {}
        pred p { {1+1} = {2} }
        run p for 3
    "#;
    assert_eq!(outcome(sat, 0), "SAT");
    let unsat = r#"
        module t
        sig A {}
        pred p { {1+1} = {1} }
        run p for 3
    "#;
    assert_eq!(outcome(unsat, 0), "UNSAT");
}

/// Binding domains fold pure literal arithmetic: `{x: 1+2}` is `{3}`.
#[test]
fn quant_domain_fold_eq() {
    let sat = r#"
        module t
        sig A {}
        pred p { {x: 1+2} = {3} }
        run p for 3
    "#;
    assert_eq!(outcome(sat, 0), "SAT");
    let unsat = r#"
        module t
        sig A {}
        pred p { {x: 1+2} = {1, 2} }
        run p for 3
    "#;
    assert_eq!(outcome(unsat, 0), "UNSAT");
}

/// `sum e` over a unary set (Java parity), incl. braced comprehension.
#[test]
fn sum_of_set() {
    let sat = r#"
        module t
        sig X in Int {}
        fact pin { X = {1} + {2} + {3} }
        pred p { (sum X) = 6 }
        run p for 3
    "#;
    assert_eq!(outcome(sat, 0), "SAT");
    let unsat = r#"
        module t
        sig X in Int {}
        fact pin { X = {1} + {2} + {3} }
        pred p { (sum X) = 7 }
        run p for 3
    "#;
    assert_eq!(outcome(unsat, 0), "UNSAT");
    let braced = r#"
        module t
        sig X in Int {}
        fact pin { X = {1} + {2} + {3} }
        pred p { (sum {x: X | some x}) = 6 }
        run p for 3
    "#;
    assert_eq!(outcome(braced, 0), "SAT");
}

/// `set = sum {...}` is a bitmask read of the set side (uniform rule):
/// `X = sum {1,2}` holds iff bitmask(X) = 3, i.e. X = {0, 1}.
#[test]
fn set_eq_sum_mask() {
    let sat = r#"
        module t
        sig X in Int {}
        fact pin { X = {1} + {2} + {3} }
        pred p { X = sum {1, 2} }
        run p for 3, 8 Int
    "#;
    // X = {1,2,3}, bitmask(X) = 2+4-8 = -2 != 3
    assert_eq!(outcome(sat, 0), "UNSAT");
    let sat2 = r#"
        module t
        sig X in Int {}
        fact pin { X = {0} + {1} }
        pred p { X = sum {1, 2} }
        run p for 3, 8 Int
    "#;
    // X = {0,1}, bitmask(X) = 1+2 = 3 = sum {1,2}
    assert_eq!(outcome(sat2, 0), "SAT");
    // mirrored form (`sum Y = X` rewinds to the gate-2 desugar) and `!=`
    let mirror = r#"
        module t
        sig X in Int {}
        sig Y in Int {}
        fact pin { X = {0}  Y = {1} }
        pred p { (sum Y) = X and X != sum {2} }
        run p for 3, 8 Int
    "#;
    // sum(Y) = 1, bitmask(X) = 1: equal and not 2
    assert_eq!(outcome(mirror, 0), "SAT");
}
