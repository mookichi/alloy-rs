//! `..` — retain-join: like `.`, but the joined column stays in the
//! result.
//!
//! `.` joins the left's last column against the right's first and
//! *consumes* it, so `a->b . b->c` collapses to `a->c` (arity 2). `..`
//! joins on the same columns and *keeps* that column, so the result is
//! arity `l + r - 1` and `a->b .. b->c` is `a->b->c`.
//!
//! That is the relational product `{a, b, c | a->b in R and b->c in S}`.
//! `^r` reports only whether a path exists; a `..` chain enumerates paths
//! keeping every intermediate node, which is the part closure cannot say.
//!
//! The lowering desugars to existing primitives —
//! `(R × univ^(r-1)) ∩ (univ^(l-1) × S)`, both sides padded to `l+r-1` —
//! rather than adding a backend operator. See docs/mepk_valid.md 5.5 for
//! the measurement behind that choice.

use alloy_front_rs::{parse_expr, parse_module, run, solve, BinOp, Expr};

fn sat(src: &str) {
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("run");
    assert!(solve(&cnf).expect("solve").is_some(), "expected SAT: {src}");
}

fn unsat(src: &str) {
    let m = parse_module(src).expect("run parse");
    let cnf = run(&m, 0).expect("run");
    assert!(
        solve(&cnf).expect("solve").is_none(),
        "expected UNSAT: {src}"
    );
}

fn build_err(src: &str, want: &str) {
    let m = parse_module(src).expect("parse");
    match run(&m, 0) {
        Ok(_) => panic!("expected build error: {src}"),
        Err(e) => {
            let msg = format!("{e:?}");
            assert!(msg.contains(want), "error {msg:?} should mention {want:?} ({src})");
        }
    }
}

/// The operator means exactly the comprehension that already existed in
/// Alloy. That is the whole justification for the sugar: nothing here is
/// expressible that `{a, b, c | a->b in R and b->c in S}` was not, so if
/// these two ever disagree the lowering is wrong, not the model.
#[test]
fn matches_the_comprehension_definition() {
    sat("sig A, B, C {}\npred p { (A->B)..(B->C) = {a: A, b: B, c: C | a->b in A->B and b->c in B->C} }\nrun p");
    sat("sig A, B, C, D {}\npred p { (A->B)..(B->C)..(C->D) = {a: A, b: B, c: C, d: D | a->b in A->B and b->c in B->C and c->d in C->D} }\nrun p");
    // With real data present, not just over the empty top bounds.
    sat("sig A, B, C {}\none sig a1, a2 in A {}\none sig b in B {}\none sig c1, c2 in C {}\nfact { a1->b in A->B and b->c1 in B->C and b->c2 in B->C }\npred p { (A->B)..(B->C) = {a: A, b: B, c: C | a->b in A->B and b->c in B->C} }\nrun p");
}

/// The defining contrast with `.`: same columns, different result.
///
/// Arity cannot be pinned by `= A->C`, since comparing an arity-3 result
/// against an arity-2 relation auto-promotes the short side with `univ`
/// (existing behaviour for every relational operator, `lower_formula_cmp`
/// calls `promote_arity`), so that comparison is satisfiable either way.
/// Tuple membership is the honest test: a 3-tuple is in the `..` result
/// and cannot be in the `.` result.
#[test]
fn differs_from_dot() {
    // `.` collapses to arity 2.
    sat("sig A, B, C {}\none sig a in A {}\none sig b in B {}\none sig c in C {}\nfact { a->b in A->B and b->c in B->C }\npred p { a->c in (A->B).(B->C) }\nrun p");
    // `..` keeps the middle column, so the 3-tuple is in the result.
    sat("sig A, B, C {}\none sig a in A {}\none sig b in B {}\none sig c in C {}\nfact { a->b in A->B and b->c in B->C }\npred p { a->b->c in (A->B)..(B->C) }\nrun p");
    // And the two results are not the same relation.
    sat("sig A, B, C {}\npred p { (A->B)..(B->C) != (A->B).(B->C) }\nrun p");
}

/// Both operands must agree on the boundary column. `A->B` joined with
/// `A->C` has `b` against `a`, so nothing survives — this is what keeps
/// `..` a *boundary* join rather than a match-anywhere one.
#[test]
fn non_matching_boundary_is_empty() {
    unsat("sig A, B, C {}\none sig a in A {}\none sig b in B {}\none sig c in C {}\nfact { a->b in A->B and a->c in A->C }\npred p { (A->B)..(A->C) != none }\nrun p");
    // The aligned form does produce tuples.
    sat("sig A, B, C {}\none sig a in A {}\none sig b in B {}\none sig c in C {}\nfact { a->b in A->B and b->c in B->C }\npred p { (A->B)..(B->C) != none }\nrun p");
}

/// A chain enumerates paths of that length with every intermediate node,
/// which is what `^r` cannot express (it only answers reachability).
#[test]
fn chain_enumerates_paths() {
    sat("sig A, B, C, D {}\npred p { (A->B)..(B->C)..(C->D) = A->B->C->D }\nrun p");
    // Three hops is arity 4: the full path with both intermediates is in
    // the result. (A quantified comprehension over a 4-ary domain is not
    // available — higher-order quantification is unary-only — so membership
    // of the concrete path is the test.)
    sat("sig A, B, C, D {}\none sig a in A {}\none sig b in B {}\none sig c in C {}\none sig d in D {}\nfact { a->b in A->B and b->c in B->C and c->d in C->D }\npred p { a->b->c->d in (A->B)..(B->C)..(C->D) }\nrun p");
}

/// `..` sits in `parse_join` beside `.`, so both nest the same way and mix
/// without parentheses. Note they nest to the *right* (`a.b.c` is
/// `a . (b . c)`), not left-associatively as the module docs state for the
/// other binary operators; that is harmless for `.` and `..` because both
/// are associative, and it is pre-existing behaviour being matched rather
/// than a new choice.
#[test]
fn precedence_and_associativity() {
    // `..` chains like `.` chains.
    let e = parse_expr("a..b..c").expect("parse");
    let (op, rest) = match &e {
        Expr::Bin(op, _, r) => (*op, r),
        other => panic!("expected Bin, got {other:?}"),
    };
    assert_eq!(op, BinOp::RetainJoin);
    assert!(matches!(rest.as_ref(), Expr::Bin(BinOp::RetainJoin, _, _)));

    // Mixed with `.` at the same level: `a.b..c.d` is `a . (b .. (c.d))`.
    let e = parse_expr("a.b..c.d").expect("parse");
    let (op, rest) = match &e {
        Expr::Bin(op, _, r) => (*op, r),
        other => panic!("expected Bin, got {other:?}"),
    };
    assert_eq!(op, BinOp::Join);
    match rest.as_ref() {
        Expr::Bin(BinOp::RetainJoin, _, tail) => {
            assert!(matches!(tail.as_ref(), Expr::Bin(BinOp::Join, _, _)));
        }
        other => panic!("expected RetainJoin, got {other:?}"),
    }

    // `..` binds tighter than union, like every relational operator.
    let e = parse_expr("a..b+c..d").expect("parse");
    assert!(matches!(e, Expr::Bin(BinOp::Union, _, _)));
}

/// Field type position: arity `l + r - 1`.
#[test]
fn field_type_arity() {
    // `A..B` is arity 3, so a field declared with it can hold 3-tuples.
    sat("sig A, B {}\nsig C { f: A..B }\nsig D {}\none sig d in D {}\nfact { d->C.f = d->C.f }\nrun {}");
    // `A..B..C` is arity 4.
    sat("sig A, B, C {}\nsig D { f: A..B..C }\nsig E {}\none sig e in E {}\nfact { e->D.f = e->D.f }\nrun {}");
    // A lone boundary column yields no tuples, so `some f` is UNSAT.
    unsat("sig A, B {}\nsig C { f: A..B }\npred p { some f }\nrun p");
}

/// Both sides need a boundary column, and a lane label is an integer.
#[test]
fn rejections() {
    build_err(
        "sig A {}\npred p { (A..univ) != none }\nrun p",
        "retain-join needs two relations",
    );
    build_err(
        "sig A, B {}\npred p { (A->B..A) != none }\nrun p",
        "retain-join needs two relations",
    );
    // A lane label on the right is the same category error as with `.`:
    // a lane is an integer, not a relation.
    build_err(
        "sig A in Real {}\npred p { (A..m) != none }\nrun p",
        "reads a bit lane",
    );
    build_err(
        "sig A in Real {}\npred p { (A->A..e) != none }\nrun p",
        "reads a bit lane",
    );
}
