//! Alloy6 operator precedence and associativity (shape tests).
//!
//! - Expressions (loosest first): `+ -`, `++`, `&`, `->` (`<->`, `-<`
//!   same level), `<:`/`:>`, unary/`'`/`.`/`[]`. Binary operators are
//!   left-associative.
//! - Formulas: binary temporal connectives (weakest, non-associative), then
//!   `||`, `<=>` (left-assoc), `=>` (right-assoc), `&&`, unary/`!`/`not`.

use alloy_front_rs::{parse_expr, parse_formula, parse_module, run_command, BinOp, Expr, Formula};

fn ex(src: &str) -> Expr {
    parse_expr(src).unwrap_or_else(|e| panic!("cannot parse expr {src:?}: {e}"))
}

fn fm(src: &str) -> Formula {
    parse_formula(src).unwrap_or_else(|e| panic!("cannot parse formula {src:?}: {e}"))
}

fn is_name(e: &Expr, want: &str) -> bool {
    matches!(e, Expr::Name(n, _) if n == want)
}

fn as_bin(e: &Expr) -> (BinOp, &Expr, &Expr) {
    match e {
        Expr::Bin(op, l, r) => (*op, l, r),
        other => panic!("expected Bin, got {other:?}"),
    }
}

// `a->b + c->d` == `(a->b) + (c->d)`: product binds tighter than union.
#[test]
fn arrow_tighter_than_union() {
    let e = ex("a->b + c->d");
    let (op, l, r) = as_bin(&e);
    assert_eq!(op, BinOp::Union);
    assert_eq!(as_bin(l).0, BinOp::Product);
    assert_eq!(as_bin(r).0, BinOp::Product);
    assert!(is_name(as_bin(l).1, "a"));
    assert!(is_name(as_bin(r).1, "c"));
}

// `a->b->c` == `(a->b)->c`: left associativity.
#[test]
fn arrow_left_assoc() {
    let e = ex("a->b->c");
    let (op, l, r) = as_bin(&e);
    assert_eq!(op, BinOp::Product);
    assert!(is_name(r, "c"));
    let (op2, ll, lr) = as_bin(l);
    assert_eq!(op2, BinOp::Product);
    assert!(is_name(ll, "a") && is_name(lr, "b"));
}

// `a&b->c&d` == `(a&(b->c))&d`: product binds tighter than intersection
// (like `*` over `+`: `a+b*c+d` == `(a+(b*c))+d`).
#[test]
fn arrow_tighter_than_intersect() {
    let e = ex("a&b->c&d");
    let (op, l, r) = as_bin(&e);
    assert_eq!(op, BinOp::Intersect);
    assert!(is_name(r, "d"));
    let (op2, ll, lr) = as_bin(l);
    assert_eq!(op2, BinOp::Intersect);
    assert!(is_name(ll, "a"));
    assert_eq!(as_bin(lr).0, BinOp::Product);
}

// `a+b->c` == `a+(b->c)`: union is the loosest expression operator.
#[test]
fn union_loosest() {
    let e = ex("a+b->c");
    let (op, l, r) = as_bin(&e);
    assert_eq!(op, BinOp::Union);
    assert!(is_name(l, "a"));
    assert_eq!(as_bin(r).0, BinOp::Product);
}

// `a++b+c` == `(a++b)+c`: override binds tighter than union.
#[test]
fn override_tighter_than_union() {
    let e = ex("a++b+c");
    let (op, l, _) = as_bin(&e);
    assert_eq!(op, BinOp::Union);
    assert_eq!(as_bin(l).0, BinOp::Override);
}

// `a<->b` == `b->a`: reverse product preserved at arrow level.
#[test]
fn sharrow_is_reverse_product() {
    let e = ex("a<->b");
    let (op, l, r) = as_bin(&e);
    assert_eq!(op, BinOp::Product);
    assert!(is_name(l, "b") && is_name(r, "a"));
}

// `a<->b->c` == `(b->a)->c`: `<->` shares the left-assoc arrow loop.
#[test]
fn sharrow_joins_arrow_loop() {
    let e = ex("a<->b->c");
    let (op, l, r) = as_bin(&e);
    assert_eq!(op, BinOp::Product);
    assert!(is_name(r, "c"));
    let (op2, ll, lr) = as_bin(l);
    assert_eq!(op2, BinOp::Product);
    assert!(is_name(ll, "b") && is_name(lr, "a"));
}

// `<=>` is left-associative: `a<=>b<=>c` == `(a<=>b)<=>c`.
#[test]
fn iff_left_assoc() {
    // Bare names in formula position lower as zero-arg calls; compare shapes.
    let f = fm("a<=>b<=>c");
    match f {
        Formula::Iff(l, r) => {
            assert!(matches!(*l, Formula::Iff(..)), "got {l:?}");
            assert!(matches!(*r, Formula::Call(..)), "got {r:?}");
        }
        other => panic!("expected Iff, got {other:?}"),
    }
}

// `=>` stays right-associative: `a=>b=>c` == `a=>(b=>c)`.
#[test]
fn implies_right_assoc() {
    let f = fm("a=>b=>c");
    match f {
        Formula::Implies(_, r) => assert!(matches!(*r, Formula::Implies(..)), "got {r:?}"),
        other => panic!("expected Implies, got {other:?}"),
    }
}

// `||` is looser than `&&`: `a&&b||c` == `(a&&b)||c`.
#[test]
fn or_looser_than_and() {
    let f = fm("some A && some B || some C");
    match f {
        Formula::Or(l, _) => assert!(matches!(*l, Formula::And(..)), "got {l:?}"),
        other => panic!("expected Or, got {other:?}"),
    }
}

// Binary temporal connectives are the weakest: `a until b || c` stays whole
// on the right (`a until (b || c)`), and `a || b until c` groups the `||`
// on the left (`(a || b) until c`).
#[test]
fn temporal_weakest() {
    match fm("some A until some B || some C") {
        Formula::Until(_, r) => assert!(matches!(*r, Formula::Or(..)), "got {r:?}"),
        other => panic!("expected Until, got {other:?}"),
    }
    match fm("some A || some B until some C") {
        Formula::Until(l, _) => assert!(matches!(*l, Formula::Or(..)), "got {l:?}"),
        other => panic!("expected Until, got {other:?}"),
    }
    // Bare zero-arg predicate calls work as temporal operands too.
    match fm("p until q || r") {
        Formula::Until(_, r) => assert!(matches!(*r, Formula::Or(..)), "got {r:?}"),
        other => panic!("expected Until, got {other:?}"),
    }
}

// Binary temporal connectives are non-associative: chaining is an error.
#[test]
fn temporal_nonassoc() {
    assert!(parse_formula("some A until some B until some C").is_err());
    assert!(parse_formula("some A until some B releases some C").is_err());
    assert!(parse_formula("(some A until some B) until some C").is_ok());
}

// Temporal unaries bind tightly: `always a && b` == `(always a) && b`.
#[test]
fn temporal_unary_tight() {
    match fm("always some A && some B") {
        Formula::And(l, _) => assert!(matches!(*l, Formula::Always(..)), "got {l:?}"),
        other => panic!("expected And, got {other:?}"),
    }
    match fm("not some A && some B") {
        Formula::And(l, _) => assert!(matches!(*l, Formula::Not(..)), "got {l:?}"),
        other => panic!("expected And, got {other:?}"),
    }
}

// `a -< b` == `b->a`: the `-<` spelling shares the arrow loop.
// Glued only: `a - <b` (spaces) stays minus plus comparison.
#[test]
fn revarrow_is_reverse_product() {
    let e = ex("a-<b");
    let (op, l, r) = as_bin(&e);
    assert_eq!(op, BinOp::Product);
    assert!(is_name(l, "b") && is_name(r, "a"));
    // Spaced `- <` must not become a product.
    assert!(parse_expr("a - <b").is_err());
}

// `:>` parses at the `<:` level: `a:>b->c` == `(a:>b)->c`.
#[test]
fn range_restrict_level() {
    let e = ex("a:>b");
    let (op, l, r) = as_bin(&e);
    assert_eq!(op, BinOp::RangeRestrict);
    assert!(is_name(l, "a") && is_name(r, "b"));
    let e2 = ex("a:>b->c");
    let (op2, l2, r2) = as_bin(&e2);
    assert_eq!(op2, BinOp::Product);
    assert!(is_name(r2, "c"));
    assert_eq!(as_bin(l2).0, BinOp::RangeRestrict);
}

// Declaration types keep their own arrow loop with multiplicity placement.
#[test]
fn decl_types_unaffected() {
    let m = parse_module("sig A {} sig B { f: A -> lone B, g: A + B }").expect("parse");
    assert_eq!(m.sigs.len(), 2);
}

// End to end: range restriction keeps tuples whose last column is in range.
// (`one sig` singletons stand in for atom literals, which are rejected in
// model text since atoms are solver outputs, not language terms.)
#[test]
fn range_restrict_solves() {
    let src = "sig A {}\none sig A1 extends A {}\nsig B { f: A }\nrun { f :> A1 = B->A1 } for 2";
    let m = parse_module(src).expect("parse");
    let sol = run_command(&m, 0).expect("run");
    assert!(sol.satisfiable, "range restriction must be SAT");
    let inst = sol.instance.expect("instance");
    let r = inst.find_relation_by_name("B.f").expect("B.f");
    assert_eq!(inst.tuples(r).unwrap().len(), 2);
}

// End to end: an unparenthesized multi-tuple pin now parses Alloy-style
// (previously regrouped and went UNSAT).
#[test]
fn unparenthesized_pin_solves() {
    let src = "sig A {}\none sig A0 extends A {}\none sig A1 extends A {}\nsig B { f: A }\none sig B0 extends B {}\none sig B1 extends B {}\nrun { f = B0->A1 + B1->A0 } for 3";
    let m = parse_module(src).expect("parse");
    let sol = run_command(&m, 0).expect("run");
    assert!(sol.satisfiable, "unparenthesized pin must be SAT");
    let inst = sol.instance.expect("instance");
    let r = inst.find_relation_by_name("B.f").expect("B.f");
    assert_eq!(inst.tuples(r).unwrap().len(), 2);
}
