//! Bounds simplifier (Java `Simplifier` port) tests.

use alloy_kodkod_rs::ast::{BinaryOp, ExprCompOp};
use alloy_kodkod_rs::bounds::Bounds;
use alloy_kodkod_rs::relation::RelationPool;
use alloy_kodkod_rs::simplify::{simplify_bounds, SimplifyOutcome};
use alloy_kodkod_rs::tuple::Tuple;
use alloy_kodkod_rs::tupleset::TupleSet;
use alloy_kodkod_rs::universe::Universe;
use alloy_kodkod_rs::AstArena;
use std::sync::Arc;

fn setup() -> (AstArena, Bounds, Arc<Universe>) {
    let u = Universe::new(vec!["a", "b", "c"]).unwrap();
    let pool = Arc::new(RelationPool::new());
    let bounds = Bounds::new(&u, &pool);
    let arena = AstArena::with_pool(Arc::clone(&pool));
    (arena, bounds, u)
}

fn set_of(u: &Arc<Universe>, arity: u32, flats: &[&str]) -> TupleSet {
    let mut s = TupleSet::new(u, arity).unwrap();
    for chunk in flats.chunks(arity as usize) {
        let t = Tuple::from_atoms(u, chunk).unwrap();
        s.insert(&t).unwrap();
    }
    s
}

#[test]
fn subset_fact_shrinks_upper() {
    let (mut arena, mut bounds, u) = setup();
    let r = arena.relation("r", 1);
    let lo = set_of(&u, 1, &[]);
    let up = set_of(&u, 1, &["a", "b", "c"]);
    bounds.bound(r, &lo, &up).unwrap();
    // fact: r in {a, b}
    let atoms = arena.expr_atoms(vec![0, 1]);
    let rel = arena.expr_relation(r);
    let f = arena.comparison(ExprCompOp::Subset, rel, atoms).unwrap();
    let out = simplify_bounds(&arena, &mut bounds, f).unwrap();
    assert_eq!(out, SimplifyOutcome::Changed);
    assert_eq!(bounds.upper_bound(r).unwrap().len(), 2);
    assert!(bounds.upper_bound(r).unwrap().contains_index(0));
    assert!(bounds.upper_bound(r).unwrap().contains_index(1));
}

#[test]
fn equality_fact_raises_lower_and_shrinks_upper() {
    let (mut arena, mut bounds, u) = setup();
    let r = arena.relation("r", 1);
    let s = arena.relation("s", 1);
    bounds
        .bound(r, &set_of(&u, 1, &[]), &set_of(&u, 1, &["a", "b", "c"]))
        .unwrap();
    bounds
        .bound(s, &set_of(&u, 1, &["a"]), &set_of(&u, 1, &["a"]))
        .unwrap();
    // fact: r = s  →  r becomes exactly {a}.
    let re = arena.expr_relation(r);
    let se = arena.expr_relation(s);
    let f = arena.comparison(ExprCompOp::Equals, re, se).unwrap();
    let out = simplify_bounds(&arena, &mut bounds, f).unwrap();
    assert_eq!(out, SimplifyOutcome::Changed);
    assert_eq!(bounds.lower_bound(r).unwrap().len(), 1);
    assert_eq!(bounds.upper_bound(r).unwrap().len(), 1);
}

#[test]
fn shrink_below_lower_is_unsat() {
    let (mut arena, mut bounds, u) = setup();
    let r = arena.relation("r", 1);
    bounds
        .bound(
            r,
            &set_of(&u, 1, &["a"]),
            &set_of(&u, 1, &["a", "b"]),
        )
        .unwrap();
    // fact: r in {b} contradicts lower {a}.
    let atoms = arena.expr_atoms(vec![1]);
    let rel = arena.expr_relation(r);
    let f = arena.comparison(ExprCompOp::Subset, rel, atoms).unwrap();
    let out = simplify_bounds(&arena, &mut bounds, f).unwrap();
    assert_eq!(out, SimplifyOutcome::Unsat);
}

#[test]
fn product_of_atoms_raises_exact_lower() {
    // fact: r = A0->B0 + A1->B1  →  r becomes exact (lower raised AND
    // upper shrunk), eliminating its primary variables entirely.
    let (mut arena, mut bounds, u) = setup();
    let r = arena.relation("r", 2);
    let full = set_of(
        &u,
        2,
        &["a", "a", "a", "b", "a", "c", "b", "a", "b", "b", "b", "c", "c", "a", "c", "b",
            "c", "c"],
    );
    bounds.bound(r, &set_of(&u, 2, &[]), &full).unwrap();
    let a0 = arena.expr_atoms(vec![0]);
    let b0 = arena.expr_atoms(vec![1]);
    let p0 = arena.binary_expr(BinaryOp::Product, a0, b0).unwrap();
    let a1 = arena.expr_atoms(vec![1]);
    let b1 = arena.expr_atoms(vec![2]);
    let p1 = arena.binary_expr(BinaryOp::Product, a1, b1).unwrap();
    let id = arena.compose_expr(BinaryOp::Union, &[p0, p1]).unwrap();
    let re = arena.expr_relation(r);
    let f = arena.comparison(ExprCompOp::Equals, re, id).unwrap();
    let out = simplify_bounds(&arena, &mut bounds, f).unwrap();
    assert_eq!(out, SimplifyOutcome::Changed);
    assert_eq!(bounds.lower_bound(r).unwrap().len(), 2);
    assert_eq!(bounds.upper_bound(r).unwrap().len(), 2);
}

#[test]
fn join_domain_is_skipped_soundly() {
    let (mut arena, mut bounds, u) = setup();
    let r = arena.relation("r", 2);
    let full = set_of(
        &u,
        2,
        &["a", "a", "a", "b", "a", "c", "b", "a", "b", "b", "b", "c", "c", "a", "c", "b",
            "c", "c"],
    );
    bounds.bound(r, &set_of(&u, 2, &[]), &full).unwrap();
    // fact: r in ~r: transpose has no approx → unchanged, still sound.
    let re = arena.expr_relation(r);
    let tr = arena
        .unary_expr(alloy_kodkod_rs::ast::UnaryExprOp::Transpose, re)
        .unwrap();
    let re2 = arena.expr_relation(r);
    let f = arena.comparison(ExprCompOp::Subset, re2, tr).unwrap();
    let out = simplify_bounds(&arena, &mut bounds, f).unwrap();
    assert_eq!(out, SimplifyOutcome::Unchanged);
    assert_eq!(bounds.upper_bound(r).unwrap().len(), 9);
}
