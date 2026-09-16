//! Regression: quantified formulas must key memoization on domain
//! free variables too.
//!
//! `all x: D | (all y: x.R | ...)` evaluated under different `x` must
//! not share results: dropping the domain's free vars (`x`) from the
//! key collapses distinct instantiations (unsound sharing that once
//! slipped through temporal + course models).

use alloy_kodkod_rs::ast::{BinaryOp, ExprCompOp, Multiplicity, Quantifier};
use alloy_kodkod_rs::bounds::Bounds;
use alloy_kodkod_rs::fol::FolTranslator;
use alloy_kodkod_rs::relation::RelationPool;
use alloy_kodkod_rs::tuple::Tuple;
use alloy_kodkod_rs::tupleset::TupleSet;
use alloy_kodkod_rs::universe::Universe;
use alloy_kodkod_rs::{AstArena, BoolCtx};
use std::sync::Arc;

#[test]
fn dynamic_domain_distinguishes_outer_bindings() {
    // Universe {a, b}; R = {(a,a),(b,b)} exact.
    // F = all x in {a,b} | (all y in x.R | y = a).
    // x=a: y in {a}: true.  x=b: y in {b}: b=a false.  Overall: UNSAT.
    // A memo keyed without the domain free var (`x`) reuses x=a's
    // `true` for x=b and wrongly reports SAT.
    let u = Universe::new(vec!["a", "b"]).unwrap();
    let pool = Arc::new(RelationPool::new());
    let mut bounds = Bounds::new(&u, &pool);
    let mut arena = AstArena::with_pool(Arc::clone(&pool));
    let r = arena.relation("R", 2);
    let mut ts = TupleSet::new(&u, 2).unwrap();
    for chunk in [["a", "a"], ["b", "b"]] {
        ts.insert(&Tuple::from_atoms(&u, &chunk).unwrap()).unwrap();
    }
    bounds.bound_exactly(r, &ts).unwrap();

    let xv = arena.variable("x");
    let yv = arena.variable("y");
    let atoms = arena.expr_atoms(vec![0, 1]);
    let dx = arena
        .decl(xv, Multiplicity::One, atoms)
        .expect("unary var over unary domain");
    let x_e = arena.expr_variable(xv);
    let r_e = arena.expr_relation(r);
    let dom_y = arena.binary_expr(BinaryOp::Join, x_e, r_e).unwrap();
    let dy = arena
        .decl(yv, Multiplicity::One, dom_y)
        .expect("unary var over unary join domain");
    let y_e = arena.expr_variable(yv);
    let a_e = arena.expr_atoms(vec![0]);
    let eq = arena
        .comparison(ExprCompOp::Equals, y_e, a_e)
        .unwrap();
    let inner = {
        let ds = arena.add_decls(vec![dy]);
        arena.quantified(Quantifier::All, ds, eq)
    };
    let outer = {
        let ds = arena.add_decls(vec![dx]);
        arena.quantified(Quantifier::All, ds, inner)
    };

    let mut tr = FolTranslator::new(BoolCtx::new(), &bounds);
    let root = tr.formula_ref(&arena, outer, &[]).unwrap();
    assert!(
        root.is_const() && !root.const_value(),
        "dynamic-domain quantifier must evaluate to false, got {root:?}"
    );
}
