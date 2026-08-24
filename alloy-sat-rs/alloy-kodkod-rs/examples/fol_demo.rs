#![cfg(feature = "ipasir")]

use alloy_kodkod_rs::ast::*;
use alloy_kodkod_rs::bounds::Bounds;
use alloy_kodkod_rs::cnf::translate_into_solver;
use alloy_kodkod_rs::fol::FolTranslator;
use alloy_kodkod_rs::ipasir_bridge::IpasirSolver;
use alloy_kodkod_rs::relation::{RelationId, RelationPool};
use alloy_kodkod_rs::sat::SatSolver;
use alloy_kodkod_rs::tuple::Tuple;
use alloy_kodkod_rs::tupleset::TupleSet;
use alloy_kodkod_rs::universe::Universe;
use std::sync::Arc;

fn main() {
    let u = Universe::new(["N0", "N1", "N2", "N3"]).unwrap();
    let pool = Arc::new(RelationPool::new());
    let mut arena = AstArena::with_pool(Arc::clone(&pool));
    let mut bounds = Bounds::new(&u, &pool);

    let node = arena.relation("Node", 1);
    let next = arena.relation("next", 2);

    fn exact(u: &Arc<Universe>, arity: u32, flat: &[&str]) -> TupleSet {
        let mut s = TupleSet::new(u, arity).unwrap();
        for chunk in flat.chunks(arity as usize) {
            let t = Tuple::from_atoms(u, chunk).unwrap();
            s.insert(&t).unwrap();
        }
        s
    }

    bounds
        .bound_exactly(node, &exact(&u, 1, &["N0", "N1", "N2", "N3"]))
        .unwrap();
    // next: cycle N0->N1->N2->N3->N0 forced exactly
    bounds
        .bound_exactly(
            next,
            &exact(&u, 2, &["N0", "N1", "N1", "N2", "N2", "N3", "N3", "N0"]),
        )
        .unwrap();

    let empty_rel: RelationId = {
        let e = arena.relation("E", 2);
        bounds.bound_exactly(e, &exact(&u, 2, &[])).unwrap();
        e
    };
    let mut translator = FolTranslator::new(alloy_kodkod_rs::BoolCtx::new(), &bounds);
    let en = arena.expr_relation(node);
    let x = arena.variable("x");
    let dx = arena.decl(x, Multiplicity::One, en).unwrap();
    let ds = arena.add_decls(vec![dx]);
    let exn = arena.expr_variable(x);
    let enext = arena.expr_relation(next);
    let j = arena.binary_expr(BinaryOp::Join, exn, enext).unwrap();
    let body = arena.multiplicity_formula(Multiplicity::One, j).unwrap();
    let all_func = arena.quantified(Quantifier::All, ds, body);
    // every node has exactly one successor AND the graph is a single cycle:
    // additionally require no self loops
    let no_self = {
        let iden = arena.iden();
        let enext2 = arena.expr_relation(next);
        let inter = arena
            .binary_expr(BinaryOp::Intersection, enext2, iden)
            .unwrap();
        let eempty = arena.expr_relation(empty_rel);
        arena.comparison(ExprCompOp::Equals, inter, eempty).unwrap()
    };
    let f = arena.and(&[all_func, no_self]);

    let root = translator.formula_ref(&arena, f, &[]).unwrap();
    let max_primary = translator.ctx.num_slots();
    let ctx = translator.ctx.clone();

    println!("circuit slots allocated: {}", max_primary);

    let mut solver = IpasirSolver::new().unwrap();
    ctx.with_factory(|factory| translate_into_solver(&mut solver, factory, root, max_primary))
        .unwrap();
    println!("backend: {}", solver.backend_name());
    let sat = SatSolver::solve(&mut solver);
    println!(
        "forced 4-cycle with functional next + no self loops => {}",
        if sat { "SAT" } else { "UNSAT" }
    );

    // now break the cycle requirement: allow arbitrary functional next
    let mut bounds2 = Bounds::new(&u, &pool);
    bounds2
        .bound_exactly(node, &exact(&u, 1, &["N0", "N1", "N2", "N3"]))
        .unwrap();
    let upper = {
        let mut s = TupleSet::new(&u, 2).unwrap();
        for i in 0..4usize {
            for jj in 0..4usize {
                if i != jj {
                    let _ = s.insert_index((i * 4 + jj) as i64);
                }
            }
        }
        s
    };
    bounds2.bound_upper(next, &upper).unwrap();
    let mut t2 = FolTranslator::new(alloy_kodkod_rs::BoolCtx::new(), &bounds2);
    let root2 = t2.formula_ref(&arena, all_func, &[]).unwrap();
    let mp2 = t2.ctx.num_slots();
    let ctx2 = t2.ctx.clone();
    let mut s2 = IpasirSolver::new().unwrap();
    ctx2.with_factory(|factory| translate_into_solver(&mut s2, factory, root2, mp2))
        .unwrap();
    println!(
        "functional-only (acyclic allowed) => {}",
        if SatSolver::solve(&mut s2) {
            "SAT"
        } else {
            "UNSAT"
        }
    );

    // contradictory variant: functional-one over all nodes, but next forced empty
    let none_rel: RelationId = {
        let e = arena.relation("NONE", 2);
        bounds.bound_exactly(e, &exact(&u, 2, &[])).unwrap();
        e
    };
    let mut t3 = FolTranslator::new(alloy_kodkod_rs::BoolCtx::new(), &bounds);
    let enone = arena.expr_relation(none_rel);
    let body3 = arena
        .multiplicity_formula(Multiplicity::One, enone)
        .unwrap();
    let f3 = arena.and(&[all_func, body3]);
    let root3 = t3.formula_ref(&arena, f3, &[]).unwrap();
    let mp3 = t3.ctx.num_slots();
    let ctx3 = t3.ctx.clone();
    let mut s3 = IpasirSolver::new().unwrap();
    ctx3.with_factory(|factory| translate_into_solver(&mut s3, factory, root3, mp3))
        .unwrap();
    println!(
        "functional-one but next==empty     => {}",
        if SatSolver::solve(&mut s3) {
            "SAT"
        } else {
            "UNSAT"
        }
    );
}
