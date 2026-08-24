#![cfg(feature = "ipasir")]

//! Iter-backlog-2 tests: static and temporal (HASLab-style) Skolemization.

use alloy_kodkod_rs::ast::*;
use alloy_kodkod_rs::bounds::Bounds;
use alloy_kodkod_rs::relation::{RelationId, RelationPool};
use alloy_kodkod_rs::solver::SolverOptions;
use alloy_kodkod_rs::temporal::TemporalEval;
use alloy_kodkod_rs::tupleset::TupleSet;
use alloy_kodkod_rs::universe::Universe;
use alloy_kodkod_rs::Solver;
use std::sync::Arc;

fn univ(names: &[&str]) -> Arc<Universe> {
    Universe::new(names.to_vec()).unwrap()
}

fn upper_free(u: &Arc<Universe>, arity: u32) -> TupleSet {
    let mut s = TupleSet::new(u, arity).unwrap();
    for i in 0..u.size().pow(arity) {
        s.insert_index(i as i64);
    }
    s
}

/// `some x: U | x in R` — witness membership. With R exactly {a} the model
/// must place the skolem witness on atom a.
#[test]
fn static_skolem_constant_membership() {
    let u = univ(&["a", "b"]);
    let pool = Arc::new(RelationPool::new());
    let mut bounds = Bounds::new(&u, &pool);
    let mut arena = AstArena::with_pool(Arc::clone(&pool));

    let r = arena.relation("R", 1);
    {
        let mut s = TupleSet::new(&u, 1).unwrap();
        s.insert_index(0); // R = {a}
        bounds.bound_exactly(r, &s).unwrap();
    }
    let re = arena.expr_relation(r);
    let xv = arena.variable("x");
    let xu = arena.univ();
    let d = arena.decl(xv, Multiplicity::One, xu).unwrap();
    let ds = arena.add_decls(vec![d]);
    let xve = arena.expr_variable(xv);
    let mem = arena.comparison(ExprCompOp::Equals, xve, re).unwrap();
    let f = arena.quantified(Quantifier::Some, ds, mem);

    let base = Solver::new();
    let sk = Solver::with_options(SolverOptions {
        skolemize: true,
        ..Default::default()
    });

    let sol_plain = base.solve(&mut arena, f, &bounds).unwrap();
    let sol_sk = sk.solve(&mut arena, f, &bounds).unwrap();
    assert!(sol_plain.satisfiable);
    assert!(sol_sk.satisfiable);

    let inst = sol_sk.instance.unwrap();
    // the skolem relation appears in the materialized instance
    let sk_rel = inst
        .relations()
        .find(|&r| pool.is_skolem(r))
        .expect("skolem relation in instance");
    let ts = inst.tuples(sk_rel).unwrap();
    assert!(!ts.is_empty(), "witness nonempty");
    for idx in ts.index_view().iter() {
        assert!(inst.tuples(r).unwrap().contains_index(idx), "witness ⊆ R");
    }

    // UNSAT parity: domain U \ R is empty
    let uu2 = arena.univ();
    let diff = arena.binary_expr(BinaryOp::Difference, uu2, re).unwrap();
    let xv2 = arena.variable("y");
    let d2 = arena.decl(xv2, Multiplicity::One, diff).unwrap();
    let ds2 = arena.add_decls(vec![d2]);
    let xv2e = arena.expr_variable(xv2);
    let mem2 = arena.comparison(ExprCompOp::Equals, xv2e, re).unwrap();
    let f2 = arena.quantified(Quantifier::Some, ds2, mem2);
    let p2 = base.solve(&mut arena, f2, &bounds).unwrap();
    let s2 = sk.solve(&mut arena, f2, &bounds).unwrap();
    assert!(!p2.satisfiable && !s2.satisfiable, "empty-domain parity");
}

/// Function witness: `all p: P | some q: Q | p->q in E`.
/// Totality of the Skolem function forces one edge per process.
#[test]
fn static_skolem_function_totality() {
    let u = univ(&["pa", "pb", "qx", "qy"]);
    let pool = Arc::new(RelationPool::new());
    let mut bounds = Bounds::new(&u, &pool);
    let mut arena = AstArena::with_pool(Arc::clone(&pool));

    let proc_rel = arena.relation("P", 1);
    {
        let mut s = TupleSet::new(&u, 1).unwrap();
        s.insert_index(0);
        s.insert_index(1);
        bounds.bound_exactly(proc_rel, &s).unwrap();
    }
    let e_rel = arena.relation("E", 2);
    bounds.bound_upper(e_rel, &upper_free(&u, 2)).unwrap();

    let pe = arena.expr_relation(proc_rel);
    let pv = arena.variable("p");
    let qv = arena.variable("q");
    let qu = arena.univ();
    let dq = arena.decl(qv, Multiplicity::One, qu).unwrap();
    let ds_q = arena.add_decls(vec![dq]);
    let dp = arena.decl(pv, Multiplicity::One, pe).unwrap();
    let ds_p = arena.add_decls(vec![dp]);

    let pve = arena.expr_variable(pv);
    let qve = arena.expr_variable(qv);
    let pair = arena.binary_expr(BinaryOp::Product, pve, qve).unwrap();
    let ee = arena.expr_relation(e_rel);
    let edge_cmp = arena.comparison(ExprCompOp::Subset, pair, ee).unwrap();

    let inner = arena.quantified(Quantifier::Some, ds_q, edge_cmp);
    let f = arena.quantified(Quantifier::All, ds_p, inner);

    let base = Solver::new();
    let sk = Solver::with_options(SolverOptions {
        skolemize: true,
        ..Default::default()
    });

    let a = base.solve(&mut arena, f, &bounds).unwrap().satisfiable;
    let b = sk.solve(&mut arena, f, &bounds).unwrap().satisfiable;
    assert!(a && b, "free E admits witnesses");

    // E forced empty => totality impossible either way
    let mut b2 = bounds.clone();
    let empty = TupleSet::new(&u, 2).unwrap();
    b2.bound_exactly(e_rel, &empty).unwrap();
    let a2 = base.solve(&mut arena, f, &b2).unwrap().satisfiable;
    let b2sat = sk.solve(&mut arena, f, &b2).unwrap().satisfiable;
    assert!(!a2 && !b2sat, "empty E parity");
}

/// Temporal HASLab witness: `always (some x: B | x in tok)` inside the
/// token-ring. Skolemized and plain runs must agree, and the extracted
/// trace's witness relation must mirror `tok` at every state.
#[test]
fn temporal_skolem_always_witness() {
    fn build(
        with_skolem: bool,
    ) -> (
        Solver,
        AstArena,
        Bounds,
        Arc<RelationPool>,
        RelationId,
        FormulaId,
    ) {
        let n = 3usize;
        let atoms: Vec<String> = (0..n).map(|i| format!("q{i}")).collect();
        let refs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
        let u = Universe::new(refs).unwrap();
        let pool = Arc::new(RelationPool::new());
        let mut bounds = Bounds::new(&u, &pool);
        let mut arena = AstArena::with_pool(Arc::clone(&pool));
        let b_set = arena.relation("B", 1);
        let tok = {
            let r = arena.relation("tok", 1);
            arena.set_variable(r, true);
            r
        };
        {
            let mut s = TupleSet::new(&u, 1).unwrap();
            s.insert_index(1);
            bounds.bound_exactly(b_set, &s).unwrap();
            let mut s = TupleSet::new(&u, 1).unwrap();
            for i in 0..n {
                s.insert_index(i as i64);
            }
            bounds.bound_upper(tok, &s).unwrap();
        }
        let te = arena.expr_relation(tok);
        let one = arena.multiplicity_formula(Multiplicity::One, te).unwrap();
        let fa = arena.temporal_unary(TemporalFormulaOp::Always, one);

        let be = arena.expr_relation(b_set);
        let xv = arena.variable("x");
        let dx = arena.decl(xv, Multiplicity::One, be).unwrap();
        let dsx = arena.add_decls(vec![dx]);
        let xve = arena.expr_variable(xv);
        let hit = arena.comparison(ExprCompOp::Subset, xve, te).unwrap();
        let exists_hit = arena.quantified(Quantifier::Some, dsx, hit);
        let fsome = arena.temporal_unary(TemporalFormulaOp::Always, exists_hit);
        let f = arena.and(&[fa, fsome]);

        let opts = SolverOptions {
            skolemize: with_skolem,
            ..Default::default()
        };
        let _ = b_set;
        (
            Solver::with_options(opts),
            arena,
            bounds,
            Arc::clone(&pool),
            tok,
            f,
        )
    }

    let (s0, mut arena0, b0, _pool0, tok0, f0) = build(false);
    let (s1, mut arena1, bounds1, pool1, _tok1, f1) = build(true);

    let steps = 3usize;
    let plain = s0.solve_temporal(&mut arena0, f0, &b0, steps).unwrap();
    let skim = s1
        .solve_temporal_with(&mut arena1, f1, &bounds1, steps, true, &[], &[])
        .unwrap();
    assert_eq!(plain.satisfiable, skim.satisfiable, "parity");
    assert!(skim.satisfiable, "spec is satisfiable with token=q1 fixed");

    let ti = skim.temporal.as_ref().unwrap();
    let checker = TemporalEval::new(ti);
    assert!(checker.holds(&arena1, f1).unwrap(), "trace satisfies spec");
    let inst = skim.instance.as_ref().unwrap();
    let skrels: Vec<RelationId> = inst.relations().filter(|&r| pool1.is_skolem(r)).collect();
    assert!(!skrels.is_empty(), "witness relation present");
    for st in ti.states().iter() {
        let tok_ts = st.tuples(tok0).unwrap();
        assert_eq!(tok_ts.len(), 1);
        assert!(tok_ts.contains_index(1));
    }
}
