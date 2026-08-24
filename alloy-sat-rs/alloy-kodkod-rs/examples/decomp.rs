//! Iter-8 demo: `cargo run --release --example decomp`
//!
//! Shows both Pardinus-style decompositions implemented in `pardinus.rs`:
//!
//! * **static** — two INDEPENDENT problems conjoined (pigeonhole SAT part +
//!   triangle 2-coloring UNSAT part). The conjuncts are split into connected
//!   components over shared relations and solved independently; the UNSAT
//!   component proves the whole problem UNSAT without touching the other.
//! * **dynamic** — the token-ring temporal spec sliced into a partial
//!   stage (token totality) and a completion stage (movement + visit).
//!   Stage 1 models are explored with blocking clauses until one extends.

#[path = "../tests/puzzles.rs"]
mod puzzles;

use alloy_kodkod_rs::ast::*;
use alloy_kodkod_rs::bounds::Bounds;
use alloy_kodkod_rs::pardinus::{slice_formula, PardinusBounds};
use alloy_kodkod_rs::relation::RelationPool;
use alloy_kodkod_rs::tupleset::TupleSet;
use alloy_kodkod_rs::universe::Universe;
use alloy_kodkod_rs::{Solver, TemporalEval};
use std::sync::Arc;
use std::time::Instant;

fn demo_static(solver: &Solver) {
    println!("=== static component decomposition ===");
    let atoms: Vec<String> = (0..11).map(|i| format!("a{i}")).collect();
    let refs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
    let u = Universe::new(refs).unwrap();
    let pool = Arc::new(RelationPool::new());
    let mut bounds = Bounds::new(&u, &pool);
    let mut arena = AstArena::with_pool(Arc::clone(&pool));

    // part A: pigeonhole 2 pigeons / 3 holes over atoms {a0,a1} x {a3..a5}
    let pig = {
        let r = arena.relation("Pig", 1);
        let mut s = TupleSet::new(&u, 1).unwrap();
        s.insert_index(0);
        s.insert_index(1);
        bounds.bound_exactly(r, &s).unwrap();
        r
    };
    let _hole = {
        let r = arena.relation("Hole", 1);
        let mut s = TupleSet::new(&u, 1).unwrap();
        for i in 3..6 {
            s.insert_index(i as i64);
        }
        bounds.bound_exactly(r, &s).unwrap();
        r
    };
    let inr = {
        let r = arena.relation("IN", 2);
        let mut s = TupleSet::new(&u, 2).unwrap();
        for p in [0i64, 1] {
            for h in 3..6i64 {
                s.insert_index(p * u.size() as i64 + h);
            }
        }
        bounds.bound_upper(r, &s).unwrap();
        r
    };
    let pv = arena.variable("p");
    let pig_e = arena.expr_relation(pig);
    let d_p = arena.decl(pv, Multiplicity::One, pig_e).unwrap();
    let pve = arena.expr_variable(pv);
    let inr_e = arena.expr_relation(inr);
    let pin = arena.binary_expr(BinaryOp::Join, pve, inr_e).unwrap();
    let one_pin = arena.multiplicity_formula(Multiplicity::One, pin).unwrap();
    let ds_p = arena.add_decls(vec![d_p]);
    let total = arena.quantified(Quantifier::All, ds_p, one_pin);

    // part B: triangle needs >= 3 colors; give only 2 => UNSAT component
    let node = {
        let r = arena.relation("N", 1);
        let mut s = TupleSet::new(&u, 1).unwrap();
        for i in 6..9 {
            s.insert_index(i as i64);
        }
        bounds.bound_exactly(r, &s).unwrap();
        r
    };
    let color = {
        let r = arena.relation("C", 1);
        let mut s = TupleSet::new(&u, 1).unwrap();
        for i in 9..11 {
            s.insert_index(i as i64);
        }
        bounds.bound_exactly(r, &s).unwrap();
        r
    };
    let edge = {
        let r = arena.relation("Ed", 2);
        let mut s = TupleSet::new(&u, 2).unwrap();
        let sz = u.size() as i64;
        for &(a, b) in &[(6i64, 7i64), (7, 8), (6, 8)] {
            s.insert_index(a * sz + b);
        }
        bounds.bound_exactly(r, &s).unwrap();
        r
    };
    let assign = {
        let r = arena.relation("COL", 2);
        let mut s = TupleSet::new(&u, 2).unwrap();
        let sz = u.size() as i64;
        for v in 6..9i64 {
            for c in 9..11i64 {
                s.insert_index(v * sz + c);
            }
        }
        bounds.bound_upper(r, &s).unwrap();
        r
    };
    let vv = arena.variable("v");
    let node_e0 = arena.expr_relation(node);
    let d_v = arena.decl(vv, Multiplicity::Some, node_e0).unwrap();
    let vve = arena.expr_variable(vv);
    let assign_e0 = arena.expr_relation(assign);
    let vcol = arena.binary_expr(BinaryOp::Join, vve, assign_e0).unwrap();
    let some_body = arena
        .multiplicity_formula(Multiplicity::Some, vcol)
        .unwrap();
    let ds_v = arena.add_decls(vec![d_v]);
    let total_b = arena.quantified(Quantifier::All, ds_v, some_body);

    let m1 = arena.variable("m1");
    let m2 = arena.variable("m2");
    let cc = arena.variable("cc");
    let e1 = arena.expr_variable(m1);
    let e2 = arena.expr_variable(m2);
    let ec = arena.expr_variable(cc);
    let edge_e = arena.expr_relation(edge);
    let pair = arena.binary_expr(BinaryOp::Product, e1, e2).unwrap();
    let col_e = arena.expr_relation(assign);
    let in_edge = arena.comparison(ExprCompOp::Subset, pair, edge_e).unwrap();
    let c1 = arena.binary_expr(BinaryOp::Join, e1, col_e).unwrap();
    let c2j = arena.binary_expr(BinaryOp::Join, e2, col_e).unwrap();
    let has1 = arena.comparison(ExprCompOp::Subset, ec, c1).unwrap();
    let has2 = arena.comparison(ExprCompOp::Subset, ec, c2j).unwrap();
    let bad = arena.and(&[in_edge, has1, has2]);
    let node_e = arena.expr_relation(node);
    let color_e = arena.expr_relation(color);
    let d_m1 = arena.decl(m1, Multiplicity::One, node_e).unwrap();
    let d_m2 = arena.decl(m2, Multiplicity::One, node_e).unwrap();
    let d_cc = arena.decl(cc, Multiplicity::One, color_e).unwrap();
    let ds_d = arena.add_decls(vec![d_m1, d_m2, d_cc]);
    let no_bad = arena.not(bad);
    let diff = arena.quantified(Quantifier::All, ds_d, no_bad);
    let tri_unsat = arena.and(&[total_b, diff]);

    let full = arena.and(&[total, tri_unsat]);
    let t0 = Instant::now();
    let sol = solver.solve_decomposed(&mut arena, full, &bounds).unwrap();
    println!(
        "decomposed verdict: {} ({:?})",
        if sol.satisfiable { "SAT" } else { "UNSAT" },
        t0.elapsed()
    );
    println!("(the UNSAT coloring component decides the whole problem)");
}

fn demo_dynamic(solver: &Solver) {
    println!("\n=== dynamic two-stage decomposition (token ring) ===");
    let n = 4usize;
    let steps = 4usize;
    let atoms: Vec<String> = (0..n).map(|i| format!("p{i}")).collect();
    let refs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
    let u = Universe::new(refs).unwrap();
    let pool = Arc::new(RelationPool::new());
    let mut bounds = Bounds::new(&u, &pool);
    let mut arena = AstArena::with_pool(Arc::clone(&pool));

    let next = arena.relation("next", 2);
    let p0r = arena.relation("P0", 1);
    let tok = {
        let r = arena.relation("tok", 1);
        arena.set_variable(r, true);
        r
    };
    {
        let mut s = TupleSet::new(&u, 2).unwrap();
        for i in 0..n {
            s.insert_index((i * n + (i + 1) % n) as i64);
        }
        bounds.bound_exactly(next, &s).unwrap();
        let mut sp = TupleSet::new(&u, 1).unwrap();
        sp.insert_index(0);
        bounds.bound_exactly(p0r, &sp).unwrap();
        let mut s = TupleSet::new(&u, 1).unwrap();
        for i in 0..n {
            s.insert_index(i as i64);
        }
        bounds.bound_upper(tok, &s).unwrap();
    }

    let tok_e = arena.expr_relation(tok);
    let one = arena
        .multiplicity_formula(Multiplicity::One, tok_e)
        .unwrap();
    let always_one = arena.temporal_unary(TemporalFormulaOp::Always, one);
    let tok_p = arena.prime(tok_e);
    let ne = arena.expr_relation(next);
    let te2 = arena.expr_relation(tok);
    let succ = arena.binary_expr(BinaryOp::Join, ne, te2).unwrap();
    let mv = arena.comparison(ExprCompOp::Subset, tok_p, succ).unwrap();
    let always_moves = arena.temporal_unary(TemporalFormulaOp::Always, mv);
    let pe = arena.expr_relation(p0r);
    let hit = arena
        .binary_expr(BinaryOp::Intersection, tok_e, pe)
        .unwrap();
    let sh = arena.multiplicity_formula(Multiplicity::Some, hit).unwrap();
    let eventually_p0 = arena.temporal_unary(TemporalFormulaOp::Eventually, sh);
    let formula = arena.and(&[always_one, always_moves, eventually_p0]);

    // slice preview: with tok partial, every conjunct touches tok...
    let pb = PardinusBounds::new(bounds.clone()).with_partial(tok);
    let (_f1, _f2) = slice_formula(&mut arena, formula, pb.partials()).unwrap();

    let t0 = Instant::now();
    match solver.solve_dynamic(&mut arena, formula, &pb, steps) {
        Ok(sol) if sol.satisfiable => {
            println!("dynamic verdict: SAT ({:?})", t0.elapsed());
            if let Some(ti) = &sol.temporal {
                println!("loop state: {}", ti.loop_state());
                for (i, st) in ti.states().iter().enumerate() {
                    if let Some(ts) = st.tuples(tok) {
                        let who: Vec<String> =
                            ts.index_view().iter().map(|x| format!("p{x}")).collect();
                        println!("  state{i}: tok = {{{}}}", who.join(", "));
                    }
                }
                let checker = TemporalEval::new(ti);
                println!(
                    "verify: {}",
                    if checker.holds(&arena, formula).unwrap_or(false) {
                        "lasso satisfies spec"
                    } else {
                        "MISMATCH"
                    }
                );
            }
        }
        other => println!("dynamic verdict: {:?}", other.map(|_| ()).err()),
    }
}

fn main() {
    let solver = Solver::new();
    demo_static(&solver);
    demo_dynamic(&solver);
}
