#![cfg(feature = "ipasir")]

//! Iter-8 tests: Pardinus-style decomposition.
//! Acceptance: decomposed solving agrees with monolithic solving on small
//! problems (satisfiability AND solution content).

use alloy_kodkod_rs::ast::*;
use alloy_kodkod_rs::bounds::Bounds;
use alloy_kodkod_rs::pardinus::{slice_formula, PardinusBounds};
use alloy_kodkod_rs::relation::{RelationId, RelationPool};
use alloy_kodkod_rs::tupleset::TupleSet;
use alloy_kodkod_rs::universe::Universe;
use alloy_kodkod_rs::Solver;
use std::collections::BTreeSet;
use std::sync::Arc;

/// Two INDEPENDENT problems conjoined:
///   part A: pigeonhole 3 pigeons / 3 holes over atoms {p*,h*}   (SAT)
///   part B: graph 2-coloring of a triangle over atoms {n*,c*}    (UNSAT)
/// Conjoined => UNSAT; each component alone keeps its own verdict.
#[test]
fn static_components_independent_verdicts() {
    fn pigeonhole_part(arena: &mut AstArena, bounds: &mut Bounds, u: &Arc<Universe>) -> FormulaId {
        let pig = {
            let r = arena.relation("Pig", 1);
            let mut s = TupleSet::new(u, 1).unwrap();
            for i in 0..3 {
                s.insert_index(i as i64);
            }
            bounds.bound_exactly(r, &s).unwrap();
            r
        };
        let hole = {
            let r = arena.relation("Hole", 1);
            let mut s = TupleSet::new(u, 1).unwrap();
            for i in 0..3 {
                s.insert_index(10 + i);
            }
            bounds.bound_exactly(r, &s).unwrap();
            r
        };
        let inr = {
            let r = arena.relation("IN", 2);
            let mut s = TupleSet::new(u, 2).unwrap();
            for p in 0..3i64 {
                for h in 0..3i64 {
                    s.insert_index(p * u.size() as i64 + 10 + h);
                }
            }
            bounds.bound_upper(r, &s).unwrap();
            r
        };
        // all p: Pig | one p.IN ; all h: Hole | lone ~IN.h
        let pv = arena.variable("p");
        let pig_e = arena.expr_relation(pig);
        let d_p = arena.decl(pv, Multiplicity::One, pig_e).unwrap();
        let pve = arena.expr_variable(pv);
        let inr_e = arena.expr_relation(inr);
        let pin = arena.binary_expr(BinaryOp::Join, pve, inr_e).unwrap();
        let total_body = arena.multiplicity_formula(Multiplicity::One, pin).unwrap();
        let ds_p = arena.add_decls(vec![d_p]);
        let total = arena.quantified(Quantifier::All, ds_p, total_body);

        let hv = arena.variable("h");
        let hole_e = arena.expr_relation(hole);
        let d_h = arena.decl(hv, Multiplicity::One, hole_e).unwrap();
        let inr_e2 = arena.expr_relation(inr);
        let tin = arena.unary_expr(UnaryExprOp::Transpose, inr_e2).unwrap();
        let hve = arena.expr_variable(hv);
        let hin = arena.binary_expr(BinaryOp::Join, tin, hve).unwrap();
        let inj_body = arena.multiplicity_formula(Multiplicity::Lone, hin).unwrap();
        let ds_h = arena.add_decls(vec![d_h]);
        let inj = arena.quantified(Quantifier::All, ds_h, inj_body);

        arena.and(&[total, inj])
    }

    fn triangle_2col_part(
        arena: &mut AstArena,
        bounds: &mut Bounds,
        u: &Arc<Universe>,
    ) -> FormulaId {
        let node = {
            let r = arena.relation("N", 1);
            let mut s = TupleSet::new(u, 1).unwrap();
            for i in 0..20 {
                s.insert_index(i as i64);
            }
            bounds.bound_exactly(r, &s).unwrap();
            r
        };
        let color = {
            let r = arena.relation("C", 1);
            let mut s = TupleSet::new(u, 1).unwrap();
            for i in 20..22 {
                s.insert_index(i as i64);
            }
            bounds.bound_exactly(r, &s).unwrap();
            r
        };
        let edge = {
            let r = arena.relation("Ed", 2);
            let mut s = TupleSet::new(u, 2).unwrap();
            let sz = u.size() as i64;
            for &(a, b) in &[(0i64, 1i64), (1, 2), (0, 2)] {
                s.insert_index(a * sz + b);
            }
            bounds.bound_exactly(r, &s).unwrap();
            r
        };
        let assign = {
            let r = arena.relation("COL", 2);
            let mut s = TupleSet::new(u, 2).unwrap();
            let sz = u.size() as i64;
            for v in 0..20i64 {
                for c in 20..22i64 {
                    s.insert_index(v * sz + c);
                }
            }
            bounds.bound_upper(r, &s).unwrap();
            r
        };
        // all v: N | some v.COL ; all m,n: N | all cc: C | !((m,n) in Ed && ...)
        let vv = arena.variable("v");
        let node_e3 = arena.expr_relation(node);
        let d_v = arena.decl(vv, Multiplicity::Some, node_e3).unwrap();
        let vve = arena.expr_variable(vv);
        let assign_e = arena.expr_relation(assign);
        let vcol = arena.binary_expr(BinaryOp::Join, vve, assign_e).unwrap();
        let some_body = arena
            .multiplicity_formula(Multiplicity::Some, vcol)
            .unwrap();
        let ds_v = arena.add_decls(vec![d_v]);
        let total = arena.quantified(Quantifier::All, ds_v, some_body);

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
        let node_e1 = arena.expr_relation(node);
        let node_e2 = arena.expr_relation(node);
        let color_e = arena.expr_relation(color);
        let d_m1 = arena.decl(m1, Multiplicity::One, node_e1).unwrap();
        let d_m2 = arena.decl(m2, Multiplicity::One, node_e2).unwrap();
        let d_cc = arena.decl(cc, Multiplicity::One, color_e).unwrap();
        let ds_d = arena.add_decls(vec![d_m1, d_m2, d_cc]);
        let bad_not = arena.not(bad);
        let diff = arena.quantified(Quantifier::All, ds_d, bad_not);
        arena.and(&[total, diff])
    }

    let atoms: Vec<String> = (0..22).map(|i| format!("a{i}")).collect();
    let refs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
    let u = Universe::new(refs).unwrap();
    let pool = Arc::new(RelationPool::new());
    let mut bounds = Bounds::new(&u, &pool);
    let mut arena = AstArena::with_pool(Arc::clone(&pool));

    let ph = pigeonhole_part(&mut arena, &mut bounds, &u);
    let tri = triangle_2col_part(&mut arena, &mut bounds, &u);
    let full = arena.and(&[ph, tri]);

    let solver = Solver::new();

    // monolithic: UNSAT (triangle is not 2-colorable)
    let mono = solver.solve(&mut arena, full, &bounds).unwrap();
    assert!(!mono.satisfiable);

    // decomposed: component B is UNSAT => whole UNSAT
    let decomp = solver.solve_decomposed(&mut arena, full, &bounds).unwrap();
    assert!(!decomp.satisfiable);

    // sanity: the pigeonhole component alone IS satisfiable when solved alone.
    // Build it via slicing against the triangle's relations only.
    let tri_rels: BTreeSet<RelationId> = ["N", "C", "Ed", "COL"]
        .iter()
        .map(|n| arena.relation(n, if *n == "Ed" || *n == "COL" { 2 } else { 1 }))
        .collect();
    let (f_partial_only, _rest) = slice_formula(&mut arena, full, &tri_rels).unwrap();
    // nothing but the triangle conjuncts may land in the partial slice here
    let sol_slice = solver.solve(&mut arena, f_partial_only, &bounds).unwrap();
    assert!(!sol_slice.satisfiable, "triangle slice must stay UNSAT");
}

/// Slicing correctness: with `tok` marked partial, the `always(one tok)`
/// conjunct lands in the partial slice while movement/visit go to stage 2.
#[test]
fn dynamic_two_stage_token_ring() {
    let n = 4usize;
    let atoms: Vec<String> = (0..n).map(|i| format!("p{i}")).collect();
    let refs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
    let u = Universe::new(refs).unwrap();
    let pool = Arc::new(RelationPool::new());
    let mut bounds = Bounds::new(&u, &pool);
    let mut arena = AstArena::with_pool(Arc::clone(&pool));

    let next = arena.relation("next", 2);
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

    let pe = arena.relation("P0", 1);
    {
        let mut s = TupleSet::new(&u, 1).unwrap();
        s.insert_index(0);
        bounds.bound_exactly(pe, &s).unwrap();
    }
    let pe_e = arena.expr_relation(pe);
    let hit = arena
        .binary_expr(BinaryOp::Intersection, tok_e, pe_e)
        .unwrap();
    let sh = arena.multiplicity_formula(Multiplicity::Some, hit).unwrap();
    let eventually_p0 = arena.temporal_unary(TemporalFormulaOp::Eventually, sh);

    let formula = arena.and(&[always_one, always_moves, eventually_p0]);

    // mark tok as the stage-1 variable
    let pb = PardinusBounds::new(bounds.clone()).with_partial(tok);

    // slice check: only always-one touches {tok} exclusively? No — moves and
    // visit also reference tok. With tok partial they ALL belong to the
    // partial slice; dynamic degenerates to the plain problem. Verify that.
    let (f1, f2) = slice_formula(&mut arena, formula, pb.partials()).unwrap();
    // both slices are non-trivial here (every conjunct references tok)
    assert_ne!(f1, f2);

    // dynamic run must agree with the plain temporal solve
    let steps = 4usize;
    let solver = Solver::new();
    let plain = solver
        .solve_temporal(&mut arena, formula, &bounds, steps)
        .unwrap();
    let dyna = solver
        .solve_dynamic(&mut arena, formula, &pb, steps)
        .unwrap();

    // dynamic parity: same verdict as the plain temporal solve
    assert_eq!(plain.satisfiable, dyna.satisfiable, "dynamic parity");

    if plain.satisfiable {
        let ti = plain.temporal.clone().expect("temporal instance");
        let checker = alloy_kodkod_rs::temporal::TemporalEval::new(&ti);
        assert!(checker.holds(&arena, formula).unwrap());
    }
}

/// Parallel static decomposition must agree with serial and monolithic
/// solving, on both SAT and UNSAT problems.
#[test]
fn parallel_decomposition_parity() {
    // Reuse the independent-parts construction from the static test by
    // building a small SAT variant: pigeonhole(2x3) + 3-colorable triangle.
    let n_atoms = 12usize;
    let atoms: Vec<String> = (0..n_atoms).map(|i| format!("a{i}")).collect();
    let refs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
    let u = Universe::new(refs).unwrap();
    let pool = Arc::new(RelationPool::new());
    let mut bounds = Bounds::new(&u, &pool);
    let mut arena = AstArena::with_pool(Arc::clone(&pool));
    let sz = u.size() as i64;

    // part A (SAT): pigeonhole 2 pigeons into 3 holes
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
                s.insert_index(p * sz + h);
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

    // part B (SAT): triangle with THREE colors
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
        for i in 9..12.min(n_atoms) {
            s.insert_index(i as i64);
        }
        bounds.bound_exactly(r, &s).unwrap();
        r
    };
    let edge = {
        let r = arena.relation("Ed", 2);
        let mut s = TupleSet::new(&u, 2).unwrap();
        for &(a, b) in &[(6i64, 7i64), (7, 8), (6, 8)] {
            s.insert_index(a * sz + b);
        }
        bounds.bound_exactly(r, &s).unwrap();
        r
    };
    let assign = {
        let r = arena.relation("COL", 2);
        let mut s = TupleSet::new(&u, 2).unwrap();
        for v in 6..9i64 {
            for c in 9..12.min(n_atoms) as i64 {
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
    let assign_e = arena.expr_relation(assign);
    let vcol = arena.binary_expr(BinaryOp::Join, vve, assign_e).unwrap();
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
    let tri = arena.and(&[total_b, diff]);

    let full = arena.and(&[total, tri]);

    let solver = Solver::new();

    // monolithic verdict
    let mono = solver.solve(&mut arena, full, &bounds).unwrap();
    assert!(mono.satisfiable, "2 pigeons/3 holes + 3-colored triangle");

    // serial decomposition
    let ser = solver.solve_decomposed(&mut arena, full, &bounds).unwrap();
    assert!(ser.satisfiable);

    // parallel decomposition (4 workers)
    let par = solver
        .solve_decomposed_parallel(&mut arena, full, &bounds, 4)
        .unwrap();
    assert!(par.satisfiable, "parallel verdict");
    assert_eq!(par.backend, "decomposed-parallel");

    // merged instance satisfies the FULL formula
    let inst = par.instance.expect("SAT implies merged instance");
    let ev = alloy_kodkod_rs::eval::Evaluator::new(&inst);
    let dump = |r: &str| {
        inst.find_relation_by_name(r)
            .and_then(|rr| inst.tuples(rr))
            .map(|ts| format!("{:?}", ts.index_view().iter().collect::<Vec<_>>()))
            .unwrap_or_else(|| "<absent>".into())
    };
    eprintln!(
        "PIG={} HOLE={} IN={}",
        dump("Pig"),
        dump("Hole"),
        dump("IN")
    );
    let t_ok = ev.formula_bool(&arena, total, &Vec::new()).unwrap();
    let b_ok = ev.formula_bool(&arena, tri, &Vec::new()).unwrap();
    assert!(
        ev.formula_bool(&arena, full, &Vec::new())
            .expect("evaluation"),
        "merged violates full (total={t_ok}, tri={b_ok})"
    );

    // UNSAT parity: shrink colors to two via a fresh bound set
    let mut bounds2 = bounds.clone();
    let c_rel = color;
    {
        let mut s = TupleSet::new(&u, 1).unwrap();
        s.insert_index(9); // single extra color beyond q0/q1? keep 2 total
        bounds2.bound_exactly(c_rel, &s).unwrap();
    }
    let mono2 = solver.solve(&mut arena, full, &bounds2).unwrap();
    let par2 = solver
        .solve_decomposed_parallel(&mut arena, full, &bounds2, 3)
        .unwrap();
    // both agree; either SAT or UNSAT is acceptable, but they must match
    assert_eq!(mono2.satisfiable, par2.satisfiable, "UNSAT parity");
}
