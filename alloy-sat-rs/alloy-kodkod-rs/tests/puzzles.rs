//! Shared puzzle builders for the Iter-6 example suite (queens / pigeonhole /
//! graph coloring). Used by `tests/examples_suite.rs` and the `solve` example.

#![allow(dead_code)]

use alloy_kodkod_rs::ast::*;
use alloy_kodkod_rs::bounds::Bounds;
use alloy_kodkod_rs::intset::Int;
use alloy_kodkod_rs::relation::{RelationId, RelationPool};
use alloy_kodkod_rs::tupleset::TupleSet;
use alloy_kodkod_rs::universe::Universe;
use std::sync::Arc;

pub struct Puzzle {
    pub arena: AstArena,
    pub bounds: Bounds,
    pub formula: FormulaId,
    pub u: Arc<Universe>,
}

fn universe(names: &[String]) -> Arc<Universe> {
    let refs: Vec<&str> = names.iter().map(|s| s.as_str()).collect();
    Universe::new(refs).unwrap()
}

fn exact_rel(
    arena: &mut AstArena,
    bounds: &mut Bounds,
    u: &Arc<Universe>,
    name: &str,
    tuples: &[Vec<Int>],
) -> RelationId {
    let arity = tuples[0].len() as u32;
    let r = arena.relation(name, arity);
    let mut s = TupleSet::new(u, arity).unwrap();
    for t in tuples {
        let flat = t.iter().fold(0i64, |acc, &d| acc * u.size() as i64 + d);
        s.insert_index(flat as Int);
    }
    bounds.bound_exactly(r, &s).unwrap();
    r
}

fn full_upper_rel(
    arena: &mut AstArena,
    bounds: &mut Bounds,
    u: &Arc<Universe>,
    name: &str,
    arity: u32,
) -> RelationId {
    let n = u.size();
    let r = arena.relation(name, arity);
    let mut s = TupleSet::new(u, arity).unwrap();
    for idx in 0..n.pow(arity) {
        s.insert_index(idx as i64);
    }
    bounds.bound_upper(r, &s).unwrap();
    r
}

/// Upper-bounds `name` to the cross product of the given atom-id columns.
fn cross_upper_rel(
    arena: &mut AstArena,
    bounds: &mut Bounds,
    u: &Arc<Universe>,
    name: &str,
    cols: &[Vec<i64>],
) -> RelationId {
    let arity = cols.len() as u32;
    let r = arena.relation(name, arity);
    let mut s = TupleSet::new(u, arity).unwrap();
    fn rec(u: &Arc<Universe>, s: &mut TupleSet, cols: &[Vec<i64>], acc: i64) {
        match cols.split_first() {
            None => {
                s.insert_index(acc);
            }
            Some((first, rest)) => {
                for &d in first {
                    rec(u, s, rest, acc * u.size() as i64 + d);
                }
            }
        }
    }
    rec(u, &mut s, cols, 0);
    bounds.bound_upper(r, &s).unwrap();
    r
}

/// n-queens encoded with an explicit quaternary attack relation.
pub fn queens(n: usize) -> Puzzle {
    let atoms: Vec<String> = (0..n).map(|i| format!("b{i}")).collect();
    let u = universe(&atoms);
    let pool = Arc::new(RelationPool::new());
    let mut bounds = Bounds::new(&u, &pool);
    let mut arena = AstArena::with_pool(Arc::clone(&pool));

    // Board is exactly all atoms
    let board = {
        let b = arena.relation("Board", 1);
        let mut s = TupleSet::new(&u, 1).unwrap();
        for i in 0..u.size() {
            s.insert_index(i as i64);
        }
        bounds.bound_exactly(b, &s).unwrap();
        b
    };
    let q = full_upper_rel(&mut arena, &mut bounds, &u, "Q", 2);

    // ATK = set of mutually attacking (r1,c1,r2,c2)
    let atk = {
        let a = arena.relation("ATK", 4);
        let mut s = TupleSet::new(&u, 4).unwrap();
        let nu = n as i64;
        for r1 in 0..nu {
            for c1 in 0..nu {
                for r2 in 0..nu {
                    if r2 == r1 {
                        continue;
                    }
                    for c2 in 0..nu {
                        if c2 != c1 && (c1 - c2).abs() == (r1 - r2).abs() {
                            s.insert_index(((r1 * nu + c1) * nu + r2) * nu + c2);
                        }
                    }
                }
            }
        }
        bounds.bound_exactly(a, &s).unwrap();
        a
    };

    let board_e = arena.expr_relation(board);

    // all r: Board | one r.Q
    let rv = arena.variable("r");
    let rv_e = arena.expr_variable(rv);
    let q_e = arena.expr_relation(q);
    let rq = arena.binary_expr(BinaryOp::Join, rv_e, q_e).unwrap();
    let d_r = arena.decl(rv, Multiplicity::One, board_e).unwrap();
    let row_body = arena.multiplicity_formula(Multiplicity::One, rq).unwrap();
    let ds_r = arena.add_decls(vec![d_r]);
    let row_one = arena.quantified(Quantifier::All, ds_r, row_body);

    // all c: Board | one c.~Q
    let cv = arena.variable("c");
    let cv_e = arena.expr_variable(cv);
    let tq = arena.unary_expr(UnaryExprOp::Transpose, q_e).unwrap();
    let cq = arena.binary_expr(BinaryOp::Join, cv_e, tq).unwrap();
    let d_c = arena.decl(cv, Multiplicity::One, board_e).unwrap();
    let col_body = arena.multiplicity_formula(Multiplicity::One, cq).unwrap();
    let ds_c = arena.add_decls(vec![d_c]);
    let col_one = arena.quantified(Quantifier::All, ds_c, col_body);

    // no r1,r2,c1,c2 : (r1,c1,r2,c2) in ATK && (r1,c1) in Q && (r2,c2) in Q
    let v1 = arena.variable("r1");
    let v2 = arena.variable("r2");
    let v3 = arena.variable("c1");
    let v4 = arena.variable("c2");
    let e1 = arena.expr_variable(v1);
    let e2 = arena.expr_variable(v2);
    let e3 = arena.expr_variable(v3);
    let e4 = arena.expr_variable(v4);
    let t1 = arena.binary_expr(BinaryOp::Product, e1, e3).unwrap();
    let t2 = arena.binary_expr(BinaryOp::Product, e2, e4).unwrap();
    let quad = {
        let p1 = t1;
        let p2 = arena.binary_expr(BinaryOp::Product, p1, e2).unwrap();
        arena.binary_expr(BinaryOp::Product, p2, e4).unwrap()
    };
    let atk_e = arena.expr_relation(atk);
    let q_e2 = arena.expr_relation(q);
    let in_atk = arena.comparison(ExprCompOp::Subset, quad, atk_e).unwrap();
    let in_q1 = arena.comparison(ExprCompOp::Subset, t1, q_e2).unwrap();
    let in_q2 = arena.comparison(ExprCompOp::Subset, t2, q_e2).unwrap();
    let q12 = arena.and(&[in_q1, in_q2]);
    let bad = arena.and(&[in_atk, q12]);
    let no_bad = arena.not(bad);
    let decls = vec![
        arena.decl(v1, Multiplicity::One, board_e).unwrap(),
        arena.decl(v2, Multiplicity::One, board_e).unwrap(),
        arena.decl(v3, Multiplicity::One, board_e).unwrap(),
        arena.decl(v4, Multiplicity::One, board_e).unwrap(),
    ];
    let ds_diag = arena.add_decls(decls);
    let clause = arena.quantified(Quantifier::All, ds_diag, no_bad);

    let formula = arena.and(&[row_one, col_one, clause]);
    Puzzle {
        arena,
        bounds,
        formula,
        u,
    }
}

/// Pigeonhole: k pigeons into m holes, injectively. SAT iff k <= m.
pub fn pigeonhole(k: usize, m: usize) -> Puzzle {
    let mut atoms: Vec<String> = (0..k).map(|i| format!("p{i}")).collect();
    atoms.extend((0..m).map(|i| format!("h{i}")));
    let u = universe(&atoms);
    let pool = Arc::new(RelationPool::new());
    let mut bounds = Bounds::new(&u, &pool);
    let mut arena = AstArena::with_pool(Arc::clone(&pool));

    let pigs: Vec<Vec<i64>> = (0..k).map(|i| vec![i as i64]).collect();
    let holes: Vec<Vec<i64>> = (0..m).map(|i| vec![(k + i) as i64]).collect();
    let pig = exact_rel(&mut arena, &mut bounds, &u, "Pig", &pigs);
    let hole = exact_rel(&mut arena, &mut bounds, &u, "Hole", &holes);
    let pig_ids: Vec<i64> = (0..k).map(|i| i as i64).collect();
    let hole_ids: Vec<i64> = (0..m).map(|i| (k + i) as i64).collect();
    let in_rel = cross_upper_rel(&mut arena, &mut bounds, &u, "IN", &[pig_ids, hole_ids]);

    // all p: Pig | one p.IN
    let pv = arena.variable("p");
    let pv_e = arena.expr_variable(pv);
    let pig_e = arena.expr_relation(pig);
    let in_e = arena.expr_relation(in_rel);
    let pin = arena.binary_expr(BinaryOp::Join, pv_e, in_e).unwrap();
    let d_p = arena.decl(pv, Multiplicity::One, pig_e).unwrap();
    let total_body = arena.multiplicity_formula(Multiplicity::One, pin).unwrap();
    let ds_p = arena.add_decls(vec![d_p]);
    let total = arena.quantified(Quantifier::All, ds_p, total_body);

    // all h: Hole | lone ~IN.h   (at most one pigeon per hole)
    let hv = arena.variable("h");
    let hv_e = arena.expr_variable(hv);
    let hole_e = arena.expr_relation(hole);
    let tin = arena.unary_expr(UnaryExprOp::Transpose, in_e).unwrap();
    let hin = arena.binary_expr(BinaryOp::Join, hv_e, tin).unwrap();
    let d_h = arena.decl(hv, Multiplicity::One, hole_e).unwrap();
    let inj_body = arena.multiplicity_formula(Multiplicity::Lone, hin).unwrap();
    let ds_h = arena.add_decls(vec![d_h]);
    let injective = arena.quantified(Quantifier::All, ds_h, inj_body);

    let formula = arena.and(&[total, injective]);
    Puzzle {
        arena,
        bounds,
        formula,
        u,
    }
}

/// Graph coloring: proper c-coloring of the given edge list.
/// Nodes/colors are atoms 0..n / n..n+c; edges are pairs of node ids.
pub fn coloring(n: usize, edges: &[(usize, usize)], c: usize) -> Puzzle {
    let mut atoms: Vec<String> = (0..n).map(|i| format!("n{i}")).collect();
    atoms.extend((0..c).map(|i| format!("col{i}")));
    let u = universe(&atoms);
    let pool = Arc::new(RelationPool::new());
    let mut bounds = Bounds::new(&u, &pool);
    let mut arena = AstArena::with_pool(Arc::clone(&pool));

    let nodes: Vec<Vec<i64>> = (0..n).map(|i| vec![i as i64]).collect();
    let colors: Vec<Vec<i64>> = (0..c).map(|i| vec![(n + i) as i64]).collect();
    let edges_t: Vec<Vec<i64>> = edges
        .iter()
        .map(|&(a, b)| vec![a as i64, b as i64])
        .collect();
    let node_ids: Vec<i64> = (0..n).map(|i| i as i64).collect();
    let color_ids: Vec<i64> = (0..c).map(|i| (n + i) as i64).collect();
    let node = exact_rel(&mut arena, &mut bounds, &u, "Node", &nodes);
    let color = exact_rel(&mut arena, &mut bounds, &u, "Color", &colors);
    let edge = exact_rel(&mut arena, &mut bounds, &u, "E", &edges_t);
    let assign = cross_upper_rel(&mut arena, &mut bounds, &u, "COL", &[node_ids, color_ids]);

    // all v: Node | some v.COL
    let vv = arena.variable("v");
    let vv_e = arena.expr_variable(vv);
    let node_e = arena.expr_relation(node);
    let col_e = arena.expr_relation(assign);
    let vcol = arena.binary_expr(BinaryOp::Join, vv_e, col_e).unwrap();
    let d_v = arena.decl(vv, Multiplicity::Some, node_e).unwrap();
    let total_body = arena
        .multiplicity_formula(Multiplicity::Some, vcol)
        .unwrap();
    let ds_v = arena.add_decls(vec![d_v]);
    let total = arena.quantified(Quantifier::All, ds_v, total_body);

    // all n1,n2: Node | all cc: Color |
    //   !((n1,n2) in E && cc in n1.COL && cc in n2.COL)
    let v1 = arena.variable("m1");
    let v2 = arena.variable("m2");
    let vc = arena.variable("cc");
    let e1 = arena.expr_variable(v1);
    let e2 = arena.expr_variable(v2);
    let ec = arena.expr_variable(vc);
    let pair = arena.binary_expr(BinaryOp::Product, e1, e2).unwrap();
    let edge_e = arena.expr_relation(edge);
    let col_e2 = arena.expr_relation(assign);
    let in_edge = arena.comparison(ExprCompOp::Subset, pair, edge_e).unwrap();
    let c1 = arena.binary_expr(BinaryOp::Join, e1, col_e2).unwrap();
    let c2 = arena.binary_expr(BinaryOp::Join, e2, col_e2).unwrap();
    let has1 = arena.comparison(ExprCompOp::Subset, ec, c1).unwrap();
    let has2 = arena.comparison(ExprCompOp::Subset, ec, c2).unwrap();
    let bad = arena.and(&[in_edge, has1, has2]);
    let no_bad = arena.not(bad);
    let node_e2 = arena.expr_relation(node);
    let color_e2 = arena.expr_relation(color);
    let decls = vec![
        arena.decl(v1, Multiplicity::One, node_e2).unwrap(),
        arena.decl(v2, Multiplicity::One, node_e2).unwrap(),
        arena.decl(vc, Multiplicity::One, color_e2).unwrap(),
    ];
    let ds_d = arena.add_decls(decls);
    let diff = arena.quantified(Quantifier::All, ds_d, no_bad);

    let formula = arena.and(&[total, diff]);
    Puzzle {
        arena,
        bounds,
        formula,
        u,
    }
}
