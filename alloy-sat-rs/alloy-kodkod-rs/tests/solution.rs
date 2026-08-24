#![cfg(feature = "ipasir")]

use alloy_kodkod_rs::ast::*;
use alloy_kodkod_rs::bounds::Bounds;
use alloy_kodkod_rs::cnf::translate_into_solver;
use alloy_kodkod_rs::eval::Evaluator;
use alloy_kodkod_rs::fol::{FolTranslator, TranslateError};
use alloy_kodkod_rs::instance::Instance;
use alloy_kodkod_rs::ipasir_bridge::IpasirSolver;
use alloy_kodkod_rs::relation::{RelationId, RelationPool};
use alloy_kodkod_rs::sat::SatSolver;
use alloy_kodkod_rs::tuple::Tuple;
use alloy_kodkod_rs::tupleset::TupleSet;
use alloy_kodkod_rs::universe::Universe;
use alloy_kodkod_rs::BoolCtx;
use std::sync::Arc;

struct Queens {
    arena: AstArena,
    bounds: Bounds,
    u: Arc<Universe>,
}

impl Queens {
    fn new(n: usize) -> Queens {
        let atoms: Vec<String> = (0..n).map(|i| format!("b{i}")).collect();
        let refs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
        let u = Universe::new(refs).unwrap();
        let pool = Arc::new(RelationPool::new());
        let bounds = Bounds::new(&u, &pool);
        Queens {
            arena: AstArena::with_pool(Arc::clone(&pool)),
            bounds,
            u,
        }
    }

    fn board(&mut self) -> RelationId {
        let b = self.arena.relation("Board", 1);
        let mut s = TupleSet::new(&self.u, 1).unwrap();
        for i in 0..self.u.size() {
            s.insert_index(i as i64);
        }
        self.bounds.bound_exactly(b, &s).unwrap();
        b
    }

    fn queens_upper_free(&mut self) -> RelationId {
        let q = self.arena.relation("Q", 2);
        let mut s = TupleSet::new(&self.u, 2).unwrap();
        let n = self.u.size() as i64;
        for r in 0..n {
            for c in 0..n {
                s.insert_index(r * n + c);
            }
        }
        self.bounds.bound_upper(q, &s).unwrap();
        q
    }

    fn attack_quaternary(&mut self) -> RelationId {
        let atk = self.arena.relation("ATK", 4);
        let n = self.u.size() as i64;
        let mut s = TupleSet::new(&self.u, 4).unwrap();
        for r1 in 0..n {
            for c1 in 0..n {
                for r2 in 0..n {
                    if r2 == r1 {
                        continue;
                    }
                    for c2 in 0..n {
                        if c2 != c1 && (c1 - c2).abs() == (r1 - r2).abs() {
                            let idx = ((r1 * n + c1) * n + r2) * n + c2;
                            s.insert_index(idx);
                        }
                    }
                }
            }
        }
        self.bounds.bound_exactly(atk, &s).unwrap();
        atk
    }
}

fn queens_formula(m: &mut Queens, board: RelationId, q: RelationId, atk_expr: ExprId) -> FormulaId {
    // all r1: Board | all r2: Board | some c1: r1.Q | some c2: r2.Q |
    //   (r1,c1,r2,c2) in ATK => r1 = r2
    let mut clauses: Vec<FormulaId> = Vec::new();

    // rows: one r.Q
    let r1 = m.arena.variable("r1");
    let eb = m.arena.expr_relation(board);
    let d1 = m.arena.decl(r1, Multiplicity::One, eb).unwrap();
    let ds_rows = m.arena.add_decls(vec![d1]);
    let ex_r1 = m.arena.expr_variable(r1);
    let eq_ = m.arena.expr_relation(q);
    let rq = m.arena.binary_expr(BinaryOp::Join, ex_r1, eq_).unwrap();
    let one_body = m.arena.multiplicity_formula(Multiplicity::One, rq).unwrap();
    let row_one = m.arena.quantified(Quantifier::All, ds_rows, one_body);
    clauses.push(row_one);

    // cols: one c.~Q
    let c1v = m.arena.variable("c1");
    let eb2 = m.arena.expr_relation(board);
    let dc = m.arena.decl(c1v, Multiplicity::One, eb2).unwrap();
    let ds_cols = m.arena.add_decls(vec![dc]);
    let ex_c = m.arena.expr_variable(c1v);
    let eqq = m.arena.expr_relation(q);
    let tq = m.arena.unary_expr(UnaryExprOp::Transpose, eqq).unwrap();
    let cq = m.arena.binary_expr(BinaryOp::Join, ex_c, tq).unwrap();
    let col_body = m.arena.multiplicity_formula(Multiplicity::One, cq).unwrap();
    let col_one = m.arena.quantified(Quantifier::All, ds_cols, col_body);
    clauses.push(col_one);

    // diagonals
    let rv1 = m.arena.variable("rv1");
    let rv2 = m.arena.variable("rv2");
    let cv1 = m.arena.variable("cv1");
    let cv2 = m.arena.variable("cv2");

    let db = m.arena.expr_relation(board);
    let dr1 = m.arena.decl(rv1, Multiplicity::One, db).unwrap();
    let db2 = m.arena.expr_relation(board);
    let dr2 = m.arena.decl(rv2, Multiplicity::One, db2).unwrap();
    let ds_diag = m.arena.add_decls(vec![dr1, dr2]);

    let e_rv1 = m.arena.expr_variable(rv1);
    let eq1 = m.arena.expr_relation(q);
    let j1 = m.arena.binary_expr(BinaryOp::Join, e_rv1, eq1).unwrap();
    let dc1 = m.arena.decl(cv1, Multiplicity::Some, j1).unwrap();
    let ds_c1 = m.arena.add_decls(vec![dc1]);

    let e_rv2 = m.arena.expr_variable(rv2);
    let eq2 = m.arena.expr_relation(q);
    let j2 = m.arena.binary_expr(BinaryOp::Join, e_rv2, eq2).unwrap();
    let dc2 = m.arena.decl(cv2, Multiplicity::Some, j2).unwrap();
    let ds_c2 = m.arena.add_decls(vec![dc2]);

    // tuple (rv1,cv1,rv2,cv2) in ATK
    let t_rv1 = m.arena.expr_variable(rv1);
    let t_cv1 = m.arena.expr_variable(cv1);
    let t_rv2 = m.arena.expr_variable(rv2);
    let t_cv2 = m.arena.expr_variable(cv2);
    let p1 = m
        .arena
        .binary_expr(BinaryOp::Product, t_rv1, t_cv1)
        .unwrap();
    let p2 = m.arena.binary_expr(BinaryOp::Product, p1, t_rv2).unwrap();
    let quad = m.arena.binary_expr(BinaryOp::Product, p2, t_cv2).unwrap();
    let in_atk = m.subset(quad, atk_expr);

    let inner = m.arena.quantified(Quantifier::Some, ds_c2, in_atk);
    let mid = m.arena.quantified(Quantifier::Some, ds_c1, inner);

    let same = {
        let a = m.arena.expr_variable(rv1);
        let b = m.arena.expr_variable(rv2);
        m.arena.comparison(ExprCompOp::Equals, a, b).unwrap()
    };
    let not_same = m.arena.not(same);
    let violation = m.arena.and(&[not_same, mid]);
    let no_violation = m.arena.not(violation);
    let diag_all = m.arena.quantified(Quantifier::All, ds_diag, no_violation);
    clauses.push(diag_all);

    m.arena.and(&clauses)
}

impl Queens {
    fn subset(&mut self, a: ExprId, b: ExprId) -> FormulaId {
        self.arena.comparison(ExprCompOp::Subset, a, b).unwrap()
    }
}

#[test]
fn nqueens4_solves_materializes_and_evaluates() -> Result<(), TranslateError> {
    let mut m = Queens::new(4);
    let board = m.board();
    let q = m.queens_upper_free();
    let atk = m.attack_quaternary();

    let atk_e = m.arena.expr_relation(atk);
    let f = queens_formula(&mut m, board, q, atk_e);

    let mut translator = FolTranslator::new(BoolCtx::new(), &m.bounds);
    let root = translator.formula_ref(&m.arena, f, &[])?;
    let max_primary = translator.ctx.num_slots();
    let ctx = translator.ctx.clone();
    let mut solver = IpasirSolver::new().unwrap();
    ctx.with_factory(|factory| translate_into_solver(&mut solver, factory, root, max_primary))?;
    assert!(
        SatSolver::solve(&mut solver),
        "4-queens must be satisfiable"
    );

    let origins: Vec<_> = translator.var_origins().to_vec();
    assert!(!origins.is_empty(), "free Q upper bound must allocate vars");

    let inst: Instance = translator.materialize(|slot| SatSolver::value_of(&solver, slot as i64));

    // every free var true/false decided consistently: count placed queens == 4
    let qs = inst.tuples(q).unwrap();
    assert_eq!(qs.len(), 4, "exactly 4 queens placed");

    // evaluator re-verifies the full formula on the materialized instance
    let ev = Evaluator::new(&inst);
    assert!(
        ev.formula_bool(&m.arena, f, &Vec::new())
            .unwrap_or_else(|e| panic!("eval failed: {e}")),
        "materialized solution satisfies constraints"
    );

    // print the board (demo)
    let n = m.u.size();
    println!("\n4-queens solution:");
    for r in 0..n {
        let mut line = String::new();
        for c in 0..n {
            line.push(if qs.contains_index((r * n + c) as i64) {
                'Q'
            } else {
                '.'
            });
        }
        println!("  {line}");
    }

    Ok(())
}

#[test]
fn evaluator_rejects_perturbed_board() -> Result<(), TranslateError> {
    let mut m = Queens::new(4);
    let _board = m.board();
    let q = m.queens_upper_free();
    let atk = m.attack_quaternary();
    let atk_e = m.arena.expr_relation(atk);
    let f = queens_formula(&mut m, _board, q, atk_e);

    let mut translator = FolTranslator::new(BoolCtx::new(), &m.bounds);
    let root = translator.formula_ref(&m.arena, f, &[])?;
    let mp = translator.ctx.num_slots();
    let ctx = translator.ctx.clone();
    let mut solver = IpasirSolver::new().unwrap();
    ctx.with_factory(|factory| translate_into_solver(&mut solver, factory, root, mp))?;
    assert!(SatSolver::solve(&mut solver));
    let inst = translator.materialize(|slot| SatSolver::value_of(&solver, slot as i64));

    // remove one queen tuple -> row totality breaks
    let mut broken = Instance::new(inst.universe(), inst.pool());
    for r in inst.relations() {
        let arity = inst.pool().arity(r);
        let src = inst.tuples(r).unwrap();
        let mut ts = TupleSet::new(inst.universe(), arity).unwrap();
        let skip = if r == q {
            Some(src.index_view().max().unwrap())
        } else {
            None
        };
        for idx in src.index_view().iter() {
            if skip != Some(idx) {
                ts.insert_index(idx);
            }
        }
        broken.add(r, &ts).unwrap();
    }
    let ev = Evaluator::new(&broken);
    assert!(
        !ev.formula_bool(&m.arena, f, &Vec::new())
            .unwrap_or_else(|e| panic!("eval failed: {e}")),
        "removing a queen must violate the constraints"
    );
    Ok(())
}

#[test]
fn materialization_keeps_lower_bounds_intact() -> Result<(), TranslateError> {
    let mut m = Queens::new(3);
    let fixed = m.rel_exact_helper("fixed", 1, &["b1"]);
    let _b = m.board();
    let f = m.arena.true_formula();

    let mut translator = FolTranslator::new(BoolCtx::new(), &m.bounds);
    let _root = translator.formula_ref(&m.arena, f, &[])?;
    let inst = translator.materialize(|_| false);
    let fs = inst.tuples(fixed).unwrap();
    assert_eq!(fs.len(), 1);
    assert!(fs.contains_index(1));
    Ok(())
}

impl Queens {
    fn rel_exact_helper(&mut self, name: &str, arity: u32, flat: &[&str]) -> RelationId {
        let r = self.arena.relation(name, arity);
        let mut s = TupleSet::new(&self.u, arity).unwrap();
        for chunk in flat.chunks(arity as usize) {
            let t = Tuple::from_atoms(&self.u, chunk).unwrap();
            s.insert(&t).unwrap();
        }
        self.bounds.bound_exactly(r, &s).unwrap();
        r
    }
}

#[test]
fn unsat_model_reports_no_solution() -> Result<(), TranslateError> {
    let mut m = Queens::new(2); // 2-queens is unsolvable
    let board = m.board();
    let q = m.queens_upper_free();
    let atk = m.attack_quaternary();
    let atk_e = m.arena.expr_relation(atk);
    let f = queens_formula(&mut m, board, q, atk_e);

    let mut translator = FolTranslator::new(BoolCtx::new(), &m.bounds);
    let root = translator.formula_ref(&m.arena, f, &[])?;
    let mp = translator.ctx.num_slots();
    let ctx = translator.ctx.clone();
    let mut solver = IpasirSolver::new().unwrap();
    ctx.with_factory(|factory| translate_into_solver(&mut solver, factory, root, mp))?;
    assert!(
        !SatSolver::solve(&mut solver),
        "2-queens is classically UNSAT"
    );
    Ok(())
}
