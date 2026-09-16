//! Optimization (Iter 13) tests: OLL core-guided loop over weighted
//! relation sums and integer objectives, solved with RecordingSolver
//! (exact brute-force oracle backend) plus one CaDiCaL-backed test.

use alloy_kodkod_rs::ast::*;
use alloy_kodkod_rs::bounds::Bounds;
use alloy_kodkod_rs::opt::{Objective, OptSense, OptSolution};
use alloy_kodkod_rs::relation::{RelationId, RelationPool};
use alloy_kodkod_rs::sat::RecordingSolver;
use alloy_kodkod_rs::solver::Solver;
use alloy_kodkod_rs::tuple::Tuple;
use alloy_kodkod_rs::tupleset::TupleSet;
use alloy_kodkod_rs::universe::Universe;
use std::collections::HashMap;
use std::sync::Arc;

struct Model {
    arena: AstArena,
    bounds: Bounds,
    u: Arc<Universe>,
}

impl Model {
    fn new(atoms: &[&str]) -> Model {
        let u = Universe::new(atoms.to_vec()).unwrap();
        let pool = Arc::new(RelationPool::new());
        let bounds = Bounds::new(&u, &pool);
        Model {
            arena: AstArena::with_pool(Arc::clone(&pool)),
            bounds,
            u,
        }
    }

    fn rel(&mut self, name: &str, arity: u32, upper: &[&str], lower: &[&str]) -> RelationId {
        let r = self.arena.relation(name, arity);
        let build = |flat: &[&str]| {
            let mut s = TupleSet::new(&self.u, arity).unwrap();
            for chunk in flat.chunks(arity as usize) {
                let t = Tuple::from_atoms(&self.u, chunk).unwrap();
                s.insert(&t).unwrap();
            }
            s
        };
        let up = build(upper);
        if lower.len() == upper.len() && lower.iter().zip(upper).all(|(a, b)| a == b) {
            self.bounds.bound_exactly(r, &up).unwrap();
        } else {
            let lo = build(lower);
            self.bounds.bound(r, &lo, &up).unwrap();
        }
        r
    }

    fn var_unary(&mut self, name: &str, atoms: &[&str]) -> RelationId {
        self.rel(name, 1, atoms, &[])
    }

    fn leaf(&mut self, r: RelationId) -> ExprId {
        self.arena.expr_relation(r)
    }

    fn some_rel(&mut self, r: RelationId) -> FormulaId {
        let e = self.leaf(r);
        self.arena
            .multiplicity_formula(Multiplicity::Some, e)
            .unwrap()
    }

    fn card_of(&mut self, r: RelationId) -> IntId {
        let e = self.leaf(r);
        self.arena
            .cast_to_int(CastToIntOp::Cardinality, e)
            .unwrap()
    }

    fn opt_with(
        &self,
        solver: &mut RecordingSolver,
        f: FormulaId,
        obj: Objective,
    ) -> OptSolution {
        Solver::new()
            .solve_opt_with(solver, &self.arena, f, &self.bounds, obj)
            .unwrap()
    }
}

fn weights(pairs: &[(RelationId, i64)]) -> HashMap<RelationId, i64> {
    pairs.iter().copied().collect()
}

#[test]
fn max_cardinality_unconstrained() {
    let mut m = Model::new(&["n0", "n1", "n2"]);
    let r = m.var_unary("r", &["n0", "n1", "n2"]);
    let f = m.arena.true_formula();
    let sol = m.opt_with(
        &mut RecordingSolver::new(),
        f,
        Objective::max_weighted(weights(&[(r, 1)])),
    );
    assert!(sol.satisfiable);
    assert_eq!(sol.cost, Some(3));
    let inst = sol.instance.unwrap();
    assert_eq!(inst.tuples(r).unwrap().len(), 3);
}

#[test]
fn min_cardinality_with_some_constraint() {
    let mut m = Model::new(&["n0", "n1", "n2"]);
    let r = m.var_unary("r", &["n0", "n1", "n2"]);
    let f = m.some_rel(r);
    let sol = m.opt_with(
        &mut RecordingSolver::new(),
        f,
        Objective::min_weighted(weights(&[(r, 1)])),
    );
    assert!(sol.satisfiable);
    assert_eq!(sol.cost, Some(1));
}

#[test]
fn weighted_two_relations() {
    let mut m = Model::new(&["n0", "n1"]);
    let r1 = m.var_unary("r1", &["n0", "n1"]); // 2 cells, w=2
    let r2 = m.var_unary("r2", &["n0"]); // 1 cell, w=5
    let f = m.arena.true_formula();
    let sol = m.opt_with(
        &mut RecordingSolver::new(),
        f,
        Objective::max_weighted(weights(&[(r1, 2), (r2, 5)])),
    );
    assert!(sol.satisfiable);
    assert_eq!(sol.cost, Some(2 * 2 + 5));
    // Minimization of the same problem must bottom out at 0 (empty model).
    let sol = m.opt_with(
        &mut RecordingSolver::new(),
        f,
        Objective::min_weighted(weights(&[(r1, 2), (r2, 5)])),
    );
    assert!(sol.satisfiable);
    assert_eq!(sol.cost, Some(0));
}

#[test]
fn lower_bounds_count_toward_cost() {
    // lower={n0} is forced true: maximizing #r must yield 2 (not 1),
    // even though only one cell is a search variable.
    let mut m = Model::new(&["n0", "n1"]);
    let r = m.rel("r", 1, &["n0", "n1"], &["n0"]);
    let f = m.arena.true_formula();
    let sol = m.opt_with(
        &mut RecordingSolver::new(),
        f,
        Objective::max_weighted(weights(&[(r, 1)])),
    );
    assert!(sol.satisfiable);
    assert_eq!(sol.cost, Some(2));
}

#[test]
fn weighted_negative_weight_prefers_empty() {
    // Regression for the fresh-variable aliasing bug: selectors must
    // live past every primary slot, otherwise soft clauses silently
    // misbehave. A full B at w=-1 must lose to an empty B.
    let mut m = Model::new(&["n0", "n1"]);
    let a = m.var_unary("a", &["n0", "n1"]); // 2 cells, w=+2
    let b = m.var_unary("b", &["n0", "n1"]); // 2 cells, w=-1
    let f = m.arena.true_formula();
    let sol = m.opt_with(
        &mut RecordingSolver::new(),
        f,
        Objective::max_weighted(weights(&[(a, 2), (b, -1)])),
    );
    assert!(sol.satisfiable);
    assert_eq!(sol.cost, Some(4));
    let inst = sol.instance.unwrap();
    assert_eq!(inst.tuples(a).unwrap().len(), 2);
    assert_eq!(inst.tuples(b).unwrap().len(), 0);
}

#[test]
fn and_conjunctions_maximize() {
    // `#(r & s)` without the counting circuit: two unary relations over
    // {n0, n1}; optimum picks both shared cells.
    use alloy_kodkod_rs::opt::CellRef;
    let mut m = Model::new(&["n0", "n1"]);
    let r = m.var_unary("r", &["n0", "n1"]);
    let s = m.var_unary("s", &["n0", "n1"]);
    // Flat indices for unary relations over a 2-atom universe: n0->0, n1->1.
    let pairs = vec![
        (
            CellRef { relation: r, tuple_index: 0 },
            CellRef { relation: s, tuple_index: 0 },
            1,
        ),
        (
            CellRef { relation: r, tuple_index: 1 },
            CellRef { relation: s, tuple_index: 1 },
            1,
        ),
    ];
    let f = m.arena.true_formula();
    let sol = Solver::new()
        .solve_opt_with(
            &mut RecordingSolver::new(),
            &m.arena,
            f,
            &m.bounds,
            Objective::max_and(pairs),
        )
        .unwrap();
    assert!(sol.satisfiable);
    assert_eq!(sol.cost, Some(2));
    // Minimizing the same conjunctions bottoms out at 0.
    let pairs = vec![
        (
            CellRef { relation: r, tuple_index: 0 },
            CellRef { relation: s, tuple_index: 0 },
            1,
        ),
        (
            CellRef { relation: r, tuple_index: 1 },
            CellRef { relation: s, tuple_index: 1 },
            1,
        ),
    ];
    let sol = Solver::new()
        .solve_opt_with(
            &mut RecordingSolver::new(),
            &m.arena,
            f,
            &m.bounds,
            Objective::min_and(pairs),
        )
        .unwrap();
    assert!(sol.satisfiable);
    assert_eq!(sol.cost, Some(0));
}

#[test]
fn int_constant_objective() {
    // All-const bits: no softs; the feasible model is trivially optimal.
    let mut m = Model::new(&["n0", "n1"]);
    let five = m.arena.int_constant(5);
    let f = m.arena.true_formula();
    let sol = m.opt_with(&mut RecordingSolver::new(), f, Objective::max_int(five));
    assert!(sol.satisfiable);
    assert_eq!(sol.cost, Some(5));
    let sol = m.opt_with(&mut RecordingSolver::new(), f, Objective::min_int(five));
    assert!(sol.satisfiable);
    assert_eq!(sol.cost, Some(5));
}

#[test]
fn unsat_reports_no_cost() {
    let mut m = Model::new(&["n0", "n1"]);
    let r = m.rel("r", 1, &[], &[]); // exact empty
    let f = m.some_rel(r);
    let sol = m.opt_with(
        &mut RecordingSolver::new(),
        f,
        Objective::max_weighted(weights(&[(r, 1)])),
    );
    assert!(!sol.satisfiable);
    assert_eq!(sol.cost, None);
    assert!(sol.instance.is_none());
}

#[test]
fn sense_and_pardinus_constructors() {
    // Objective::Int carries its sense; from_pardinus mirrors weights.
    let mut m = Model::new(&["n0"]);
    let r = m.var_unary("r", &["n0"]);
    let card = m.card_of(r);
    assert!(matches!(
        Objective::max_int(card),
        Objective::Int {
            sense: OptSense::Maximize,
            ..
        }
    ));
    assert!(matches!(
        Objective::min_weighted(weights(&[(r, 1)])),
        Objective::Weighted {
            sense: OptSense::Minimize,
            ..
        }
    ));
}

#[cfg(feature = "ipasir")]
#[test]
fn ipasir_backend_agrees_with_recording() {
    use alloy_kodkod_rs::ipasir_bridge::IpasirSolver;
    let mut m = Model::new(&["n0", "n1", "n2"]);
    let r = m.var_unary("r", &["n0", "n1", "n2"]);
    let f = m.arena.true_formula();
    let solver = Solver::new();
    let mut ipasir = IpasirSolver::new().unwrap();
    let sol = solver
        .solve_opt_with(
            &mut ipasir,
            &m.arena,
            f,
            &m.bounds,
            Objective::max_weighted(weights(&[(r, 1)])),
        )
        .unwrap();
    assert!(sol.satisfiable);
    assert_eq!(sol.cost, Some(3));

    // Int objective through the real CaDiCaL core path (failed_core).
    let card = m.card_of(r);
    let mut ipasir = IpasirSolver::new().unwrap();
    let sol = solver
        .solve_opt_with(&mut ipasir, &m.arena, f, &m.bounds, Objective::min_int(card))
        .unwrap();
    assert!(sol.satisfiable);
    assert_eq!(sol.cost, Some(0));

    // Int max with arithmetic: (#r + 1) over P({n0,n1,n2}) → 4.
    let card = m.card_of(r);
    let one = m.arena.int_constant(1);
    let plus = m.arena.binary_int(IntBinOp::Plus, card, one);
    let mut ipasir = IpasirSolver::new().unwrap();
    let sol = solver
        .solve_opt_with(
            &mut ipasir,
            &m.arena,
            f,
            &m.bounds,
            Objective::max_int(plus),
        )
        .unwrap();
    assert!(sol.satisfiable);
    assert_eq!(sol.cost, Some(4));

    // Int min under a constraint: some r → min #r = 1.
    let some = m.some_rel(r);
    let mut ipasir = IpasirSolver::new().unwrap();
    let sol = solver
        .solve_opt_with(
            &mut ipasir,
            &m.arena,
            some,
            &m.bounds,
            Objective::min_int(card),
        )
        .unwrap();
    assert!(sol.satisfiable);
    assert_eq!(sol.cost, Some(1));
}
