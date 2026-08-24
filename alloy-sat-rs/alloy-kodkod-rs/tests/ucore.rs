//! Iter 9 acceptance tests: UNSAT core extraction (`-core=rce` equivalent).
//!
//! The AST-level tests use the IPASIR/CaDiCaL backend (`failed` assumptions);
//! the CNF-level soft-group tests run on `RecordingSolver` and therefore
//! work with or without the `ipasir` feature.

use alloy_kodkod_rs::ast::*;
use alloy_kodkod_rs::relation::RelationPool;
use alloy_kodkod_rs::sat::{RecordingSolver, SatSolver};
use alloy_kodkod_rs::ucore::{conjuncts_of, extract_cnf_core, SoftGroup};
use std::sync::Arc;

#[test]
fn conjuncts_flatten_nested_ands() {
    let mut arena = AstArena::with_pool(Arc::new(RelationPool::new()));
    let a = arena.bool_formula(true);
    let b = arena.bool_formula(false);
    let inner = arena.and(&[a, b]);
    let root = arena.and(&[inner, a]);
    let cs = conjuncts_of(&arena, root);
    assert_eq!(cs.len(), 3);
}

#[cfg(feature = "ipasir")]
mod ipasir_tests {
    use alloy_kodkod_rs::ast::*;
    use alloy_kodkod_rs::bounds::Bounds;
    use alloy_kodkod_rs::eval::Evaluator;
    use alloy_kodkod_rs::ipasir_bridge::IpasirSolver;
    use alloy_kodkod_rs::relation::{RelationId, RelationPool};
    use alloy_kodkod_rs::tuple::Tuple;
    use alloy_kodkod_rs::tupleset::TupleSet;
    use alloy_kodkod_rs::universe::Universe;
    use alloy_kodkod_rs::Solver;
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

        /// Relation with the given upper bound and an empty lower bound.
        fn rel_free(&mut self, name: &str, arity: u32, upper: &[&str]) -> RelationId {
            let r = self.arena.relation(name, arity);
            let mut s = TupleSet::new(&self.u, arity).unwrap();
            for chunk in upper.chunks(arity as usize) {
                let t = Tuple::from_atoms(&self.u, chunk).unwrap();
                s.insert(&t).unwrap();
            }
            self.bounds.bound_upper(r, &s).unwrap();
            r
        }

        /// Relation pinned to exactly one tuple set (or the empty relation).
        fn rel_exact(&mut self, name: &str, arity: u32, flat: &[&str]) -> RelationId {
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

    fn some_of(arena: &mut AstArena, r: RelationId) -> FormulaId {
        let e = arena.expr_relation(r);
        arena.multiplicity_formula(Multiplicity::Some, e).unwrap()
    }

    fn no_of(arena: &mut AstArena, r: RelationId) -> FormulaId {
        let inner = some_of(arena, r);
        arena.not(inner)
    }

    #[test]
    fn core_maps_back_to_culprit_conjuncts() {
        // f0: no p, f1: some p, f2: tautology. The core must be {f0, f1}.
        let mut m = Model::new(&["a", "b"]);
        let p = m.rel_free("p", 1, &["a", "b"]);
        let f0 = no_of(&mut m.arena, p);
        let f1 = some_of(&mut m.arena, p);
        let f2 = m.arena.bool_formula(true);
        let formula = m.arena.and(&[f0, f1, f2]);

        let sol = Solver::new()
            .solve_core(&m.arena, formula, &m.bounds)
            .unwrap();
        assert!(!sol.satisfiable);
        assert_eq!(sol.core, vec![0, 1]);
    }

    #[test]
    fn core_shrinks_and_members_are_necessary() {
        // Two independent conflicts plus blame-free filler conjuncts:
        // f0: no p   f1: some p          (conflict A)
        // f2: no q   f3: some q          (conflict B)
        // f4: p subset p (tautology), f5/f6: true
        let mut m = Model::new(&["a", "b"]);
        let p = m.rel_free("p", 1, &["a", "b"]);
        let q = m.rel_free("q", 1, &["a", "b"]);
        let fs = vec![
            no_of(&mut m.arena, p),
            some_of(&mut m.arena, p),
            no_of(&mut m.arena, q),
            some_of(&mut m.arena, q),
            {
                let e = m.arena.expr_relation(p);
                m.arena.comparison(ExprCompOp::Subset, e, e).unwrap()
            },
            m.arena.bool_formula(true),
            m.arena.bool_formula(true),
        ];
        let formula = m.arena.and(&fs);

        let sol = Solver::new()
            .solve_core(&m.arena, formula, &m.bounds)
            .unwrap();
        assert!(!sol.satisfiable);

        // Shrinking happened: tautologies are never blamed; only the four
        // atomic constraint conjuncts can appear.
        assert!(sol.core.len() < fs.len(), "core={:?}", sol.core);
        for &c in &sol.core {
            assert!(c <= 3, "blamed tautological conjunct #{c}");
        }
        assert!(sol.core.len() >= 2, "core={:?} too small", sol.core);

        // Every member is individually necessary: dropping it yields SAT.
        let mut solver_fn = |keep: &[usize]| {
            let kept: Vec<FormulaId> = keep.iter().map(|&i| fs[i]).collect();
            let f = m.arena.and(&kept);
            let mut s = IpasirSolver::new().unwrap();
            Solver::new()
                .solve_core_with(&mut s, &m.arena, f, &m.bounds)
                .unwrap()
                .satisfiable
        };
        assert!(!solver_fn(&sol.core));
        for drop in &sol.core {
            let keep: Vec<usize> = sol.core.iter().copied().filter(|&c| c != *drop).collect();
            assert!(solver_fn(&keep), "member {drop} is not necessary");
        }
    }

    #[test]
    fn sat_problem_has_empty_core_and_valid_instance() {
        let mut m = Model::new(&["a", "b"]);
        let p = m.rel_free("p", 1, &["a", "b"]);
        let f0 = some_of(&mut m.arena, p);
        let f1 = m.arena.bool_formula(true);
        let formula = m.arena.and(&[f0, f1]);

        let sol = Solver::new()
            .solve_core(&m.arena, formula, &m.bounds)
            .unwrap();
        assert!(sol.satisfiable);
        assert!(sol.core.is_empty());
        let inst = sol.instance.as_ref().unwrap();

        // Re-validate both conjuncts against the materialized instance.
        let ev = Evaluator::new(inst);
        let empty: Vec<(VarId, Vec<u32>)> = Vec::new();
        assert!(ev.formula_bool(&m.arena, f0, &empty).unwrap());
        assert!(ev.formula_bool(&m.arena, f1, &empty).unwrap());
    }

    #[test]
    fn trivially_false_conjunct_is_whole_core() {
        // p is bound to exactly {} so `some p` folds to constant false.
        let mut m = Model::new(&["a", "b"]);
        let p = m.rel_exact("p", 1, &[]);
        let f0 = some_of(&mut m.arena, p);
        let f1 = m.arena.bool_formula(true);
        let formula = m.arena.and(&[f0, f1]);

        let sol = Solver::new()
            .solve_core(&m.arena, formula, &m.bounds)
            .unwrap();
        assert!(!sol.satisfiable);
        assert_eq!(sol.core, vec![0]);
        assert!(sol.instance.is_none());
    }
}

// ---------------------------------------------------------------------------
// CNF-level soft-group extraction on RecordingSolver (feature-independent)
// ---------------------------------------------------------------------------

#[test]
fn cnf_core_finds_minimal_conflicting_groups() {
    // Groups: {x1}, {¬x1}, {x2}. Only the first two conflict.
    let mut s = RecordingSolver::new();
    s.add_variables(2);
    let soft = vec![
        SoftGroup::new("x1", vec![vec![1]]),
        SoftGroup::new("not-x1", vec![vec![-1]]),
        SoftGroup::new("x2", vec![vec![2]]),
    ];
    let core = extract_cnf_core(&mut s, &[], &soft).unwrap().unwrap();
    assert_eq!(core.groups, vec![0, 1]);
    // The exact minimal core is computed by brute force.
    assert_eq!(core.initial, vec![0, 1]);
    assert!(core.solves >= 2);
}

#[test]
fn cnf_core_sat_problem_returns_none() {
    let mut s = RecordingSolver::new();
    s.add_variables(2);
    let soft = vec![
        SoftGroup::new("x1", vec![vec![1]]),
        SoftGroup::new("x2", vec![vec![2]]),
    ];
    assert!(extract_cnf_core(&mut s, &[], &soft).unwrap().is_none());
}

#[test]
fn cnf_core_with_hard_clauses() {
    // Hard: x1 ∨ x2. Groups {¬x1} and {¬x2} are individually fine (the
    // other literal can hold) but jointly contradict the hard clause;
    // {¬x3} is irrelevant. Core must be exactly {0, 1}.
    let mut s = RecordingSolver::new();
    s.add_variables(3);
    let hard = vec![vec![1, 2]];
    let soft = vec![
        SoftGroup::new("not-x1", vec![vec![-1]]),
        SoftGroup::new("not-x2", vec![vec![-2]]),
        SoftGroup::new("not-x3", vec![vec![-3]]),
    ];
    let core = extract_cnf_core(&mut s, &hard, &soft).unwrap().unwrap();
    assert_eq!(core.groups, vec![0, 1]);
}

#[test]
fn cnf_single_group_conflict_with_hard() {
    // Hard: x3. Group {¬x3} alone contradicts it; everything else is fine.
    let mut s = RecordingSolver::new();
    s.add_variables(3);
    let hard = vec![vec![3]];
    let soft = vec![
        SoftGroup::new("not-x3", vec![vec![-3]]),
        SoftGroup::new("x1", vec![vec![1]]),
    ];
    let core = extract_cnf_core(&mut s, &hard, &soft).unwrap().unwrap();
    assert_eq!(core.groups, vec![0]);
}
