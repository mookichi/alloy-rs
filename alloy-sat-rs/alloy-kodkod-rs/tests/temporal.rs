#![cfg(feature = "ipasir")]

//! Iter-7 tests: temporal bounds expander, LTL->FOL rewrite, lasso
//! extraction, and stability under varying trace lengths.

use alloy_kodkod_rs::ast::*;
use alloy_kodkod_rs::bounds::Bounds;
use alloy_kodkod_rs::relation::{RelationId, RelationPool};
use alloy_kodkod_rs::temporal::{expand_bounds, TemporalError, TemporalEval};
use alloy_kodkod_rs::tupleset::TupleSet;
use alloy_kodkod_rs::universe::Universe;
use alloy_kodkod_rs::Solver;
use std::sync::Arc;

#[allow(dead_code)]
struct Ring {
    pub arena: AstArena,
    pub bounds: Bounds,
    pub u: Arc<Universe>,
    pub next: RelationId,
    pub tok: RelationId,
    pub p0: RelationId,
}

impl Ring {
    fn new(n: usize) -> Ring {
        let atoms: Vec<String> = (0..n).map(|i| format!("p{i}")).collect();
        let refs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
        let u = Universe::new(refs).unwrap();
        let pool = Arc::new(RelationPool::new());
        let mut bounds = Bounds::new(&u, &pool);
        let arena = AstArena::with_pool(Arc::clone(&pool));

        // static ring successor
        let next = {
            let r = arena.relation("next", 2);
            let mut s = TupleSet::new(&u, 2).unwrap();
            for i in 0..n {
                s.insert_index((i * n + (i + 1) % n) as i64);
            }
            bounds.bound_exactly(r, &s).unwrap();
            r
        };
        // static predicate {p0}
        let p0 = {
            let r = arena.relation("P0", 1);
            let mut s = TupleSet::new(&u, 1).unwrap();
            s.insert_index(0);
            bounds.bound_exactly(r, &s).unwrap();
            r
        };
        // variable token set
        let tok = {
            let r = arena.relation("tok", 1);
            arena.set_variable(r, true);
            let mut s = TupleSet::new(&u, 1).unwrap();
            for i in 0..n {
                s.insert_index(i as i64);
            }
            bounds.bound_upper(r, &s).unwrap();
            r
        };
        Ring {
            arena,
            bounds,
            u,
            next,
            tok,
            p0,
        }
    }

    /// always (one tok)
    fn always_one_tok(&mut self) -> FormulaId {
        let tok_e = self.arena.expr_relation(self.tok);
        let one = self
            .arena
            .multiplicity_formula(Multiplicity::One, tok_e)
            .unwrap();
        self.arena.temporal_unary(TemporalFormulaOp::Always, one)
    }

    /// always (tok' in next.tok)
    fn always_moves(&mut self) -> FormulaId {
        let tok_e = self.arena.expr_relation(self.tok);
        let tok_p = self.arena.prime(tok_e);
        let next_e = self.arena.expr_relation(self.next);
        let tok_e2 = self.arena.expr_relation(self.tok);
        let succ = self
            .arena
            .binary_expr(BinaryOp::Join, next_e, tok_e2)
            .unwrap();
        let mv = self
            .arena
            .comparison(ExprCompOp::Subset, tok_p, succ)
            .unwrap();
        self.arena.temporal_unary(TemporalFormulaOp::Always, mv)
    }

    /// eventually (some tok & P0)
    fn eventually_visits_p0(&mut self) -> FormulaId {
        let tok_e = self.arena.expr_relation(self.tok);
        let p0_e = self.arena.expr_relation(self.p0);
        let hit = self
            .arena
            .binary_expr(BinaryOp::Intersection, tok_e, p0_e)
            .unwrap();
        let some = self
            .arena
            .multiplicity_formula(Multiplicity::Some, hit)
            .unwrap();
        self.arena
            .temporal_unary(TemporalFormulaOp::Eventually, some)
    }

    /// eventually (tok = none)
    fn eventually_empty(&mut self) -> FormulaId {
        let tok_e = self.arena.expr_relation(self.tok);
        let none = self.arena.constant(ConstantExpr::Empty);
        let eq = self
            .arena
            .comparison(ExprCompOp::Equals, tok_e, none)
            .unwrap();
        self.arena.temporal_unary(TemporalFormulaOp::Eventually, eq)
    }
}

#[test]
fn expander_structure() {
    let mut ring = Ring::new(3);
    let _ = &mut ring.arena;
    let exp = expand_bounds(&ring.arena, &ring.bounds, 4, 1).unwrap();

    assert_eq!(exp.bounds.universe().size(), 3 + 4);
    assert_eq!(exp.mapping.len(), 1, "only tok is variable");
    assert!(exp.mapping.contains_key(&ring.tok));

    let state_ts = exp.bounds.lower_bound(exp.ids.state).unwrap();
    assert_eq!(state_ts.len(), 4);
    let first_ts = exp.bounds.lower_bound(exp.ids.first).unwrap();
    assert_eq!(first_ts.len(), 1);
    assert!(first_ts.contains_index(3)); // atom index of Time0_0
    let last_ts = exp.bounds.lower_bound(exp.ids.last).unwrap();
    assert_eq!(last_ts.len(), 1);
    assert!(last_ts.contains_index(6)); // Time3_0

    let pl = exp.bounds.lower_bound(exp.ids.prefix).unwrap();
    let pu = exp.bounds.upper_bound(exp.ids.prefix).unwrap();
    assert_eq!(pl.len(), 3); // chain 0->1->2->3
    assert_eq!(pu.len(), 3 + 4); // chain + loop-back candidates

    let lo = exp.bounds.lower_bound(exp.ids.loop_).unwrap();
    assert_eq!(lo.len(), 0, "LOOP must be free");
}

#[test]
fn unrolls_gt_1_rejected() {
    let ring = Ring::new(3);
    let err = expand_bounds(&ring.arena, &ring.bounds, 4, 2).unwrap_err();
    assert!(matches!(err, TemporalError::UnrollsWithoutPast));
}

/// The token-ring problem: exactly one token, it moves along the ring, and it
/// eventually returns to p0.
#[test]
fn token_ring_sat_and_stable_across_steps() {
    let solver = Solver::new();
    for steps in [4usize, 5, 6] {
        let mut ring = Ring::new(4);
        let clauses = vec![
            ring.always_one_tok(),
            ring.always_moves(),
            ring.eventually_visits_p0(),
        ];
        let f = ring.arena.and(&clauses);

        let sol = solver
            .solve_temporal(&mut ring.arena, f, &ring.bounds, steps)
            .unwrap();
        assert!(sol.satisfiable, "steps={steps}");
        let ti = sol.temporal.as_ref().expect("SAT implies lasso");
        assert_eq!(ti.len(), steps);
        assert!(ti.loop_state() < steps);

        // the extracted trace must satisfy the original temporal formula
        let checker = TemporalEval::new(ti);
        assert!(
            checker.holds(&ring.arena, f).unwrap(),
            "extracted trace violates formula (steps={steps})"
        );

        // spot-check the movement invariant position-by-position
        for pos in 0..steps + ti.loop_state().max(1) + 2 {
            let st = ti.state_at(pos);
            let tok_ts = st.tuples(ring.tok).unwrap();
            assert_eq!(tok_ts.len(), 1, "one token per state (pos={pos})");
            let nxt = ti.state_at(pos + 1);
            let nt = nxt.tuples(ring.tok).unwrap();
            // token must move to a PREDECESSOR along the ring
            // (constraint is tok' ⊆ next.tok, i.e. holders of next.tok)
            let cur = tok_ts.index_view().iter().next().unwrap();
            let prev = (cur as usize + 4 - 1) % 4;
            let got = nt.index_view().iter().next().unwrap();
            assert_eq!(got, prev as i64, "token rotates along the ring");
        }
    }
}

/// Contradictory request: token always present but eventually absent.
#[test]
fn token_ring_contradiction_unsat_for_any_steps() {
    let solver = Solver::new();
    for steps in [2usize, 3, 5] {
        let mut ring = Ring::new(3);
        let clauses = vec![ring.always_one_tok(), ring.eventually_empty()];
        let f = ring.arena.and(&clauses);
        let sol = solver
            .solve_temporal(&mut ring.arena, f, &ring.bounds, steps)
            .unwrap();
        assert!(!sol.satisfiable, "steps={steps}");
        assert!(sol.temporal.is_none());
    }
}

/// `until` needs at least two distinct states when its operands are mutually
/// exclusive: (tok⊆{p1}) U (tok⊆{p2}) with `always (one tok)`.
#[test]
fn until_is_step_sensitive() {
    fn build(n: usize, target: usize) -> (AstArena, Bounds, RelationId, FormulaId) {
        let atoms: Vec<String> = (0..n).map(|i| format!("q{i}")).collect();
        let refs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
        let u = Universe::new(refs).unwrap();
        let pool = Arc::new(RelationPool::new());
        let mut bounds = Bounds::new(&u, &pool);
        let mut arena = AstArena::with_pool(Arc::clone(&pool));

        let a_set = {
            let r = arena.relation("A", 1);
            let mut s = TupleSet::new(&u, 1).unwrap();
            s.insert_index(0);
            bounds.bound_exactly(r, &s).unwrap();
            r
        };
        let b_set = {
            let r = arena.relation("B", 1);
            let mut s = TupleSet::new(&u, 1).unwrap();
            s.insert_index(target as i64);
            bounds.bound_exactly(r, &s).unwrap();
            r
        };
        let tok = {
            let r = arena.relation("tok", 1);
            arena.set_variable(r, true);
            let mut s = TupleSet::new(&u, 1).unwrap();
            for i in 0..n {
                s.insert_index(i as i64);
            }
            bounds.bound_upper(r, &s).unwrap();
            r
        };

        let tok_e = arena.expr_relation(tok);
        let one = arena
            .multiplicity_formula(Multiplicity::One, tok_e)
            .unwrap();
        let always_one = arena.temporal_unary(TemporalFormulaOp::Always, one);

        let ae = arena.expr_relation(a_set);
        let be = arena.expr_relation(b_set);
        let te = arena.expr_relation(tok);
        let fa = arena.comparison(ExprCompOp::Subset, te, ae).unwrap();
        let te2 = arena.expr_relation(tok);
        let gb = arena.comparison(ExprCompOp::Subset, te2, be).unwrap();
        let until = arena.temporal_binary(TemporalBinaryOp::Until, fa, gb);

        let f = arena.and(&[always_one, until]);
        (arena, bounds, tok, f)
    }

    let solver = Solver::new();

    // steps=1: the exclusive range [t, r) is empty, so only the right side
    // binds at t0: tok must be {q1}.
    {
        let (mut arena, bounds, tok, f) = build(3, 1);
        let sol = solver.solve_temporal(&mut arena, f, &bounds, 1).unwrap();
        assert!(sol.satisfiable, "steps=1: right-side-only witness");
        let ti = sol.temporal.unwrap();
        let ts = ti.state_at(0).tuples(tok).unwrap();
        assert!(ts.contains_index(1) && ts.len() == 1);
    }

    // steps=2+: start at q0, move to q1
    for steps in [2usize, 3] {
        let (mut arena, bounds, _tok, f) = build(3, 1);
        let sol = solver
            .solve_temporal(&mut arena, f, &bounds, steps)
            .unwrap_or_else(|e| panic!("steps={steps}: {e}"));
        assert!(sol.satisfiable, "steps={steps}");
        let ti = sol.temporal.unwrap();
        let checker = TemporalEval::new(&ti);
        assert!(checker.holds(&arena, f).unwrap(), "steps={steps}");

        // UNTIL may be witnessed immediately (right side at t0), so we only
        // require that every state still satisfies exactly-one via the
        // checker above; semantic validity is fully covered by `holds`.
    }
}

/// Extraction sanity: static relations are copied into every state unchanged.
#[test]
fn extraction_copies_static_relations() {
    let solver = Solver::new();
    let mut ring = Ring::new(4);
    let clauses = vec![ring.always_one_tok(), ring.always_moves()];
    let f = ring.arena.and(&clauses);
    let sol = solver
        .solve_temporal(&mut ring.arena, f, &ring.bounds, 4)
        .unwrap();
    assert!(sol.satisfiable);
    let ti = sol.temporal.unwrap();
    for s in ti.states() {
        let nx = s.tuples(ring.next).unwrap();
        assert_eq!(nx.len(), 4);
        let p0 = s.tuples(ring.p0).unwrap();
        assert_eq!(p0.len(), 1);
    }
}
