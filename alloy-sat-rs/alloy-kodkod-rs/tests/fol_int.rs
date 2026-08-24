use alloy_kodkod_rs::ast::*;
use alloy_kodkod_rs::bounds::Bounds;
use alloy_kodkod_rs::cnf::translate_into_solver;
use alloy_kodkod_rs::fol::FolTranslator;
use alloy_kodkod_rs::relation::{RelationId, RelationPool};
use alloy_kodkod_rs::sat::{RecordingSolver, SatSolver};
use alloy_kodkod_rs::tuple::Tuple;
use alloy_kodkod_rs::tupleset::TupleSet;
use alloy_kodkod_rs::universe::Universe;
use alloy_kodkod_rs::BoolCtx;
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

    fn bind_int(&mut self, value: i64, flat: &[&str]) {
        let mut s = TupleSet::new(&self.u, 1).unwrap();
        for a in flat {
            let t = Tuple::from_atoms(&self.u, &[a]).unwrap();
            s.insert(&t).unwrap();
        }
        self.bounds.bound_exactly_int(value, &s).unwrap();
    }

    fn int_const(&mut self, v: i64) -> IntId {
        self.arena.int_constant(v)
    }

    fn leaf(&mut self, r: RelationId) -> ExprId {
        self.arena.expr_relation(r)
    }

    fn card(&mut self, r: RelationId) -> IntId {
        let e = self.leaf(r);
        self.arena.cast_to_int(CastToIntOp::Cardinality, e).unwrap()
    }

    fn sum_rel(&mut self, r: RelationId) -> Result<IntId, ()> {
        let e = self.leaf(r);
        self.arena.cast_to_int(CastToIntOp::Sum, e).map_err(|_| ())
    }

    fn icmp_eq(&mut self, l: IntId, r: IntId) -> FormulaId {
        self.arena.int_comparison(IntCompOp::Eq, l, r)
    }

    fn icmp(&mut self, op: IntCompOp, l: IntId, r: IntId) -> FormulaId {
        self.arena.int_comparison(op, l, r)
    }

    fn sat(&mut self, f: FormulaId) -> bool {
        let mut translator = FolTranslator::new(BoolCtx::new(), &self.bounds);
        translator.set_bitwidth(6);
        let root = translator.formula_ref(&self.arena, f, &[]).unwrap();
        let max_primary = translator.ctx.num_slots();
        let ctx = translator.ctx.clone();
        let mut solver = RecordingSolver::new();
        ctx.with_factory(|factory| translate_into_solver(&mut solver, factory, root, max_primary))
            .unwrap();
        SatSolver::solve(&mut solver)
    }
}

#[test]
fn cardinality_equality() {
    let mut m = Model::new(&["n0", "n1", "n2"]);
    let p = m.rel_exact("p", 1, &["n0"]);
    let cp = m.card(p);
    let one = m.int_const(1);
    let f_h = m.icmp_eq(cp, one);
    assert!(m.sat(f_h));

    let mut m = Model::new(&["n0", "n1", "n2"]);
    let p = m.rel_exact("p", 1, &["n0", "n1"]);
    let cp = m.card(p);
    let one = m.int_const(1);
    let f_h = m.icmp_eq(cp, one);
    assert!(!m.sat(f_h));
}

#[test]
fn cardinality_addition() {
    let mut m = Model::new(&["n0", "n1", "n2"]);
    let p = m.rel_exact("p", 1, &["n0"]);
    let q = m.rel_exact("q", 1, &["n1", "n2"]);
    let cp = m.card(p);
    let cq = m.card(q);
    let three = m.int_const(3);
    let sum = m.arena.binary_int(IntBinOp::Plus, cp, cq);
    let f_h = m.icmp_eq(sum, three);
    assert!(m.sat(f_h));

    let cp2 = m.card(p);
    let cq2 = m.card(q);
    let sum2 = m.arena.binary_int(IntBinOp::Plus, cp2, cq2);
    let four = m.int_const(4);
    let f_h = m.icmp_eq(sum2, four);
    assert!(!m.sat(f_h));
}

#[test]
fn cardinality_ordering() {
    for (psize, qsize, op, expect) in [
        (&["n0"][..], &["n1", "n2"][..], IntCompOp::Lt, true),
        (&["n0", "n1"][..], &["n2"][..], IntCompOp::Lt, false),
        (&["n0", "n1"][..], &["n2", "n3"][..], IntCompOp::Lte, true),
    ] {
        let mut m = Model::new(&["n0", "n1", "n2", "n3"]);
        let p = m.rel_exact("p", 1, psize);
        let q = m.rel_exact("q", 1, qsize);
        let cp = m.card(p);
        let cq = m.card(q);
        let f = m.icmp(op, cp, cq);
        assert_eq!(m.sat(f), expect);
    }
}

#[test]
fn sum_over_intbounds_relation() {
    for (target, expect) in [(7i64, true), (6, true), (8, false)] {
        let mut m = Model::new(&["n0", "n1", "n2", "n3"]);
        // upper bound {n0,n1,n2}, empty lower
        let rr = m.arena.relation("r", 1);
        let up = {
            let mut s = TupleSet::new(&m.u, 1).unwrap();
            for a in ["n0", "n1", "n2"] {
                let t = Tuple::from_atoms(&m.u, &[a]).unwrap();
                s.insert(&t).unwrap();
            }
            s
        };
        m.bounds.bound_upper(rr, &up).unwrap();
        m.bind_int(1, &["n0"]);
        m.bind_int(2, &["n1"]);
        m.bind_int(4, &["n2"]);

        let sum_cast = m.sum_rel(rr).unwrap();
        let t = m.int_const(target);
        let f = m.icmp_eq(sum_cast, t);
        assert_eq!(m.sat(f), expect, "sum target {}", target);
    }
}

#[test]
fn from_int_uses_integer_bounds_atoms() {
    let mut m = Model::new(&["n0", "n1", "n2"]);
    m.bind_int(2, &["n2"]);
    let a2 = m.rel_exact("A2", 1, &["n2"]);
    let a1 = m.rel_exact("A1", 1, &["n1"]);

    let i2 = m.int_const(2);
    let two_expr = m.arena.from_int(i2);
    let eb = m.leaf(a2);
    let f_ok = m
        .arena
        .comparison(ExprCompOp::Equals, two_expr, eb)
        .unwrap();
    assert!(m.sat(f_ok));

    let i2 = m.int_const(2);
    let two_expr = m.arena.from_int(i2);
    let eb = m.leaf(a1);
    let f_bad = m
        .arena
        .comparison(ExprCompOp::Equals, two_expr, eb)
        .unwrap();
    assert!(!m.sat(f_bad));
}

#[test]
fn sum_over_decls_multiplies_constant() {
    let mut m = Model::new(&["n0", "n1"]);
    let node = m.rel_exact("Node", 1, &["n0", "n1"]);
    let x = m.arena.variable("x");
    let e_node = m.leaf(node);
    let d = m.arena.decl(x, Multiplicity::One, e_node).unwrap();
    let ds = m.arena.add_decls(vec![d]);
    let two = m.int_const(2);
    let total = m.arena.sum_int(ds, two);

    for (target, expect) in [(4i64, true), (5, false)] {
        let t = m.int_const(target);
        let f = m.icmp_eq(total, t);
        assert_eq!(m.sat(f), expect, "decl-sum target {}", target);
    }
}

#[test]
fn division_and_modulo_formulas() {
    let mut m = Model::new(&["n0", "n1", "n2"]);
    let p = m.rel_exact("p", 1, &["n0", "n1", "n2"]);
    let card = m.card(p);
    let two = m.int_const(2);
    let one = m.int_const(1);
    let dq = m.arena.binary_int(IntBinOp::Divide, card, two);
    let dr = m.arena.binary_int(IntBinOp::Modulo, card, two);
    let f_h = m.icmp_eq(dq, one);
    assert!(m.sat(f_h));
    let _ = dr;

    let mut m = Model::new(&["n0", "n1", "n2"]);
    let p = m.rel_exact("p", 1, &["n0", "n1", "n2"]);
    let card = m.card(p);
    let two = m.int_const(2);
    let one = m.int_const(1);
    let dr = m.arena.binary_int(IntBinOp::Modulo, card, two);
    let f_h = m.icmp_eq(dr, one);
    assert!(m.sat(f_h));

    let mut m = Model::new(&["n0", "n1", "n2"]);
    let p = m.rel_exact("p", 1, &["n0", "n1"]);
    let card = m.card(p);
    let two = m.int_const(2);
    let zero = m.int_const(0);
    let dr = m.arena.binary_int(IntBinOp::Modulo, card, two);
    let f_h = m.icmp_eq(dr, zero);
    assert!(m.sat(f_h));
}
