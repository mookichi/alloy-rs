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
        self.rel(name, arity, flat, flat)
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

    fn leaf(&mut self, r: RelationId) -> ExprId {
        self.arena.expr_relation(r)
    }

    fn some_rel(&mut self, r: RelationId) -> FormulaId {
        let e = self.leaf(r);
        self.arena
            .multiplicity_formula(Multiplicity::Some, e)
            .unwrap()
    }

    fn eq(&mut self, a: ExprId, b: ExprId) -> FormulaId {
        self.arena.comparison(ExprCompOp::Equals, a, b).unwrap()
    }

    fn subset(&mut self, a: ExprId, b: ExprId) -> FormulaId {
        self.arena.comparison(ExprCompOp::Subset, a, b).unwrap()
    }

    fn sat(&mut self, f: FormulaId) -> bool {
        let mut translator = FolTranslator::new(BoolCtx::new(), &self.bounds);
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
fn some_on_exact_bounds() {
    let mut m = Model::new(&["n0", "n1"]);
    let p = m.rel_exact("p", 1, &["n0"]);
    let f_h = m.some_rel(p);
    assert!(m.sat(f_h));

    let mut m = Model::new(&["n0", "n1"]);
    let p = m.rel_exact("empty_p", 1, &[]);
    let f_h = m.some_rel(p);
    assert!(!m.sat(f_h));
}

#[test]
fn equality_of_relations() {
    let mut m = Model::new(&["n0", "n1"]);
    let (r, s) = (
        m.rel_exact("r", 2, &["n0", "n1"]),
        m.rel_exact("s", 2, &["n0", "n1"]),
    );
    let (er, es) = (m.leaf(r), m.leaf(s));
    let f_h = m.eq(er, es);
    assert!(m.sat(f_h));

    let mut m = Model::new(&["n0", "n1"]);
    let (r, s) = (
        m.rel_exact("r", 2, &["n0", "n1"]),
        m.rel_exact("s", 2, &["n1", "n0"]),
    );
    let (er, es) = (m.leaf(r), m.leaf(s));
    let f_h = m.eq(er, es);
    assert!(!m.sat(f_h));
}

#[test]
fn subset_constraint_drives_choice() {
    let mut m = Model::new(&["n0", "n1"]);
    let r = m.rel_exact("r", 1, &["n0"]);
    let p = m.rel("p", 1, &["n0", "n1"], &[]);
    let (ep, er) = (m.leaf(p), m.leaf(r));
    let f_h = m.subset(ep, er);
    assert!(m.sat(f_h));
}

fn lone_over_next(free_choice: bool) -> bool {
    let mut m = Model::new(&["n0", "n1", "n2"]);
    let node = m.rel_exact("Node", 1, &["n0", "n1", "n2"]);
    let next = if free_choice {
        m.rel("next", 2, &["n0", "n1", "n0", "n2"], &[])
    } else {
        m.rel_exact("next", 2, &["n0", "n1", "n0", "n2"])
    };
    let x = m.arena.variable("x");
    let en0 = next;
    let ex_node = m.leaf(node);
    let d = m.arena.decl(x, Multiplicity::One, ex_node).unwrap();
    let ds = m.arena.add_decls(vec![d]);
    let vx = m.arena.expr_variable(x);
    let en = m.leaf(en0);
    let j = m.arena.binary_expr(BinaryOp::Join, vx, en).unwrap();
    let body = m.arena.multiplicity_formula(Multiplicity::Lone, j).unwrap();
    let f_h = m.arena.quantified(Quantifier::All, ds, body);
    m.sat(f_h)
}

#[test]
fn lone_multiplicity_over_join() {
    assert!(!lone_over_next(false), "two forced out-edges violate lone");
    assert!(lone_over_next(true), "free choice keeps functionality");
}

#[test]
fn one_multiplicity_cardinality() {
    let mut m = Model::new(&["n0", "n1"]);
    let p = m.rel_exact("p", 1, &["n0"]);
    let ep = m.leaf(p);
    let f = m.arena.multiplicity_formula(Multiplicity::One, ep).unwrap();
    assert!(m.sat(f));

    let mut m = Model::new(&["n0", "n1"]);
    let p = m.rel_exact("p", 1, &["n0", "n1"]);
    let ep = m.leaf(p);
    let f = m.arena.multiplicity_formula(Multiplicity::One, ep).unwrap();
    assert!(!m.sat(f));
}

#[test]
fn join_some_reachability() {
    for (tuples, expect) in [(&["n0", "n2"][..], true), (&[][..], false)] {
        let mut m = Model::new(&["n0", "n1", "n2"]);
        let node = m.rel_exact("Node", 1, &["n0", "n1", "n2"]);
        let friend = m.rel_exact("friend", 2, tuples);
        let en = m.leaf(node);
        let ef = m.leaf(friend);
        let j = m.arena.binary_expr(BinaryOp::Join, en, ef).unwrap();
        let f = m.arena.multiplicity_formula(Multiplicity::Some, j).unwrap();
        assert_eq!(m.sat(f), expect);
    }
}

#[test]
fn transitive_closure_reachability() {
    for (target, expect) in [("n2", true), ("n3", false)] {
        let mut m = Model::new(&["n0", "n1", "n2", "n3"]);
        let a0 = m.rel_exact("A0", 1, &["n0"]);
        let at = m.rel_exact("AT", 1, &[target]);
        let edge = m.rel_exact("edge", 2, &["n0", "n1", "n1", "n2"]);
        let e_edge = m.leaf(edge);
        let pow = m.arena.unary_expr(UnaryExprOp::Closure, e_edge).unwrap();
        let e_a0 = m.leaf(a0);
        let e_at = m.leaf(at);
        let pair = m.arena.binary_expr(BinaryOp::Product, e_a0, e_at).unwrap();
        let f = m.subset(pair, pow);
        assert_eq!(m.sat(f), expect, "target {}", target);
    }
}

#[test]
fn reflexive_closure_admits_empty_graph() {
    let mut m = Model::new(&["n0"]);
    let a0 = m.rel_exact("A0", 1, &["n0"]);
    let edge = m.rel_exact("edge", 2, &[]);
    let e_edge = m.leaf(edge);
    let star = m
        .arena
        .unary_expr(UnaryExprOp::ReflexiveClosure, e_edge)
        .unwrap();
    let e_a0 = m.leaf(a0);
    let pair = m.arena.binary_expr(BinaryOp::Product, e_a0, e_a0).unwrap();
    let f_h = m.subset(pair, star);
    assert!(m.sat(f_h));
}

#[test]
fn iden_subset_and_intersection_with_none() {
    let mut m = Model::new(&["n0", "n1"]);
    let next = m.rel(
        "next",
        2,
        &["n0", "n0", "n0", "n1", "n1", "n0", "n1", "n1"],
        &[],
    );
    let e_iden = m.arena.iden();
    let e_next = m.leaf(next);
    let f = m.subset(e_iden, e_next);
    assert!(m.sat(f), "diagonal selectable");

    let mut m = Model::new(&["n0", "n1"]);
    let next = m.rel_exact("next", 2, &["n0", "n1", "n1", "n0"]);
    let empty = m.rel_exact("E", 2, &[]);
    let e_next = m.leaf(next);
    let e_iden = m.arena.iden();
    let inter = m
        .arena
        .binary_expr(BinaryOp::Intersection, e_next, e_iden)
        .unwrap();
    let e_empty = m.leaf(empty);
    let f = m.eq(inter, e_empty);
    assert!(m.sat(f), "off-diagonal choice keeps intersection empty");
}

#[test]
fn difference_and_override_equalities() {
    let mut m = Model::new(&["n0", "n1", "n2"]);
    let r = m.rel_exact("r", 2, &["n0", "n1", "n1", "n2"]);
    let s = m.rel_exact("s", 2, &["n1", "n2"]);
    let p01 = m.rel_exact("P01", 2, &["n0", "n1"]);
    let e_r = m.leaf(r);
    let e_s = m.leaf(s);
    let diff = m.arena.binary_expr(BinaryOp::Difference, e_r, e_s).unwrap();
    let e_p01 = m.leaf(p01);
    let f_h = m.eq(diff, e_p01);
    assert!(m.sat(f_h));

    for (target, expect) in [("P02", true), ("P01", false)] {
        let mut m = Model::new(&["n0", "n1", "n2"]);
        let s = m.rel_exact("s", 2, &["n0", "n1"]);
        let o = m.rel_exact("o", 2, &["n0", "n2"]);
        let tgt = m.rel_exact(
            target,
            2,
            if target == "P02" {
                &["n0", "n2"]
            } else {
                &["n0", "n1"]
            },
        );
        let e_s = m.leaf(s);
        let e_o = m.leaf(o);
        let ovr = m.arena.binary_expr(BinaryOp::Override, e_s, e_o).unwrap();
        let e_tgt = m.leaf(tgt);
        let f_h = m.eq(ovr, e_tgt);
        assert_eq!(m.sat(f_h), expect, "override vs {}", target);
    }
}

#[test]
fn two_var_quantifier_forces_full_product() {
    let all4: Vec<&str> = vec![
        "n0", "n0", "n0", "n1", "n0", "n2", "n0", "n3", "n1", "n0", "n1", "n1", "n1", "n2", "n1",
        "n3", "n2", "n0", "n2", "n1", "n2", "n2", "n2", "n3", "n3", "n0", "n3", "n1", "n3", "n2",
        "n3", "n3",
    ];
    let missing_one: Vec<&str> = all4[..30].to_vec();

    for (name, pairs, expect) in [
        ("full", all4.as_slice(), true),
        ("missing", missing_one.as_slice(), false),
    ] {
        let mut m = Model::new(&["n0", "n1", "n2", "n3"]);
        let node = m.rel_exact("Node", 1, &["n0", "n1", "n2", "n3"]);
        let r = m.rel_exact(name, 2, pairs);
        let (x, y) = (m.arena.variable("x"), m.arena.variable("y"));
        let e_node = m.leaf(node);
        let dx = m.arena.decl(x, Multiplicity::One, e_node).unwrap();
        let e_node2 = m.leaf(node);
        let dy = m.arena.decl(y, Multiplicity::One, e_node2).unwrap();
        let ds = m.arena.add_decls(vec![dx, dy]);
        let ex = m.arena.expr_variable(x);
        let ey = m.arena.expr_variable(y);
        let prod = m.arena.binary_expr(BinaryOp::Product, ex, ey).unwrap();
        let e_r = m.leaf(r);
        let body = m.subset(prod, e_r);
        let f = m.arena.quantified(Quantifier::All, ds, body);
        assert_eq!(m.sat(f), expect, "case {}", name);
    }
}

#[test]
fn comprehension_domain_matches_filter() {
    for (hset, expect) in [(&["n0", "n2"][..], true), (&["n0"][..], false)] {
        let mut m = Model::new(&["n0", "n1", "n2", "n3"]);
        let node = m.rel_exact("Node", 1, &["n0", "n1", "n2", "n3"]);
        let q = m.rel_exact("q", 2, &["n0", "n1", "n2", "n3"]);
        let h = m.rel_exact("H", 1, hset);
        let x = m.arena.variable("x");
        let e_node = m.leaf(node);
        let dx = m.arena.decl(x, Multiplicity::One, e_node).unwrap();
        let ds = m.arena.add_decls(vec![dx]);
        let ex = m.arena.expr_variable(x);
        let eq_ = m.leaf(q);
        let jq = m.arena.binary_expr(BinaryOp::Join, ex, eq_).unwrap();
        let cond = m
            .arena
            .multiplicity_formula(Multiplicity::Some, jq)
            .unwrap();
        let comp = m.arena.comprehension(ds, cond).unwrap();
        let e_h = m.leaf(h);
        let f = m.eq(comp, e_h);
        assert_eq!(m.sat(f), expect);
    }
}

#[test]
fn if_expression_selects_branch_by_condition() {
    let mut m = Model::new(&["n0", "n1"]);
    let q = m.rel_exact("q", 1, &[]);
    let p = m.rel_exact("p", 2, &["n0", "n1"]);
    let r = m.rel_exact("r", 2, &["n1", "n0"]);
    let cond = m.some_rel(q);
    let ep = m.leaf(p);
    let er = m.leaf(r);
    let ite = m.arena.if_expr(cond, ep, er).unwrap();
    let er2 = m.leaf(r);
    let f = m.eq(ite, er2);
    assert!(m.sat(f), "empty condition selects else branch");

    let mut m = Model::new(&["n0", "n1"]);
    let q = m.rel_exact("q", 1, &["n0"]);
    let p = m.rel_exact("p", 2, &["n0", "n1"]);
    let r = m.rel_exact("r", 2, &["n1", "n0"]);
    let cond = m.some_rel(q);
    let ep = m.leaf(p);
    let er = m.leaf(r);
    let ite = m.arena.if_expr(cond, ep, er).unwrap();
    let er2 = m.leaf(r);
    let f = m.eq(ite, er2);
    assert!(!m.sat(f), "non-empty condition forces then branch");
}

#[test]
fn all_over_free_relation_gates_body_by_membership() {
    let mut m = Model::new(&["n0", "n1"]);
    let p_free = m.rel("p", 1, &["n0", "n1"], &[]);
    let p_full = m.rel_exact("pf", 1, &["n0", "n1"]);
    let n0 = m.rel_exact("n0", 1, &["n0"]);

    let build = |m: &mut Model, p: RelationId| -> FormulaId {
        let x = m.arena.variable("x");
        let ep = m.leaf(p);
        let d = m.arena.decl(x, Multiplicity::One, ep).unwrap();
        let ds = m.arena.add_decls(vec![d]);
        let vx = m.arena.expr_variable(x);
        let en0 = m.leaf(n0);
        let body = m.subset(vx, en0);
        m.arena.quantified(Quantifier::All, ds, body)
    };

    let f_free = build(&mut m, p_free);
    assert!(
        m.sat(f_free),
        "solver may exclude n1 from p, making the implication vacuous"
    );

    let f_full = build(&mut m, p_full);
    assert!(
        !m.sat(f_full),
        "with p exact, n1 is a member and cannot equal n0"
    );
}
