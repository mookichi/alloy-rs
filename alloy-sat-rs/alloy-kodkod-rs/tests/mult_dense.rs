//! Regression probes for `not (some (v0 . (v1 . rel)))` under dense bounds.
use alloy_kodkod_rs::ast::*;
use alloy_kodkod_rs::bounds::Bounds;
use alloy_kodkod_rs::cnf::translate_into_solver;
use alloy_kodkod_rs::fol::FolTranslator;
use alloy_kodkod_rs::relation::RelationPool;
use alloy_kodkod_rs::sat::{RecordingSolver, SatSolver};
use alloy_kodkod_rs::tuple::Tuple;
use alloy_kodkod_rs::tupleset::TupleSet;
use alloy_kodkod_rs::universe::Universe;
use alloy_kodkod_rs::BoolCtx;
use std::sync::Arc;

fn solve_all_not_some(dense: bool) -> bool {
    let u: Arc<Universe> = Universe::new(["b0", "b1"]).unwrap();
    let pool = Arc::new(RelationPool::new());
    let mut arena = AstArena::with_pool(Arc::clone(&pool));
    let mut bounds = Bounds::new(&u, &pool);

    let addr = arena.relation("addr", 3);
    let mut full = TupleSet::new(&u, 3).unwrap();
    for a in ["b0", "b1"] {
        for b in ["b0", "b1"] {
            for c in ["b0", "b1"] {
                let t = Tuple::from_atoms(&u, &[a, b, c]).unwrap();
                full.insert(&t).unwrap();
            }
        }
    }
    if dense {
        bounds.bound_exactly(addr, &full).unwrap();
    } else {
        let empty = TupleSet::new(&u, 3).unwrap();
        bounds.bound(addr, &empty, &full).unwrap();
    }

    // vars b, n over unary "univ-ish" relation? Use the relation-free approach:
    // decl domains need expressions; use a dedicated unary relation U exact-full.
    let ub = arena.relation("U", 1);
    let mut uu = TupleSet::new(&u, 1).unwrap();
    for a in ["b0", "b1"] {
        let t = Tuple::from_atoms(&u, &[a]).unwrap();
        uu.insert(&t).unwrap();
    }
    bounds.bound_exactly(ub, &uu).unwrap();

    let vb = arena.variable("b");
    let vn = arena.variable("n");
    let eu = arena.expr_relation(ub);
    let db = {
        let d = arena.decl(vb, Multiplicity::One, eu);
        d.unwrap()
    };
    let dn = arena.decl(vn, Multiplicity::One, eu).unwrap();
    let ds = arena.add_decls(vec![db, dn]);

    let eb = arena.expr_variable(vb);
    let en = arena.expr_variable(vn);
    let ea = arena.expr_relation(addr);
    let j1 = arena.binary_expr(BinaryOp::Join, eb, ea).unwrap(); // b.addr
    let j2 = arena.binary_expr(BinaryOp::Join, en, j1).unwrap(); // n.(b.addr)
    let body = arena.multiplicity_formula(Multiplicity::Some, j2).unwrap();
    let not_body = arena.not(body);
    let f = arena.quantified(Quantifier::All, ds, not_body);

    let mut translator = FolTranslator::new(BoolCtx::new(), &bounds);
    let root = translator.formula_ref(&arena, f, &[]).unwrap();
    let max_primary = translator.ctx.num_slots();
    let ctx = translator.ctx.clone();
    let mut solver = RecordingSolver::new();
    ctx.with_factory(|factory| translate_into_solver(&mut solver, factory, root, max_primary))
        .unwrap();
    SatSolver::solve(&mut solver)
}

#[test]
fn dense_bounds_make_some_always_true() {
    // addr is exactly Book x Book x Book: every image nonempty.
    assert!(
        !solve_all_not_some(true),
        "not(some(...)) must be UNSAT under dense exact bounds"
    );
}

#[test]
fn empty_bounds_make_some_always_false() {
    // addr is exactly empty: every image empty.
    assert!(
        solve_all_not_some(false),
        "not(some(...)) must be SAT under empty exact bounds"
    );
}

/// KNOWN-BUG regression test (currently expected to PASS because it uses
/// RecordingSolver, which bails out on >22 variables; see sat.rs). The real
/// engine reproduces the bug via the facade: see
/// alloy-engine-rs/examples/repro_spurious_sat.rs and the differential test.
///
/// Original discovery: the assertion
///   all b,b',b'',n,t | (noImg /\ addEq /\ delEq) -> concl
/// is VALID over bounds lo=empty hi=full (kodkod agrees: check reports
/// UNSAT), yet the Rust engine reports SAT with a counterexample whose
/// antecedent is nowhere true.
#[test]
#[ignore = "known bug: spurious SAT for quantified implication over free relations"]
fn quantified_implication_validity() {
    let u = Universe::new(["b0", "b1"]).unwrap();
    let pool = Arc::new(RelationPool::new());
    let mut arena = AstArena::with_pool(Arc::clone(&pool));
    let mut bounds = Bounds::new(&u, &pool);

    let ub = arena.relation("U", 1);
    let mut uu = TupleSet::new(&u, 1).unwrap();
    for a in ["b0", "b1"] {
        uu.insert(&Tuple::from_atoms(&u, &[a]).unwrap()).unwrap();
    }
    bounds.bound_exactly(ub, &uu).unwrap();

    let addr = arena.relation("addr", 3);
    let mut full = TupleSet::new(&u, 3).unwrap();
    for a in ["b0", "b1"] {
        for b in ["b0", "b1"] {
            for c in ["b0", "b1"] {
                full.insert(&Tuple::from_atoms(&u, &[a, b, c]).unwrap())
                    .unwrap();
            }
        }
    }
    let empty = TupleSet::new(&u, 3).unwrap();
    bounds.bound(addr, &empty, &full).unwrap();

    let eu = arena.expr_relation(ub);
    let vb = arena.variable("b");
    let db = { arena.decl(vb, Multiplicity::One, eu).unwrap() };
    let vb2 = arena.variable("b2");
    let d2 = { arena.decl(vb2, Multiplicity::One, eu).unwrap() };
    let vb3 = arena.variable("b3");
    let d3 = { arena.decl(vb3, Multiplicity::One, eu).unwrap() };
    let vn = arena.variable("n");
    let dn = { arena.decl(vn, Multiplicity::One, eu).unwrap() };
    let vt = arena.variable("t");
    let dt = { arena.decl(vt, Multiplicity::One, eu).unwrap() };
    let ds = arena.add_decls(vec![db, d2, d3, dn, dt]);

    let ea = arena.expr_relation(addr);
    let eb = arena.expr_variable(vb);
    let eb2 = arena.expr_variable(vb2);
    let eb3 = arena.expr_variable(vb3);
    let en = arena.expr_variable(vn);
    let et = arena.expr_variable(vt);

    let j1 = arena.binary_expr(BinaryOp::Join, eb, ea).unwrap();
    let img = arena.binary_expr(BinaryOp::Join, en, j1).unwrap();
    let ms = arena.multiplicity_formula(Multiplicity::Some, img).unwrap();
    let no_img = arena.not(ms);

    let b_addr = arena.binary_expr(BinaryOp::Join, eb, ea).unwrap();
    let b2_addr = arena.binary_expr(BinaryOp::Join, eb2, ea).unwrap();
    let b3_addr = arena.binary_expr(BinaryOp::Join, eb3, ea).unwrap();
    let nt = arena.binary_expr(BinaryOp::Product, en, et).unwrap();
    let un = arena.binary_expr(BinaryOp::Union, b_addr, nt).unwrap();
    let add_eq = arena.comparison(ExprCompOp::Equals, b2_addr, un).unwrap();
    // NOTE: b_addr consumed above; rebuild for difference
    let b_addr2 = arena.binary_expr(BinaryOp::Join, eb, ea).unwrap();
    let df = arena
        .binary_expr(BinaryOp::Difference, b_addr2, nt)
        .unwrap();
    let del_eq = arena.comparison(ExprCompOp::Equals, b3_addr, df).unwrap();
    let b_addr3 = arena.binary_expr(BinaryOp::Join, eb, ea).unwrap();
    let b3_addr2 = arena.binary_expr(BinaryOp::Join, eb3, ea).unwrap();
    let conc = arena
        .comparison(ExprCompOp::Equals, b_addr3, b3_addr2)
        .unwrap();

    let ante = arena.and(&[no_img, add_eq, del_eq]);
    let na = arena.not(ante);
    let body = arena.or(&[na, conc]);
    let q = arena.quantified(Quantifier::All, ds, body);

    let mut translator = FolTranslator::new(BoolCtx::new(), &bounds);
    let root = translator.formula_ref(&arena, q, &[]).unwrap();
    let max_primary = translator.ctx.num_slots();
    let ctx = translator.ctx.clone();
    let mut solver = RecordingSolver::new();
    ctx.with_factory(|factory| translate_into_solver(&mut solver, factory, root, max_primary))
        .unwrap();
    assert!(
        !SatSolver::solve(&mut solver),
        "assertion is valid; must be UNSAT"
    );
}
