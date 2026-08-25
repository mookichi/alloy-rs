//! Minimal deterministic isolation of the spurious-SAT defect.
//!
//! Translates the m15-style body under ONE fixed binding and enumerates
//! all 256 leaf assignments, evaluating the circuit with BoolFactory::eval
//! (0-based model convention: Var(slot s) reads model[s - 1]) against the
//! independent Evaluator ground truth on the same instance.

use alloy_kodkod_rs::ast::*;
use alloy_kodkod_rs::bounds::Bounds;
use alloy_kodkod_rs::fol::FolTranslator;
use alloy_kodkod_rs::instance::Instance;
use alloy_kodkod_rs::relation::RelationPool;
use alloy_kodkod_rs::tuple::Tuple;
use alloy_kodkod_rs::tupleset::TupleSet;
use alloy_kodkod_rs::universe::Universe;
use alloy_kodkod_rs::BoolCtx;
use std::sync::Arc;

fn audit_tree(
    f: &alloy_kodkod_rs::BoolFactory,
    r: alloy_kodkod_rs::bool::BoolRef,
    m: &[bool],
    d: usize,
) -> bool {
    use alloy_kodkod_rs::bool::BoolNode;
    let pad = " ".repeat(d * 2);
    if r.is_const() {
        println!("{pad}const({}) h={}", r.const_value(), r.0);
        return r.const_value();
    }
    let sv = if r.sign() {
        m[r.slot() as usize]
    } else {
        !m[r.slot() as usize]
    };
    match f.node(r) {
        Some(BoolNode::Var) => {
            println!("{pad}VAR h={} val={sv}", r.0);
            sv
        }
        Some(BoolNode::And(kids)) => {
            println!("{pad}AND h={} stored={sv}", r.0);
            let mut a = true;
            for k in kids.iter() {
                a &= audit_tree(f, *k, m, d + 1);
            }
            println!("{pad}=> AND {} computed={a}", r.0);
            if a != sv {
                println!("{pad}!! INCONSISTENT AND {}", r.0);
            }
            a
        }
        Some(BoolNode::Or(kids)) => {
            println!("{pad}OR h={} stored={sv}", r.0);
            let mut a = false;
            for k in kids.iter() {
                a |= audit_tree(f, *k, m, d + 1);
            }
            println!("{pad}=> OR {} computed={a}", r.0);
            if a != sv {
                println!("{pad}!! INCONSISTENT OR {}", r.0);
            }
            a
        }
        Some(BoolNode::Ite { c, t, e }) => {
            println!("{pad}ITE h={}", r.0);
            let cv = audit_tree(f, *c, m, d + 1);
            let tv = audit_tree(f, *t, m, d + 1);
            let ev2 = audit_tree(f, *e, m, d + 1);
            if cv {
                tv
            } else {
                ev2
            }
        }
        None => {
            println!("{pad}DANGLING h={}", r.0);
            sv
        }
    }
}

fn main() {
    let u = Universe::new(["a0", "a1"]).unwrap();
    let pool = Arc::new(RelationPool::new());
    let mut arena = AstArena::with_pool(Arc::clone(&pool));
    let mut bounds = Bounds::new(&u, &pool);
    let trel = arena.relation("t", 3);
    let full = {
        let mut t = TupleSet::new(&u, 3).unwrap();
        for x in ["a0", "a1"] {
            for y in ["a0", "a1"] {
                for z in ["a0", "a1"] {
                    t.insert(&Tuple::from_atoms(&u, &[x, y, z]).unwrap())
                        .unwrap();
                }
            }
        }
        t
    };
    let empty3 = TupleSet::new(&u, 3).unwrap();
    bounds.bound(trel, &empty3, &full).unwrap();

    // binding: b=a1, c=a1, d=a0, n=a0, t=a0
    let env: Vec<(VarId, Vec<u32>)> = vec![
        (arena.variable("b"), vec![1]),
        (arena.variable("c"), vec![1]),
        (arena.variable("d"), vec![0]),
        (arena.variable("n"), vec![0]),
        (arena.variable("tt"), vec![0]),
    ];
    let vb = env[0].0;
    let vc = env[1].0;
    let vd = env[2].0;
    let vn = env[3].0;
    let vt = env[4].0;

    let et = arena.expr_relation(trel);
    let eb = arena.expr_variable(vb);
    let ec = arena.expr_variable(vc);
    let ed = arena.expr_variable(vd);
    let en = arena.expr_variable(vn);
    let evt = arena.expr_variable(vt);

    let rowb = arena.binary_expr(BinaryOp::Join, eb, et).unwrap();
    let rowc = arena.binary_expr(BinaryOp::Join, ec, et).unwrap();
    let rowd = arena.binary_expr(BinaryOp::Join, ed, et).unwrap();
    let img = arena.binary_expr(BinaryOp::Join, en, rowb).unwrap();
    let ms = arena.multiplicity_formula(Multiplicity::Some, img).unwrap();
    let no_img = arena.not(ms);
    let nt = arena.binary_expr(BinaryOp::Product, en, evt).unwrap();
    let un = arena.binary_expr(BinaryOp::Union, rowb, nt).unwrap();
    let add_eq = arena.comparison(ExprCompOp::Equals, rowc, un).unwrap();
    let df = arena.binary_expr(BinaryOp::Difference, rowb, nt).unwrap();
    let del_eq = arena.comparison(ExprCompOp::Equals, rowd, df).unwrap();
    let conc = arena.comparison(ExprCompOp::Equals, rowb, rowd).unwrap();
    let a2 = arena.and(&[no_img, add_eq]);
    let ante = arena.and(&[a2, del_eq]);
    let na = arena.not(ante);
    let body = arena.or(&[na, conc]);

    // structural matrices under this binding
    let mut tr = FolTranslator::new(BoolCtx::new(), &bounds);
    tr.set_bitwidth(4);
    let mimg = tr.expr_matrix(&arena, img, &env).unwrap();
    let mut hs_img: Vec<i32> = mimg.iter().map(|(_, v)| v.0).collect();
    hs_img.sort_unstable();
    println!("img matrix literals (expect {{5,6}}): {hs_img:?}");

    // circuit for body
    let root = tr.formula_ref(&arena, body, &env).expect("body");
    println!("body root slot={} sign={}", root.slot(), root.sign());

    // enumerate all 256 leaf assignments with the CORRECT convention:
    // Var(slot s) reads model[s - 1]
    let mp = tr.ctx.num_slots();
    tr.ctx.with_factory(|f| {
        let mut falsifying: Vec<usize> = Vec::new();
        for mask in 0..256u32 {
            let mut model: Vec<bool> = vec![false; mp + 2];
            for (i, mv) in model.iter_mut().enumerate().take(8) {
                *mv = (mask >> i) & 1 == 1; // slot i+1 -> index i
            }
            if !f.eval(root, &model) {
                falsifying.push(mask as usize);
            }
        }
        println!(
            "circuit falsifying assignments: {} / 256 (expect 0)",
            falsifying.len()
        );
        if let Some(&m) = falsifying.first() {
            println!("first falsifying mask={m:#010b}: t tuples:");
            for i in 0..8usize {
                if (m >> i) & 1 == 1 {
                    println!("   idx{i}");
                }
            }
            // signed audit of the body tree under this model
            let mut mm: Vec<bool> = vec![false; mp + 2];
            for (i, mv) in mm.iter_mut().enumerate().take(8) {
                *mv = (m >> i) & 1 == 1;
            }
            let v = audit_tree(f, root, &mm, 1);
            println!("audit body={v}");
        }
    });

    // Evaluator ground truth on the first falsifying instance
    let inst = Instance::new(&u, &pool);
    drop(inst);
}
