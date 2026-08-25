//! Is the body circuit a tautology? Enumerate ALL leaf assignments and
//! evaluate the circuit directly via BoolFactory::eval (no SAT solver).
//! Compare against Evaluator ground truth on the same instance.
// Diagnostic scratchpad example (known-bug investigation).
#![allow(dead_code, unused_imports, unused_variables, clippy::all)]

#[allow(unused_imports)]
use alloy_kodkod_rs::ast::*;
use alloy_kodkod_rs::bounds::Bounds;
use alloy_kodkod_rs::eval::Evaluator;
use alloy_kodkod_rs::fol::FolTranslator;
use alloy_kodkod_rs::instance::Instance;
use alloy_kodkod_rs::relation::RelationPool;
use alloy_kodkod_rs::tuple::Tuple;
use alloy_kodkod_rs::tupleset::TupleSet;
use alloy_kodkod_rs::universe::Universe;
use alloy_kodkod_rs::BoolCtx;
use std::sync::Arc;

fn main() {
    let u = Universe::new(["a0", "a1"]).unwrap();
    let pool = Arc::new(RelationPool::new());
    let mut arena = AstArena::with_pool(Arc::clone(&pool));
    let mut bounds = Bounds::new(&u, &pool);
    let ub = arena.relation("U", 1);
    let mut uu = TupleSet::new(&u, 1).unwrap();
    for a in ["a0", "a1"] {
        uu.insert(&Tuple::from_atoms(&u, &[a]).unwrap()).unwrap();
    }
    bounds.bound_exactly(ub, &uu).unwrap();
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

    // NOTE: vars created in the same order as the failing case
    let vs: Vec<VarId> = ["b", "c", "d", "n", "t"]
        .iter()
        .map(|n| arena.variable(n))
        .collect();
    // Shared joins like variant B
    let et = arena.expr_relation(trel);
    let e0 = arena.expr_variable(vs[0]);
    let jb = arena.binary_expr(BinaryOp::Join, e0, et).unwrap();
    let e1 = arena.expr_variable(vs[1]);
    let jc = arena.binary_expr(BinaryOp::Join, e1, et).unwrap();
    let e2 = arena.expr_variable(vs[2]);
    let jd = arena.binary_expr(BinaryOp::Join, e2, et).unwrap();
    let en = arena.expr_variable(vs[3]);
    let ev = arena.expr_variable(vs[4]);
    let img = arena.binary_expr(BinaryOp::Join, en, jb).unwrap();
    let ms = arena.multiplicity_formula(Multiplicity::Some, img).unwrap();
    let no_img = arena.not(ms);
    let nt = arena.binary_expr(BinaryOp::Product, en, ev).unwrap();
    let un = arena.binary_expr(BinaryOp::Union, jb, nt).unwrap();
    let add_eq = arena.comparison(ExprCompOp::Equals, jc, un).unwrap();
    let df = arena.binary_expr(BinaryOp::Difference, jb, nt).unwrap();
    let del_eq = arena.comparison(ExprCompOp::Equals, jd, df).unwrap();
    let conc = arena.comparison(ExprCompOp::Equals, jb, jd).unwrap();
    let a2 = arena.and(&[no_img, add_eq]);
    let ante = arena.and(&[a2, del_eq]);
    let na = arena.not(ante);
    let body = arena.or(&[na, conc]);

    // Translate ONCE under the lying binding env (fresh translator).
    let env: Vec<(VarId, Vec<u32>)> = vec![
        (vs[0], vec![1]),
        (vs[1], vec![1]),
        (vs[2], vec![0]),
        (vs[3], vec![0]),
        (vs[4], vec![0]),
    ]; // b=c=a1, d=a0, n=t=a0
    let mut tr = FolTranslator::new(BoolCtx::new(), &bounds);
    tr.set_bitwidth(4);
    let mp0 = 0usize; // placeholder
    let _ = mp0;
    let _root_unused = tr.formula_ref(&arena, body, &env).expect("body");
    // We need the actual root ref; re-translate to grab it:
    let bref = tr.formula_ref(&arena, body, &env).expect("body ref");
    println!("body bref slot={} sign={}", bref.slot(), bref.sign());
    {
        use alloy_kodkod_rs::bool::BoolNode;
        let nd = tr.ctx.with_factory(|f| f.node(bref).cloned());
        println!("body node = {:?}", nd);
        // also print na / conc refs
        let naref = tr.formula_ref(&arena, na, &env).unwrap();
        let cref = tr.formula_ref(&arena, conc, &env).unwrap();
        println!(
            "na h={} node={:?}; conc h={} node={:?}",
            naref.0,
            tr.ctx.with_factory(|f| f.node(naref).cloned()),
            cref.0,
            tr.ctx.with_factory(|f| f.node(cref).cloned())
        );
    }
    let mp = tr.ctx.num_slots();
    let mut model: Vec<bool> = vec![false; mp + 1];

    // Enumerate all 2^8 assignments of t-cell literals s1..s8 (idx0..7),
    // evaluate the circuit with factory.eval under a model vector where
    // primaries carry the enumerated bits.
    let mp = tr.ctx.num_slots();
    // explicit per-mask table
    {
        let r_noimg = tr.formula_ref(&arena, no_img, &env).unwrap();
        let r_add = tr.formula_ref(&arena, add_eq, &env).unwrap();
        let r_del = tr.formula_ref(&arena, del_eq, &env).unwrap();
        let r_conc = tr.formula_ref(&arena, conc, &env).unwrap();
        let r_ante = tr.formula_ref(&arena, ante, &env).unwrap();
        let r_na = tr.formula_ref(&arena, na, &env).unwrap();

        // SIGNED TREE of r_noimg (with model values from idx3-probe: only s4=T)
        {
            use alloy_kodkod_rs::bool::BoolNode;
            let mut mm: Vec<bool> = vec![false; mp + 1];
            mm[4] = true; // idx3 = (a0,a1,a1)
            fn dv(
                f: &alloy_kodkod_rs::BoolFactory,
                r: alloy_kodkod_rs::bool::BoolRef,
                m: &[bool],
                d: usize,
            ) -> bool {
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
                    Some(BoolNode::And(k)) => {
                        println!(
                            "{pad}AND h={} kids={:?}",
                            r.0,
                            k.iter().map(|x| x.0).collect::<Vec<_>>()
                        );
                        let mut a = true;
                        for x in k.iter() {
                            a &= dv(f, *x, m, d + 1);
                        }
                        a
                    }
                    Some(BoolNode::Or(k)) => {
                        println!(
                            "{pad}OR h={} kids={:?}",
                            r.0,
                            k.iter().map(|x| x.0).collect::<Vec<_>>()
                        );
                        let mut a = false;
                        for x in k.iter() {
                            a |= dv(f, *x, m, d + 1);
                        }
                        a
                    }
                    Some(BoolNode::Ite { c, t, e }) => {
                        println!("{pad}ITE h={}", r.0);
                        let cv = dv(f, *c, m, d + 1);
                        if cv {
                            dv(f, *t, m, d + 1)
                        } else {
                            dv(f, *e, m, d + 1)
                        }
                    }
                    None => {
                        println!("{pad}DANGLING h={}", r.0);
                        sv
                    }
                }
            }
            tr.ctx.with_factory(|f| {
                let v = dv(f, r_noimg, &mm, 1);
                println!("noImg audit value = {v} (expected TRUE)");
            });
        }
        // STRUCTURAL matrix dump for this binding
        {
            let m_jb = tr.expr_matrix(&arena, jb, &env).unwrap();
            let m_img = tr.expr_matrix(&arena, img, &env).unwrap();
            println!("M_jb dims_cap={} cells:", m_jb.dims().capacity());
            for (i, v) in m_jb.iter() {
                println!("   pos{} h{}", i, v.0);
            }
            println!("M_img cells:");
            for (i, v) in m_img.iter() {
                println!("   pos{} h{}", i, v.0);
            }
        }
        println!("origins (slot <- rel idx):");
        for o in tr.var_origins() {
            println!("   slot={} -> t-idx {}", o.slot, o.tuple_index);
        }
        // single-cell probes: which leaf bit makes noImg false?
        tr.ctx.with_factory(|f| {
            for k in 0..8usize {
                let mut mm: Vec<bool> = vec![false; mp + 1];
                mm[k + 1] = true;
                let x = k / 4; let y = (k / 2) % 2; let z = k % 2;
                println!("PROBE only(idx{k}=(a{x},a{y},a{z})) slot{}: noImg={} conc={} (expect noImg={} conc=T)",
                    k + 1,
                    f.eval(r_noimg, &mm), f.eval(r_conc, &mm),
                    if x == 1 && y == 0 { "F" } else { "T" });
            }
        });
        for m in 0..16u32 {
            for i in 0..8usize {
                model[i + 1] = (m >> i) & 1 == 1;
            }
            let (v_noimg, v_add, v_del, v_conc, v_ante, v_na, v_body) = tr.ctx.with_factory(|f| {
                (
                    f.eval(r_noimg, &model),
                    f.eval(r_add, &model),
                    f.eval(r_del, &model),
                    f.eval(r_conc, &model),
                    f.eval(r_ante, &model),
                    f.eval(r_na, &model),
                    f.eval(bref, &model),
                )
            });
            println!(
                "mask{:3} noImg={:5} addEq={:5} delEq={:5} conc={:5} ante={:5} na={:5} BODY={}",
                m, v_noimg, v_add, v_del, v_conc, v_ante, v_na, v_body
            );
        }
    }
    let mut falsifying = Vec::new();
    for mask in 0..256u32 {
        let mut model: Vec<bool> = vec![false; mp + 1];
        // origins: slot=i+1 <-> tuple idx=i for rel t (verified earlier)
        for i in 0..8usize {
            model[i + 1] = (mask >> i) & 1 == 1;
        }
        let v = tr.ctx.with_factory(|f| f.eval(bref, &model));
        if !v {
            falsifying.push(mask);
        }
    }
    println!("circuit falsifying assignments: {} / 256", falsifying.len());
    if let Some(&m) = falsifying.first() {
        // decode: bits -> tuples present
        println!("first falsifying mask={m}: t tuples:");
        for i in 0..8usize {
            if (m >> i) & 1 == 1 {
                let x = i / 4;
                let y = (i / 2) % 2;
                let z = i % 2;
                println!("   (a{}, a{}, a{})", x, y, z);
            }
        }
        // Build the matching Instance manually and evaluate AST ground truth
        let mut inst = Instance::new(&u, &pool);
        let mut ts = TupleSet::new(&u, 3).unwrap();
        for i in 0..8usize {
            if (m >> i) & 1 == 1 {
                let names = ["a0", "a1"];
                let x = i / 4;
                let y = (i / 2) % 2;
                let z = i % 2;
                ts.insert(&Tuple::from_atoms(&u, &[names[x], names[y], names[z]]).unwrap())
                    .unwrap();
            }
        }
        inst.add(trel, &ts).unwrap();
        let ev = Evaluator::new(&inst);
        let intended = ev.formula_bool(&arena, body, &env).unwrap();
        println!("Evaluator intended body={} on same instance", intended);

        // Piece-level circuit evaluation under the SAME leaf-only model
        let r_noimg = tr.formula_ref(&arena, no_img, &env).unwrap();
        let r_add = tr.formula_ref(&arena, add_eq, &env).unwrap();
        let r_del = tr.formula_ref(&arena, del_eq, &env).unwrap();
        let r_conc = tr.formula_ref(&arena, conc, &env).unwrap();
        let r_ante = tr.formula_ref(&arena, ante, &env).unwrap();
        let ev_c = |r: alloy_kodkod_rs::bool::BoolRef| tr.ctx.with_factory(|f| f.eval(r, &model));
        println!(
            "pieces: noImg={} addEq={} delEq={} conc={} ante={}",
            ev_c(r_noimg),
            ev_c(r_add),
            ev_c(r_del),
            ev_c(r_conc),
            ev_c(r_ante)
        );
        println!("intended: noImg=T addEq=F delEq=T conc=T ante=F");
        // signed tree dump of the ANTE gate
        fn dumpv(
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
                    println!(
                        "{pad}AND h={} kids={:?}",
                        r.0,
                        kids.iter().map(|k| k.0).collect::<Vec<_>>()
                    );
                    let mut a = true;
                    for k in kids.iter() {
                        a &= dumpv(f, *k, m, d + 1);
                    }
                    println!("{pad}=> AND {} = {a}", r.0);
                    if a != sv {
                        println!("{pad}!! MISMATCH stored={sv}");
                    }
                    a
                }
                Some(BoolNode::Or(kids)) => {
                    println!(
                        "{pad}OR h={} kids={:?}",
                        r.0,
                        kids.iter().map(|k| k.0).collect::<Vec<_>>()
                    );
                    let mut a = false;
                    for k in kids.iter() {
                        a |= dumpv(f, *k, m, d + 1);
                    }
                    println!("{pad}=> OR {} = {a}", r.0);
                    if a != sv {
                        println!("{pad}!! MISMATCH stored={sv}");
                    }
                    a
                }
                Some(BoolNode::Ite { c, t, e }) => {
                    println!("{pad}ITE h={}", r.0);
                    let cv = dumpv(f, *c, m, d + 1);
                    let tv = dumpv(f, *t, m, d + 1);
                    let ev2 = dumpv(f, *e, m, d + 1);
                    cv.then_some(tv).unwrap_or(ev2)
                }
                None => {
                    println!("{pad}DANGLING h={}", r.0);
                    sv
                }
            }
        }
        use alloy_kodkod_rs::bool::BoolFactory as _;
        tr.ctx.with_factory(|f| {
            dumpv(f, r_ante, &model, 1);
        });
        return;
    }
}
