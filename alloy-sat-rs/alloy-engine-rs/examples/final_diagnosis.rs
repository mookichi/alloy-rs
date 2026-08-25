//! Definitive scan: reachability + definition consistency + clause audit
//! for the failing NOT-Q unfolded circuit.
// Diagnostic scratchpad example (known-bug investigation).
#![allow(dead_code, unused_imports, unused_variables, clippy::all)]

#[allow(unused_imports)]
use alloy_kodkod_rs::ast::*;
use alloy_kodkod_rs::bool::{BoolNode, BoolRef};
use alloy_kodkod_rs::bounds::Bounds;
use alloy_kodkod_rs::cnf::{translate_into_solver, translate_to_cnf};
use alloy_kodkod_rs::fol::FolTranslator;
use alloy_kodkod_rs::ipasir_bridge::IpasirSolver;
use alloy_kodkod_rs::relation::{RelationId, RelationPool};
use alloy_kodkod_rs::sat::SatSolver;
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

    let vs: Vec<VarId> = ["b", "c", "d", "n", "t"]
        .iter()
        .map(|n| arena.variable(n))
        .collect();
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

    let mut tr = FolTranslator::new(BoolCtx::new(), &bounds);
    tr.set_bitwidth(4);
    let mut refs = Vec::new();
    for bi in 0..2u32 {
        for ci in 0..2u32 {
            for di in 0..2u32 {
                for ni in 0..2u32 {
                    for ti in 0..2u32 {
                        let env: Vec<(VarId, Vec<u32>)> = vec![
                            (vs[0], vec![bi]),
                            (vs[1], vec![ci]),
                            (vs[2], vec![di]),
                            (vs[3], vec![ni]),
                            (vs[4], vec![ti]),
                        ];
                        refs.push(tr.formula_ref(&arena, body, &env).expect("body"));
                    }
                }
            }
        }
    }
    let big = tr.ctx.and(&refs);
    let rootb = tr.ctx.not(big);
    let mp = tr.ctx.num_slots();
    let ctx = tr.ctx.clone();

    let cnf = ctx.with_factory(|f| translate_to_cnf(f, rootb, mp).unwrap());
    println!("clauses={} num_vars={}", cnf.clauses.len(), cnfv_num(&cnf));
    fn cnfv_num(c: &alloy_kodkod_rs::cnf::CnfTranslation) -> usize {
        c.num_vars
    }

    let mut ip = IpasirSolver::new().unwrap();
    if cnf.num_vars > ip.num_variables() {
        ip.add_variables(cnf.num_vars - ip.num_variables());
    }
    for cl in &cnf.clauses {
        ip.add_clause(cl);
    }
    let sat = SatSolver::solve(&mut ip);
    println!("solver SAT={sat}");
    if !sat {
        return;
    }

    let mut model: Vec<bool> = vec![false; cnf.num_vars + 1];
    for s in 1..=cnf.num_vars {
        model[s] = SatSolver::value_of(&ip, s as i64);
    }
    let val = |r: BoolRef, m: &[bool]| -> bool {
        if r.is_const() {
            return r.const_value();
        }
        let x = m[r.slot() as usize];
        if r.sign() {
            x
        } else {
            !x
        }
    };

    // sanity: every clause satisfied?
    let mut bad = 0;
    for cl in &cnf.clauses {
        if !cl.iter().any(|&l| val(BoolRef(l as i32), &model)) {
            bad += 1;
        }
    }
    println!("clauses violated by model: {bad}");

    // reachability from root
    let mut reach: std::collections::HashSet<u32> = std::collections::HashSet::new();
    let mut stack = vec![rootb.slot()];
    while let Some(s) = stack.pop() {
        if !reach.insert(s) {
            continue;
        }
        let kids: Vec<u32> = match ctx.with_factory(|f| f.node(BoolRef(s as i32)).cloned()) {
            Some(BoolNode::And(k)) | Some(BoolNode::Or(k)) => k.iter().map(|x| x.slot()).collect(),
            Some(BoolNode::Ite { c, t, e }) => vec![c.slot(), t.slot(), e.slot()],
            _ => vec![],
        };
        stack.extend(kids);
    }
    println!("reachable gates (incl primaries): {}", reach.len());

    // definition consistency among REACHABLE gates only
    let mut viol = 0;
    for &slot in &reach {
        let rr = BoolRef(slot as i32);
        let nd = ctx.with_factory(|f| f.node(rr).cloned());
        let Some(nd) = nd else { continue };
        let comp = match &nd {
            BoolNode::Var => continue,
            BoolNode::And(kids) => kids.iter().all(|k| val(*k, &model)),
            BoolNode::Or(kids) => kids.iter().any(|k| val(*k, &model)),
            BoolNode::Ite { c, t, e } => {
                let cv = val(*c, &model);
                if cv {
                    val(*t, &model)
                } else {
                    val(*e, &model)
                }
            }
        };
        if comp != model[slot as usize] {
            viol += 1;
            if viol <= 8 {
                println!(
                    "REACHABLE-DEF-VIOLATION slot={slot} node={nd:?} stored={} computed={comp}",
                    model[slot as usize]
                );
                // which clauses mention it?
                let mut touching = 0;
                for cl in &cnf.clauses {
                    if cl.iter().any(|&l| l.abs() == slot as i64) {
                        touching += 1;
                        if touching <= 6 {
                            println!("    clause {cl:?}");
                        }
                    }
                }
                println!("    ({touching} clauses mention slot {slot})");
            }
        }
    }
    println!("reachable def-violations: {viol}");

    // ---- Full signed audit of ONE binding's body circuit ----
    // the lying binding found previously: b=a1,c=a1,d=a0,n=a0,t=a0
    {
        let env: Vec<(VarId, Vec<u32>)> = vec![
            (vs[0], vec![1]),
            (vs[1], vec![1]),
            (vs[2], vec![0]),
            (vs[3], vec![0]),
            (vs[4], vec![0]),
        ];
        let bref = tr.formula_ref(&arena, body, &env).expect("body");
        println!(
            "binding b=a1 c=a1 d=a0 n=a0 t=a0: body ref handle={} slot={} sign={}",
            bref.0,
            bref.slot(),
            bref.sign()
        );
        fn audit(f: &alloy_kodkod_rs::BoolFactory, r: BoolRef, m: &[bool], d: usize) -> bool {
            let pad = " ".repeat(d * 2);
            let sv = if r.is_const() {
                r.const_value()
            } else if r.sign() {
                m[r.slot() as usize]
            } else {
                !m[r.slot() as usize]
            };
            match f.node(r) {
                Some(BoolNode::Var) => {
                    println!("{}VAR h={} val={}", pad, r.0, sv);
                    sv
                }
                Some(BoolNode::And(kids)) => {
                    println!("{}AND h={} val={}", pad, r.0, sv);
                    let mut a = true;
                    for k in kids.iter() {
                        a &= audit(f, *k, m, d + 1);
                    }
                    println!("{}=> AND {} computed={}", pad, r.0, a);
                    if a != sv {
                        println!("{}!! INCONSISTENT", pad);
                    }
                    a
                }
                Some(BoolNode::Or(kids)) => {
                    println!("{}OR h={} val={}", pad, r.0, sv);
                    let mut a = false;
                    for k in kids.iter() {
                        a |= audit(f, *k, m, d + 1);
                    }
                    println!("{}=> OR {} computed={}", pad, r.0, a);
                    if a != sv {
                        println!("{}!! INCONSISTENT", pad);
                    }
                    a
                }
                Some(BoolNode::Ite { c, t, e }) => {
                    println!("{}ITE h={} val={}", pad, r.0, sv);
                    let cv = audit(f, *c, m, d + 1);
                    let tv = audit(f, *t, m, d + 1);
                    let ev2 = audit(f, *e, m, d + 1);
                    if cv {
                        tv
                    } else {
                        ev2
                    }
                }
                None => {
                    println!("{}CONST-OR-DANGLING h={}", pad, r.0);
                    sv
                }
            }
        }
        ctx.with_factory(|f| {
            let v = audit(f, bref, &model, 1);
            println!("audited body value = {v}");
        });
    }

    // ---- Which kid of BIG is false, and what clauses cover it? ----
    {
        let bs = rootb.slot();
        let kids: Vec<i32> = match ctx.with_factory(|f| f.node(BoolRef(bs as i32)).cloned()) {
            Some(BoolNode::And(k)) | Some(BoolNode::Or(k)) => k.iter().map(|x| x.0).collect(),
            _ => vec![],
        };
        println!(
            "big(slot={bs}) kids={} root-sign={}",
            kids.len(),
            rootb.sign()
        );
        let unit = cnf
            .clauses
            .iter()
            .find(|c| c.len() == 1 && (c[0] == bs as i64 || c[0] == -(bs as i64)));
        println!("root unit clause: {:?}", unit);

        let mut shown = 0;
        for &khandle in &kids {
            let kslot = khandle.unsigned_abs() as usize;
            let kmodel = if khandle > 0 {
                model[kslot]
            } else {
                !model[kslot]
            };
            if !kmodel && shown < 2 {
                shown += 1;
                println!(
                    "--- FALSE kid h={khandle} slot={kslot} node={:?}",
                    ctx.with_factory(|f| f.node(BoolRef(kslot as i32)).cloned())
                );
                let mut cnt = 0;
                for cl in &cnf.clauses {
                    if cl.iter().any(|&l| l.abs() == kslot as i64) {
                        cnt += 1;
                        if cnt <= 8 {
                            println!("     clause {cl:?}");
                        }
                    }
                }
                println!("     ({cnt} clauses mention slot {kslot})");
            }
        }
    }
}
