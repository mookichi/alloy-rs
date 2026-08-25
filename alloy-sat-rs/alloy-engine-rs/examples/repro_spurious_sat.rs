//! Minimal reproduction of the known spurious-SAT bug (see
//! docs/agile-iterations.md "known bugs" and docs/repro/).
//!
//! The 5-variable quantified assertion
//!   all b,c,d,n,t: U | (noImg /\ addEq /\ delEq) -> conc
//! over bounds lo=empty hi=full is VALID (kodkod agrees), so NOT-Q must be
//! UNSAT. The Rust engine reports SAT. Variants:
//!   C = no AST sharing, B = manual unfolding (no quantifier machinery),
//!   A = quantifier machinery. All three spuriously satisfy NOT-Q, which
//! localises the fault to per-env circuit construction in fol.rs, not to
//! the quantifier driver, AST sharing, polarity optimisation or the SAT
//! backends (CaDiCaL and Splr agree on the wrong answer).
// Diagnostic scratchpad example (known-bug investigation).
#![allow(dead_code, unused_imports, unused_variables, clippy::all)]

#[allow(unused_imports)]
use alloy_kodkod_rs::ast::*;
use alloy_kodkod_rs::bounds::Bounds;
use alloy_kodkod_rs::cnf::translate_into_solver;
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
    // Build pieces WITHOUT quantifier: shared joins
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

    // ---- C: NO sharing — fresh join nodes per use (mult_dense style) ----
    {
        let mut tr = FolTranslator::new(BoolCtx::new(), &bounds);
        tr.set_bitwidth(4);
        // build the whole assertion without any shared ExprId
        let mk = |tr: &mut FolTranslator| -> FormulaId {
            let _ = tr;
            unreachable!()
        };
        let _ = mk;
        // build via helper on the SAME arena but fresh nodes each time:
        fn build_noshare(
            arena: &mut AstArena,
            vs: &[VarId],
            _ub: RelationId,
            trel: RelationId,
        ) -> FormulaId {
            macro_rules! j {
                ($v:expr) => {{
                    let ev_ = arena.expr_variable($v);
                    let et_ = arena.expr_relation(trel);
                    arena.binary_expr(BinaryOp::Join, ev_, et_).unwrap()
                }};
            }

            let _jb = j!(vs[0]);
            let jc = j!(vs[1]);
            let jd = j!(vs[2]);
            let en = arena.expr_variable(vs[3]);
            let ev = arena.expr_variable(vs[4]);
            let ev0 = arena.expr_variable(vs[0]);
            let et2 = arena.expr_relation(trel);
            let jb2 = arena.binary_expr(BinaryOp::Join, ev0, et2).unwrap();
            let img = arena.binary_expr(BinaryOp::Join, en, jb2).unwrap();
            let ms = arena.multiplicity_formula(Multiplicity::Some, img).unwrap();
            let no_img = arena.not(ms);
            let nt = arena.binary_expr(BinaryOp::Product, en, ev).unwrap();
            let ev0u = arena.expr_variable(vs[0]);
            let et3 = arena.expr_relation(trel);
            let jbu = arena.binary_expr(BinaryOp::Join, ev0u, et3).unwrap();
            let un = arena.binary_expr(BinaryOp::Union, jbu, nt).unwrap();
            let add_eq = arena.comparison(ExprCompOp::Equals, jc, un).unwrap();
            let ev0d = arena.expr_variable(vs[0]);
            let et4 = arena.expr_relation(trel);
            let jbd = arena.binary_expr(BinaryOp::Join, ev0d, et4).unwrap();
            let df = arena.binary_expr(BinaryOp::Difference, jbd, nt).unwrap();
            let del_eq = arena.comparison(ExprCompOp::Equals, jd, df).unwrap();
            let ev0c = arena.expr_variable(vs[0]);
            let et5 = arena.expr_relation(trel);
            let jbc = arena.binary_expr(BinaryOp::Join, ev0c, et5).unwrap();
            let evdc = arena.expr_variable(vs[2]);
            let et6 = arena.expr_relation(trel);
            let jdc = arena.binary_expr(BinaryOp::Join, evdc, et6).unwrap();
            let conc = arena.comparison(ExprCompOp::Equals, jbc, jdc).unwrap();
            let a2 = arena.and(&[no_img, add_eq]);
            let ante = arena.and(&[a2, del_eq]);
            let na = arena.not(ante);
            arena.or(&[na, conc])
        }
        let body_ns = build_noshare(&mut arena, &vs, ub, trel);
        let _eu = arena.expr_relation(ub);
        let ds = {
            let d: Vec<Decl> = vs
                .iter()
                .map(|&v| {
                    let e = arena.expr_relation(ub);
                    arena.decl(v, Multiplicity::One, e).unwrap()
                })
                .collect();
            arena.add_decls(d)
        };
        let q2 = arena.quantified(Quantifier::All, ds, body_ns);
        let nq2 = arena.not(q2);
        let mut tr = FolTranslator::new(BoolCtx::new(), &bounds);
        tr.set_bitwidth(4);
        let rootc = tr.formula_ref(&arena, nq2, &[]).expect("noshare translate");
        println!("C root const={}", rootc.is_const());
        let mp = tr.ctx.num_slots();
        let ctx = tr.ctx.clone();
        let mut ip = IpasirSolver::new().unwrap();
        ctx.with_factory(|f| translate_into_solver(&mut ip, f, rootc, mp))
            .unwrap();
        println!(
            "C no-sharing result: {}",
            if SatSolver::solve(&mut ip) {
                "SAT (BUG)"
            } else {
                "UNSAT (ok)"
            }
        );
    }

    // ---- A: quantifier machinery ----
    let _eu = arena.expr_relation(ub);
    let ds = {
        let d: Vec<Decl> = vs
            .iter()
            .map(|&v| {
                let e = arena.expr_relation(ub);
                arena.decl(v, Multiplicity::One, e).unwrap()
            })
            .collect();
        arena.add_decls(d)
    };
    let q = arena.quantified(Quantifier::All, ds, body);
    let nq = arena.not(q);

    {
        let mut tr = FolTranslator::new(BoolCtx::new(), &bounds);
        tr.set_bitwidth(4);
        let root = tr.formula_ref(&arena, nq, &[]).expect("quant translate");
        println!("A quant: root const={}", root.is_const());
        let mp = tr.ctx.num_slots();
        let ctx = tr.ctx.clone();
        let mut ip = IpasirSolver::new().unwrap();
        ctx.with_factory(|f| translate_into_solver(&mut ip, f, root, mp))
            .unwrap();
        println!(
            "A quant result: {}",
            if SatSolver::solve(&mut ip) {
                "SAT (BUG)"
            } else {
                "UNSAT (ok)"
            }
        );
    }

    // ---- B: manual unfolding over 32 bindings using env-parameterised refs ----
    {
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
        let mut ip = IpasirSolver::new().unwrap();
        ctx.with_factory(|f| translate_into_solver(&mut ip, f, rootb, mp))
            .unwrap();
        let satb = SatSolver::solve(&mut ip);
        println!(
            "B unfolded: {}",
            if satb { "SAT (BUG)" } else { "UNSAT (ok)" }
        );
        if !satb {
            return;
        }
        // Per-binding: circuit value vs intended
        use alloy_kodkod_rs::bool::{BoolNode, BoolRef as BR};
        let mut model: Vec<bool> = vec![false; mp + 1];
        for (slot, mv) in model.iter_mut().enumerate().skip(1) {
            *mv = SatSolver::value_of(&ip, slot as i64);
        }
        let inst = tr.materialize(|slot| SatSolver::value_of(&ip, slot as i64));
        let ev = alloy_kodkod_rs::eval::Evaluator::new(&inst);
        println!(
            "model t tuples: {}",
            inst.tuples(trel).map(|x| x.len()).unwrap_or(0)
        );
        if let Some(ts) = inst.tuples(trel) {
            println!("{ts}");
        }
        for _bi in 0..2u32 {
            for _di in 0..2u32 {
                // only bindings with b=c=a0 fixed? print all 32 compactly
            }
        }
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
                            let bref = refs[bi as usize * 16
                                + ci as usize * 8
                                + di as usize * 4
                                + ni as usize * 2
                                + ti as usize];
                            let cv = ctx.with_factory(|f| f.eval(bref, &model));
                            let ante_v = ev.formula_bool(&arena, ante, &env).unwrap();
                            let conc_v = ev.formula_bool(&arena, conc, &env).unwrap();
                            let intended = !(ante_v && !conc_v);
                            if cv != intended {
                                println!("LIE b={bi} c={ci} d={di} n={ni} t={ti}: circuit={cv} intended={intended} (ante={ante_v} conc={conc_v})");
                                fn dumpv(
                                    f: &alloy_kodkod_rs::BoolFactory,
                                    r: BR,
                                    m: &[bool],
                                    d: usize,
                                ) -> bool {
                                    let pad = " ".repeat(d * 2);
                                    if r.is_const() {
                                        println!("{}const({}) [{}]", pad, r.const_value(), r.0);
                                        return r.const_value();
                                    }
                                    let mv = m[r.slot() as usize];
                                    let sv = if r.sign() { mv } else { !mv };
                                    match f.node(r) {
                                        Some(BoolNode::Var) => {
                                            println!(
                                                "{}VAR h={} slot={} val={}",
                                                pad,
                                                r.0,
                                                r.slot(),
                                                sv
                                            );
                                            sv
                                        }
                                        Some(BoolNode::And(kids)) => {
                                            println!("{}AND h={} stored={} kids:", pad, r.0, sv);
                                            let mut acc = true;
                                            for k in kids.iter() {
                                                acc &= dumpv(f, *k, m, d + 1);
                                            }
                                            println!("{}AND h={} computed={}", pad, r.0, acc);
                                            acc
                                        }
                                        Some(BoolNode::Or(kids)) => {
                                            println!("{}OR h={} stored={} kids:", pad, r.0, sv);
                                            let mut acc = false;
                                            for k in kids.iter() {
                                                acc |= dumpv(f, *k, m, d + 1);
                                            }
                                            println!("{}OR h={} computed={}", pad, r.0, acc);
                                            acc
                                        }
                                        Some(BoolNode::Ite { c, t, e }) => {
                                            println!("{}ITE h={} stored={}", pad, r.0, sv);
                                            let cv2 = dumpv(f, *c, m, d + 1);
                                            let tv = dumpv(f, *t, m, d + 1);
                                            let ev2 = dumpv(f, *e, m, d + 1);
                                            let a = if cv2 { tv } else { ev2 };
                                            println!("{}ITE h={} computed={}", pad, r.0, a);
                                            a
                                        }
                                        None => {
                                            println!("{}DANGLING {}", pad, r.0);
                                            sv
                                        }
                                    }
                                }
                                ctx.with_factory(|f| {
                                    let x = dumpv(f, bref, &model, 1);
                                    println!("audited body={x}");
                                });
                            }
                        }
                    }
                }
            }
        }
    }
}
