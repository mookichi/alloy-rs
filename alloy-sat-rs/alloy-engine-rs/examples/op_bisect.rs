//! Operator bisection: which sub-formula of the m15 body stops being a
//! tautology? Every variant below MUST evaluate TRUE under all 256 leaf
//! assignments (they are semantic consequences of noImg).

use alloy_kodkod_rs::ast::*;
use alloy_kodkod_rs::bounds::Bounds;
use alloy_kodkod_rs::fol::FolTranslator;
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
    let trel = arena.relation("t", 3);
    let mut full = TupleSet::new(&u, 3).unwrap();
    for x in ["a0", "a1"] {
        for y in ["a0", "a1"] {
            for z in ["a0", "a1"] {
                full.insert(&Tuple::from_atoms(&u, &[x, y, z]).unwrap())
                    .unwrap();
            }
        }
    }
    bounds
        .bound(trel, &TupleSet::new(&u, 3).unwrap(), &full)
        .unwrap();

    // binding b=a1,c=a1,d=a0,n=a0,t=a0
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
    let _rowc = arena.binary_expr(BinaryOp::Join, ec, et).unwrap();
    let rowd = arena.binary_expr(BinaryOp::Join, ed, et).unwrap();
    let nt = arena.binary_expr(BinaryOp::Product, en, evt).unwrap();

    let mut tr = FolTranslator::new(BoolCtx::new(), &bounds);
    tr.set_bitwidth(4);

    fn check(
        tr: &mut FolTranslator,
        arena: &AstArena,
        env: &[(VarId, Vec<u32>)],
        name: &str,
        f: FormulaId,
    ) {
        let root = tr.formula_ref(arena, f, env).expect(name);
        let mp = tr.ctx.num_slots();
        let ctx = tr.ctx.clone();
        let mut bad = 0usize;
        let mut first: Option<usize> = None;
        ctx.with_factory(|fac| {
            for mask in 0..256u32 {
                let mut model: Vec<bool> = vec![false; mp + 2];
                for (i, mv) in model.iter_mut().enumerate().take(8) {
                    *mv = (mask >> i) & 1 == 1; // slot i+1 -> index i
                }
                if !fac.eval(root, &model) {
                    bad += 1;
                    if first.is_none() {
                        first = Some(mask as usize);
                    }
                }
            }
        });
        println!(
            "{name:<28} falsifying={bad:>3}/256 {}",
            first
                .map(|m| format!("first=bit-pattern {m:#010b}"))
                .unwrap_or_default()
        );
    }

    // T0 sanity: p \/ !p style tautology via equivalence of identical exprs
    let id_taut = arena.comparison(ExprCompOp::Equals, rowb, rowb).unwrap();
    check(&mut tr, &arena, &env, "T0 eq(b.addr,b.addr)", id_taut);

    // T1: noImg -> (n.t notin rowb):  some(n.rowb) implies ...
    //    equiv form: !(noImg) \/ (rowb - nt = rowb) when nt=n.t disjoint...
    // Build: delEq-without-noimg is NOT valid; use implication core:
    // noImg /\ delEq -> conc   (valid!)
    let img = arena.binary_expr(BinaryOp::Join, en, rowb).unwrap();
    let ms = arena.multiplicity_formula(Multiplicity::Some, img).unwrap();
    let no_img = arena.not(ms);
    let df = arena.binary_expr(BinaryOp::Difference, rowb, nt).unwrap();
    let del_eq = arena.comparison(ExprCompOp::Equals, rowd, df).unwrap();
    let rb2 = arena.binary_expr(BinaryOp::Join, eb, et).unwrap();
    let rd2 = arena.binary_expr(BinaryOp::Join, ed, et).unwrap();
    let conc = arena.comparison(ExprCompOp::Equals, rb2, rd2).unwrap();
    let core_ante = arena.and(&[no_img, del_eq]);
    let na_core = arena.not(core_ante);
    let core = arena.or(&[na_core, conc]);
    check(&mut tr, &arena, &env, "V1 noImg&delEq->conc", core);

    // V2: same but delEq written via union round trip on c:
    //     noImg /\ (c.addr = b.addr + n.t) -> (d.addr = c.addr - n.t -> ...)
    // simpler: noImg /\ (rowc = rowb U nt) -> (rowc - nt = rowb)   (valid!)
    let rc3 = arena.binary_expr(BinaryOp::Join, ec, et).unwrap();
    let u3 = arena.binary_expr(BinaryOp::Union, rowb, nt).unwrap();
    let add3 = arena.comparison(ExprCompOp::Equals, rc3, u3).unwrap();
    let rb4 = arena.binary_expr(BinaryOp::Join, eb, et).unwrap();
    let d4 = arena.binary_expr(BinaryOp::Difference, rc3, nt).unwrap();
    let eq4 = arena.comparison(ExprCompOp::Equals, rb4, d4).unwrap();
    // FIX: validity requires noImg in the antecedent
    let e0b = arena.expr_variable(vb);
    let etb = arena.expr_relation(trel);
    let jb4 = arena.binary_expr(BinaryOp::Join, e0b, etb).unwrap();
    let img4 = arena.binary_expr(BinaryOp::Join, en, jb4).unwrap();
    let ms4 = arena
        .multiplicity_formula(Multiplicity::Some, img4)
        .unwrap();
    let ni4 = arena.not(ms4);
    let a42 = arena.and(&[ni4, add3]);
    let na4 = arena.not(a42);
    let v4 = arena.or(&[na4, eq4]);
    check(&mut tr, &arena, &env, "V2 noImg&(c=bUt)->(c-Ut=b)", v4);
}
