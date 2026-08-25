//! MINIMAL repro of the spurious-SAT defect: image membership of a
//! two-level join (n . (b . t)) reads leaf literals shifted by one flat
//! index for certain bindings.

use alloy_kodkod_rs::ast::*;
use alloy_kodkod_rs::bounds::Bounds;
use alloy_kodkod_rs::fol::FolTranslator;
use alloy_kodkod_rs::relation::{RelationId, RelationPool};
use alloy_kodkod_rs::tuple::Tuple;
use alloy_kodkod_rs::tupleset::TupleSet;
use alloy_kodkod_rs::universe::Universe;
use alloy_kodkod_rs::BoolCtx;
use std::sync::Arc;

#[test]
fn image_membership_positions() {
    let u = Universe::new(["a0", "a1"]).unwrap();
    let pool = Arc::new(RelationPool::new());
    let mut arena = AstArena::with_pool(Arc::clone(&pool));
    let mut bounds = Bounds::new(&u, &pool);

    let trel: RelationId = arena.relation("t", 3);
    let mut full = TupleSet::new(&u, 3).unwrap();
    for x in ["a0", "a1"] {
        for y in ["a0", "a1"] {
            for z in ["a0", "a1"] {
                full.insert(&Tuple::from_atoms(&u, &[x, y, z]).unwrap())
                    .unwrap();
            }
        }
    }
    let empty3 = TupleSet::new(&u, 3).unwrap();
    bounds.bound(trel, &empty3, &full).unwrap();

    // binding: b=a1, n=a0
    let env: Vec<(VarId, Vec<u32>)> = vec![
        (arena.variable("b"), vec![1]),
        (arena.variable("n"), vec![0]),
    ];
    let vb = env[0].0;
    let vn = env[1].0;

    let et = arena.expr_relation(trel);
    let eb = arena.expr_variable(vb);
    let en = arena.expr_variable(vn);
    let rowb = arena.binary_expr(BinaryOp::Join, eb, et).unwrap();
    let img = arena.binary_expr(BinaryOp::Join, en, rowb).unwrap();

    let mut tr = FolTranslator::new(BoolCtx::new(), &bounds);
    tr.set_bitwidth(4);
    // structural: row(a1) cells must be literals idx4..7 -> slots 5..8
    let mrow = tr.expr_matrix(&arena, rowb, &env).unwrap();
    let hs_row: Vec<i32> = mrow.iter().map(|(_, v)| v.0).collect();
    assert_eq!(hs_row, vec![5, 6, 7, 8], "row(a1) literals");

    // structural: img cells must be literals idx4,idx5 -> slots 5,6
    let mimg = tr.expr_matrix(&arena, img, &env).unwrap();
    let mut hs_img: Vec<i32> = mimg.iter().map(|(_, v)| v.0).collect();
    hs_img.sort_unstable();
    assert_eq!(hs_img, vec![5, 6], "img cells must be s5,s6");

    println!(
        "PROBE row-matrix: {:?}",
        mrow.iter().map(|(i, v)| (i, v.0)).collect::<Vec<_>>()
    );
    println!(
        "PROBE img-matrix: {:?}",
        mimg.iter().map(|(i, v)| (i, v.0)).collect::<Vec<_>>()
    );
    println!("PROBE img-matrix dims: {:?}", mimg.dims().num_dimensions());
    // behavioural: some(img) under leaf-only models == s5 | s6
    let ms = arena.multiplicity_formula(Multiplicity::Some, img).unwrap();
    let root = tr.formula_ref(&arena, ms, &env).unwrap();
    let mp = tr.ctx.num_slots();
    tr.ctx.with_factory(|f| {
        for k in 0..8usize {
            let mut model: Vec<bool> = vec![false; mp + 1];
            model[k + 1] = true;
            let got = f.eval(root, &model);
            let want = k == 4 || k == 5;
            if got != want {
                println!("ROOT NODE: {:?}", f.node(root));
                println!("MISMATCH idx{k}: got={got} want={want}");
            }
        }
    });
}
