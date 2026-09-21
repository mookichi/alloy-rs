//! Bit-lane groups (`CastToIntOp::BitsIn`): per-group value namespaces
//! with independent MSB tops, so dedicated lanes never pollute the
//! builtin `Int` bitmask reading (or each other).

use alloy_kodkod_rs::ast::*;
use alloy_kodkod_rs::bounds::{Bounds, INT_BITS_GROUP};
use alloy_kodkod_rs::fol::FolTranslator;
use alloy_kodkod_rs::relation::RelationPool;
use alloy_kodkod_rs::tuple::Tuple;
use alloy_kodkod_rs::tupleset::TupleSet;
use alloy_kodkod_rs::universe::Universe;
use alloy_kodkod_rs::BoolCtx;
use std::sync::Arc;

const LANE: u32 = 7;

fn setup() -> (Arc<Universe>, Arc<RelationPool>, Bounds) {
    // Lane atoms M$0..M$2 (values 0,1,2) plus unrelated Int atoms.
    let u = Universe::new(vec!["M$0", "M$1", "M$2", "0", "1"]).unwrap();
    let pool = Arc::new(RelationPool::new());
    let mut b = Bounds::new(&u, &pool);
    for (v, name) in [(0i64, "M$0"), (1, "M$1"), (2, "M$2")] {
        let mut ts = TupleSet::new(&u, 1).unwrap();
        ts.insert(&Tuple::from_atoms(&u, &[name]).unwrap()).unwrap();
        b.bound_exactly_int_in(LANE, v, &ts).unwrap();
    }
    // Builtin group holds its own namespace.
    for (v, name) in [(0i64, "0"), (5, "1")] {
        let mut ts = TupleSet::new(&u, 1).unwrap();
        ts.insert(&Tuple::from_atoms(&u, &[name]).unwrap()).unwrap();
        b.bound_exactly_int(v, &ts).unwrap();
    }
    (u, pool, b)
}

fn singletons(u: &Arc<Universe>, atoms: &[&str]) -> TupleSet {
    let mut ts = TupleSet::new(u, 1).unwrap();
    for a in atoms {
        ts.insert(&Tuple::from_atoms(u, &[a]).unwrap()).unwrap();
    }
    ts
}

#[test]
fn lane_registry_is_isolated_from_builtin() {
    let (_, _, b) = setup();
    // Builtin iterator sees only group 0.
    let builtin: Vec<(i64, usize)> = b
        .int_bounds()
        .map(|(v, ts)| (v, ts.len()))
        .collect();
    assert_eq!(builtin, vec![(0, 1), (5, 1)]);
    // Lane iterator sees only its group.
    let lane: Vec<(i64, usize)> = b
        .int_bounds_in(LANE)
        .map(|(v, ts)| (v, ts.len()))
        .collect();
    assert_eq!(lane, vec![(0, 1), (1, 1), (2, 1)]);
    // Unknown group is empty.
    assert_eq!(b.int_bounds_in(99).count(), 0);
    assert_eq!(
        b.lane_groups().collect::<Vec<_>>(),
        vec![LANE]
    );
}

#[test]
fn bits_in_reads_lane_with_own_top() {
    let (u, pool, mut b) = setup();
    let mut arena = AstArena::with_pool(Arc::clone(&pool));
    // r = {M$0, M$1} exactly -> bits value 1 + 2 = 3 (lane top = 2).
    let r = arena.relation("r", 1);
    b.bound_exactly(r, &singletons(&u, &["M$0", "M$1"])).unwrap();
    let e = arena.expr_relation(r);
    let i = arena.cast_to_int(CastToIntOp::BitsIn(LANE), e).unwrap();

    let ctx = BoolCtx::new();
    let mut tr = FolTranslator::with_options(ctx, &b, 8, false);
    let c = tr.int_expr(&arena, i, &[]).unwrap();
    assert_eq!(c.value_of(&[]), 3);
}

#[test]
fn bits_in_signed_msb_weight() {
    let (u, pool, mut b) = setup();
    let mut arena = AstArena::with_pool(Arc::clone(&pool));
    // r = {M$2} exactly -> top-bit weight -4.
    let r = arena.relation("r", 1);
    b.bound_exactly(r, &singletons(&u, &["M$2"])).unwrap();
    let e = arena.expr_relation(r);
    let i = arena.cast_to_int(CastToIntOp::BitsIn(LANE), e).unwrap();

    let ctx = BoolCtx::new();
    let mut tr = FolTranslator::with_options(ctx, &b, 8, false);
    let c = tr.int_expr(&arena, i, &[]).unwrap();
    assert_eq!(c.value_of(&[]), -4);
}

#[test]
fn builtin_bits_ignores_lane_atoms() {
    let (u, pool, mut b) = setup();
    let mut arena = AstArena::with_pool(Arc::clone(&pool));
    // r over lane atoms only; builtin BITS must read 0 (no pollution).
    let r = arena.relation("r", 1);
    b.bound_exactly(r, &singletons(&u, &["M$0", "M$1", "M$2"])).unwrap();
    let e = arena.expr_relation(r);
    let i = arena.cast_to_int(CastToIntOp::Bits, e).unwrap();

    let ctx = BoolCtx::new();
    let mut tr = FolTranslator::with_options(ctx, &b, 8, false);
    let c = tr.int_expr(&arena, i, &[]).unwrap();
    assert_eq!(c.value_of(&[]), 0);
    let _ = INT_BITS_GROUP;
}
