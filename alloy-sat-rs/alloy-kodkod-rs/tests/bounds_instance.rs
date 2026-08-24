use alloy_kodkod_rs::bounds::Bounds;
use alloy_kodkod_rs::instance::{Instance, InstanceError};
use alloy_kodkod_rs::relation::RelationPool;
use alloy_kodkod_rs::tupleset::TupleSet;
use alloy_kodkod_rs::universe::Universe;
use std::sync::Arc;

fn setup() -> (Arc<Universe>, Arc<RelationPool>) {
    let u = Universe::new(["n0", "n1", "n2", "n3", "n4"]).unwrap();
    let pool = Arc::new(RelationPool::new());
    (u, pool)
}

#[test]
fn insertion_order_is_preserved_across_mixed_binds() {
    let (u, pool) = setup();
    let mut b = Bounds::new(&u, &pool);
    let node = pool.intern("Node", 1);
    let next = pool.intern("next", 2);
    let last = pool.intern("last", 2);

    let all: Vec<&str> = vec!["n0", "n1", "n2", "n3", "n4"];
    let node_ts = tuple_set(&u, &all);
    let upper = pair_all(&u);

    b.bound_exactly(node, &node_ts).unwrap();
    b.bound_upper(next, &upper).unwrap();
    b.bound_exactly(last, &pair_single(&u)).unwrap();

    let order: Vec<String> = b.relations().map(|r| pool.name(r).to_string()).collect();
    assert_eq!(order, vec!["Node", "next", "last"]);
}

#[test]
fn bound_validation_errors_match_java_messages() {
    let (u, pool) = setup();
    let mut b = Bounds::new(&u, &pool);
    let next = pool.intern("next", 2);
    let unary = tuple_set(&u, &["n0"]);

    assert!(matches!(
        b.bound_exactly(next, &unary),
        Err(alloy_kodkod_rs::bounds::BoundsError::ArityMismatch {
            relation: 2,
            bound: 1
        })
    ));

    let other = Universe::new(["n0"]).unwrap();
    let foreign = TupleSet::new(&other, 2).unwrap();
    assert!(matches!(
        b.bound_upper(next, &foreign),
        Err(alloy_kodkod_rs::bounds::BoundsError::WrongUniverse)
    ));

    let lower = pair_single(&u);
    let upper = {
        let mut s = TupleSet::new(&u, 2).unwrap();
        let t = alloy_kodkod_rs::tuple::Tuple::from_atoms(&u, &["n1", "n3"]).unwrap();
        s.insert(&t).unwrap();
        s
    };
    assert!(matches!(
        b.bound(next, &lower, &upper),
        Err(alloy_kodkod_rs::bounds::BoundsError::LowerNotInUpper)
    ));
}

#[test]
fn bound_with_equal_sets_stores_exact_bounds() {
    let (u, pool) = setup();
    let mut b = Bounds::new(&u, &pool);
    let r = pool.intern("r", 2);
    let lower = pair_single(&u);
    let upper = pair_single(&u);

    b.bound(r, &lower, &upper).unwrap();
    let (lo, up) = b.bound_pair(r).unwrap();
    assert_eq!(lo, up);
    assert_eq!(b.upper_bound(r).unwrap(), &lower);
}

#[test]
fn int_bounds_require_singleton_unary_sets() {
    let (u, pool) = setup();
    let mut b = Bounds::new(&u, &pool);
    let two = tuple_set(&u, &["n0", "n1"]);
    let binary = pair_single(&u);

    use alloy_kodkod_rs::bounds::BoundsError::*;
    assert!(matches!(
        b.bound_exactly_int(7, &two),
        Err(IntBoundNotSingleton(2))
    ));
    assert!(matches!(
        b.bound_exactly_int(7, &binary),
        Err(IntBoundNotUnary(2))
    ));

    b.bound_exactly_int(7, &tuple_set(&u, &["n3"])).unwrap();
    assert_eq!(b.exact_int_bound(7).unwrap().index_view().min(), Some(3));
    assert_eq!(b.ints().iter().collect::<Vec<_>>(), vec![7]);
}

#[test]
fn unbind_removes_relation_and_order_entry() {
    let (u, pool) = setup();
    let mut b = Bounds::new(&u, &pool);
    let a = pool.intern("a", 1);
    let c = pool.intern("c", 1);
    b.bound_exactly(a, &tuple_set(&u, &["n0"])).unwrap();
    b.bound_exactly(c, &tuple_set(&u, &["n1"])).unwrap();

    assert!(b.unbind(a));
    assert!(!b.unbind(a));
    let order: Vec<String> = b.relations().map(|r| pool.name(r).to_string()).collect();
    assert_eq!(order, vec!["c"]);
}

#[test]
fn skolems_are_listed_from_pool_flags() {
    let (u, pool) = setup();
    let mut b = Bounds::new(&u, &pool);
    let sk = pool.intern("$x", 1);
    let plain = pool.intern("p", 1);
    pool.set_skolem(sk, true);
    b.bound_exactly(sk, &tuple_set(&u, &["n0"])).unwrap();
    b.bound_exactly(plain, &tuple_set(&u, &["n1"])).unwrap();
    assert_eq!(b.skolems(), vec![sk]);
}

#[test]
fn instance_adds_replaces_and_finds_by_name() {
    let (u, pool) = setup();
    let mut inst = Instance::new(&u, &pool);
    let next = pool.intern("next", 2);
    let pairs = pair_all(&u);

    inst.add(next, &pairs).unwrap();
    let replaced = pair_single(&u);
    inst.add(next, &replaced).unwrap();
    assert_eq!(inst.tuples(next), Some(&replaced));
    assert_eq!(inst.find_relation_by_name("next"), Some(next));
    assert_eq!(inst.find_relation_by_name("nope"), None);

    let ints = tuple_set(&u, &["n4"]);
    inst.add_int(-2, &ints).unwrap();
    assert_eq!(inst.int_tuple(-2).unwrap().len(), 1);
    assert_eq!(inst.ints().iter().collect::<Vec<_>>(), vec![-2]);

    assert!(matches!(
        inst.add_int(5, &pair_all(&u)),
        Err(InstanceError::IntBoundNotUnary(2))
    ));
}

#[test]
fn bounds_display_dumps_like_java_tostring() {
    let (u, pool) = setup();
    let mut b = Bounds::new(&u, &pool);
    let node = pool.intern("Node", 1);
    b.bound_exactly(node, &tuple_set(&u, &["n0"])).unwrap();
    b.bound_exactly_int(0, &tuple_set(&u, &["n0"])).unwrap();

    let text = format!("{}", b);
    assert!(text.contains("relation bounds:"));
    assert!(text.contains("Node: [[[n0]], [[n0]]]"));
    assert!(text.contains("int bounds:"));
    assert!(text.contains("0->[[n0]]"));
}

fn tuple_set(u: &Arc<Universe>, atoms: &[&str]) -> TupleSet {
    let mut s = TupleSet::new(u, 1).unwrap();
    for a in atoms {
        let t = alloy_kodkod_rs::tuple::Tuple::from_atoms(u, &[a]).unwrap();
        s.insert(&t).unwrap();
    }
    s
}

fn pair_single(u: &Arc<Universe>) -> TupleSet {
    let mut s = TupleSet::new(u, 2).unwrap();
    let t = alloy_kodkod_rs::tuple::Tuple::from_atoms(u, &["n0", "n1"]).unwrap();
    s.insert(&t).unwrap();
    s
}

fn pair_all(u: &Arc<Universe>) -> TupleSet {
    let mut s = TupleSet::new(u, 2).unwrap();
    for i in 0..u.size() as i64 {
        for j in 0..u.size() as i64 {
            s.insert_index(i * u.size() as i64 + j);
        }
    }
    s
}
