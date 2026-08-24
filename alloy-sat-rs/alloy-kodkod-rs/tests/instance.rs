use alloy_kodkod_rs::{CapacityError, Tuple, TupleSet, Universe};
use std::sync::Arc;

fn u4() -> Arc<Universe> {
    Universe::new(["a0", "a1", "a2", "a3"]).unwrap()
}

#[test]
fn universe_rejects_empty_and_duplicates() {
    assert!(Universe::new(Vec::<&str>::new()).is_err());
    assert!(Universe::new(["x", "x"]).is_err());
}

#[test]
fn universe_index_atom_roundtrip() {
    let u = u4();
    assert_eq!(u.size(), 4);
    assert_eq!(u.index("a2").unwrap(), 2);
    assert_eq!(u.atom(3).unwrap().as_ref(), "a3");
    assert!(!u.contains("zz"));
    assert!(u.index("zz").is_err());
}

#[test]
fn tuple_index_encoding_matches_java() {
    let u = u4();
    // Java: index = sum(universe.index(atoms[i]) * size^(arity-1-i))
    let t = Tuple::from_atoms(&u, &["a1", "a0"]).unwrap();
    assert_eq!(t.index(), 4);
    assert_eq!(t.arity(), 2);
    assert_eq!(t.atom_index(0).unwrap(), 1);
    assert_eq!(t.atom_index(1).unwrap(), 0);
    assert_eq!(t.to_string(), "[a1, a0]");
    assert!(Tuple::from_atoms(&u, &["a9"]).is_err());
}

#[test]
fn tuple_lazy_product_and_contains() {
    let u = u4();
    let t01 = Tuple::from_atoms(&u, &["a0", "a1"]).unwrap();
    let t23 = Tuple::from_atoms(&u, &["a2", "a3"]).unwrap();
    let p = t01.product(&t23).unwrap();
    assert_eq!(p.arity(), 4);
    assert_eq!(p.index(), 27);
    assert!(p.contains("a3"));
    assert!(!p.contains("zz"));
    let cross_universe = Universe::new(["a0", "a1", "a2", "a3"]).unwrap();
    let other = Tuple::from_atoms(&cross_universe, &["a0", "a1"]).unwrap();
    assert!(t01.product(&other).is_err());
}

#[test]
fn tupleset_all_none_range_and_equality() {
    let u = u4();
    let mut all = TupleSet::new(&u, 2).unwrap();
    assert_eq!(all.capacity().unwrap(), 16);
    for i in 0..16i64 {
        all.insert_index(i);
    }
    assert_eq!(all.len(), 16);
    let full: TupleSet = {
        let mut s = TupleSet::new(&u, 2).unwrap();
        for i in 0..16i64 {
            s.insert_index(i);
        }
        s
    };
    assert_eq!(all, full);

    let from = Tuple::from_atoms(&u, &["a0", "a1"]).unwrap();
    let to = Tuple::from_atoms(&u, &["a1", "a0"]).unwrap();
    let r = TupleSet::range(&u, &from, &to).unwrap();
    assert_eq!(r.len(), 4);
    assert_eq!(r.index_view().min(), Some(1));
    assert_eq!(r.index_view().max(), Some(4));

    let inv = TupleSet::range(&u, &to, &from);
    assert!(inv.is_err());
}

#[test]
fn tupleset_area_rectangle_from_javadoc() {
    let u = u4();
    let ul = Tuple::from_atoms(&u, &["a0", "a2"]).unwrap();
    let lr = Tuple::from_atoms(&u, &["a1", "a3"]).unwrap();
    let col0 = TupleSet::range(
        &u,
        &Tuple::from_atoms(&u, &["a0"]).unwrap(),
        &Tuple::from_atoms(&u, &["a1"]).unwrap(),
    )
    .unwrap();
    let col1 = TupleSet::range(
        &u,
        &Tuple::from_atoms(&u, &["a2"]).unwrap(),
        &Tuple::from_atoms(&u, &["a3"]).unwrap(),
    )
    .unwrap();
    let area = col0.product(&col1).unwrap();
    assert_eq!(area.arity(), 2);
    assert_eq!(area.len(), 4);
    for t in [&ul, &lr] {
        assert!(area.contains(t), "{} should be in area", t);
    }
    let outside = Tuple::from_atoms(&u, &["a2", "a0"]).unwrap();
    assert!(!area.contains(&outside));
}

#[test]
fn tupleset_project_uses_java_formula() {
    let u = u4();
    let mut s = TupleSet::new(&u, 3).unwrap();
    s.insert(&Tuple::from_atoms(&u, &["a0", "a1", "a2"]).unwrap())
        .unwrap();
    s.insert(&Tuple::from_atoms(&u, &["a1", "a1", "a0"]).unwrap())
        .unwrap();
    let p0 = s.project(0).unwrap();
    let p2 = s.project(2).unwrap();
    assert_eq!(p0.arity(), 1);
    assert_eq!(p0.len(), 2);
    assert!(p0.index_view().contains(0) && p0.index_view().contains(1));
    assert_eq!(p2.len(), 2);
    assert!(p2.index_view().contains(2) && p2.index_view().contains(0));
}

#[test]
fn int_set_ops_and_tuple_set_bulk() {
    use alloy_kodkod_rs::IntSet;
    let a: IntSet = [1, 3, 5].into_iter().collect();
    let b: IntSet = [3, 4].into_iter().collect();
    assert_eq!(a.union(&b).iter().collect::<Vec<_>>(), vec![1, 3, 4, 5]);
    assert_eq!(a.intersection(&b).iter().collect::<Vec<_>>(), vec![3]);
    assert_eq!(a.difference(&b).iter().collect::<Vec<_>>(), vec![1, 5]);
    assert!(b.contains_all(&IntSet::from_iter([3])));
    assert!(!a.contains_all(&b));

    let mut s1 = a.clone();
    assert!(s1.add_all(&b));
    assert!(!s1.add_all(&b));
    assert!(s1.remove_all(&b));
    assert_eq!(
        s1.iter().collect::<Vec<_>>(),
        vec![1, 5],
        "removed 3,4 from 1,3,4,5"
    );
}

#[test]
fn tuple_contains_handles_leading_zero_digits() {
    let u = u4();
    // index=1 encodes [a0, a1]; Java's remainder loop misses the a0 digit.
    let t = Tuple::from_atoms(&u, &["a0", "a1"]).unwrap();
    assert_eq!(t.index(), 1);
    assert!(t.contains("a0"), "fixed: leading zero digit must count");
    assert!(t.contains("a1"));
}

#[test]
fn capacity_is_i64_not_int_max() {
    let big = Universe::new((0..1024usize).map(|i| format!("n{}", i))).unwrap();
    let set = TupleSet::new(&big, 6);
    assert!(set.is_ok(), "1024^6 ~ 2^60 must fit in i64");
    assert_eq!(set.unwrap().capacity().unwrap(), 1024i64.pow(6));

    let huge = Universe::new((0..4096usize).map(|i| format!("m{}", i))).unwrap();
    let over = TupleSet::new(&huge, 8);
    assert!(
        matches!(over, Err(CapacityError(_))),
        "4096^8 ~ 2^87 must overflow i64"
    );
}
