//! Property tests for the hybrid sparse/dense IntSet (backlog 5).
//! Compares the implementation against a BTreeSet oracle across random
//! operation sequences and both representations.

use alloy_kodkod_rs::intset::IntSet;
use std::collections::BTreeSet;

#[test]
fn intset_matches_oracle_random_ops() {
    let mut rng: u64 = 0x243F6A8885A308D3;
    let mut next = move || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        rng
    };

    for trial in 0..40 {
        let mut ours = IntSet::new();
        let mut oracle: BTreeSet<i64> = BTreeSet::new();
        // bias some trials toward dense small ranges to exercise the bitset
        let span = if trial % 2 == 0 { 300 } else { 5000 };

        for _ in 0..600 {
            let op = next() % 6;
            let v = (next() % span) as i64;
            match op {
                0 | 1 => {
                    let a = ours.insert(v);
                    let b = oracle.insert(v);
                    assert_eq!(a, b, "insert {v}");
                }
                2 => {
                    let a = ours.remove(v);
                    let b = oracle.remove(&v);
                    assert_eq!(a, b, "remove {v}");
                }
                3 => {
                    assert_eq!(ours.contains(v), oracle.contains(&v), "contains {v}");
                }
                _ => {}
            }
        }

        // bulk op comparison
        let other_ours = IntSet::from_iter((0..span as i64).step_by(7));
        let other_oracle: BTreeSet<i64> = (0..span as i64).step_by(7).collect();

        assert_eq!(ours.len(), oracle.len());
        assert_eq!(
            ours.iter().collect::<Vec<_>>(),
            oracle.iter().copied().collect::<Vec<_>>(),
            "iteration order/values"
        );

        for (name, o, r) in [
            ("union", other_ours.union(&ours), &oracle | &other_oracle),
            (
                "intersection",
                other_ours.intersection(&ours),
                &other_oracle & &other_ours_set(&oracle),
            ),
            (
                "difference",
                other_ours.difference(&ours),
                (&other_oracle - &oracle),
            ),
        ] {
            let _ = name;
            assert_eq!(
                o.iter().collect::<Vec<_>>(),
                r.into_iter().collect::<Vec<_>>()
            );
        }
        assert_eq!(
            ours.contains_all(&other_ours),
            oracle.is_superset(&other_oracle)
        );
    }
}

// helper so the borrow checker is happy mixing BTreeSet refs
fn other_ours_set(oracle: &BTreeSet<i64>) -> BTreeSet<i64> {
    oracle.clone()
}
