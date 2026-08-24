#![no_main]

//! Invariant: the hybrid IntSet must behave exactly like a BTreeSet oracle.

use alloy_kodkod_rs::intset::IntSet;
use libfuzzer_sys::fuzz_target;
use std::collections::BTreeSet;

fuzz_target!(|data: &[u8]| {
    let mut ours = IntSet::new();
    let mut oracle: BTreeSet<i64> = BTreeSet::new();
    let mut it = data.chunks(2);
    while let Some(pair) = it.next() {
        if pair.len() < 2 {
            break;
        }
        let op = pair[0] % 5;
        let v = i64::from(pair[1]) - 64; // allow negatives to hit sparse path
        match op {
            0 | 1 => {
                assert_eq!(ours.insert(v), oracle.insert(v));
            }
            2 => {
                assert_eq!(ours.remove(v), oracle.remove(&v));
            }
            3 => assert_eq!(ours.contains(v), oracle.contains(&v)),
            _ => {}
        }
    }
    assert_eq!(ours.len(), oracle.len());
    assert_eq!(
        ours.iter().collect::<Vec<_>>(),
        oracle.iter().copied().collect::<Vec<_>>()
    );

    // bulk op against a second derived set
    let b2: IntSet = oracle.range(0..).copied().collect();
    let u = ours.union(&b2);
    let merged: BTreeSet<i64> = oracle.union(&b2_oracle(&oracle)).copied().collect();
    assert_eq!(u.iter().collect::<Vec<_>>(), merged.into_iter().collect::<Vec<_>>());
});

fn b2_oracle(oracle: &BTreeSet<i64>) -> BTreeSet<i64> {
    oracle.range(0..).copied().collect()
}
