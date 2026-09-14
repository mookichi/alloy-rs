//! REPL-only Alloy-style formatter.
//!
//! `Display` impls stay untouched (`als`, Java bridge, tests); this module
//! renders `A.f = A$0->B$0 + ...`, empty sets as `none`.

use alloy_front_rs::{Instance, TupleSet};
use alloy_kodkod_rs::universe::Universe;

fn atom_name(universe: &Universe, idx: u32) -> String {
    universe
        .atom(idx as usize)
        .map(|s| s.to_string())
        .unwrap_or_else(|_| "?".to_string())
}

/// Decode a flat tuple index (base-`size` digits, most significant first)
/// into per-column atom indices.
fn digits(size: i64, arity: u32, mut flat: i64) -> Vec<u32> {
    let mut out = vec![0u32; arity as usize];
    if size <= 0 {
        return out;
    }
    for i in (0..arity as usize).rev() {
        let d = flat % size;
        out[i] = d as u32;
        flat /= size;
    }
    out
}

/// One tuple in Alloy style: `A$0` (unary) or `A$0->B$0` (n-ary).
pub fn tuple_alloy(universe: &Universe, arity: u32, flat: i64) -> String {
    let size = universe.size() as i64;
    digits(size, arity, flat)
        .iter()
        .map(|&d| atom_name(universe, d))
        .collect::<Vec<_>>()
        .join("->")
}

/// A tuple set in Alloy style: tuples joined with ` + `, empty as `none`.
pub fn set_alloy(universe: &Universe, arity: u32, ts: &TupleSet) -> String {
    if ts.len() == 0 {
        return "none".to_string();
    }
    ts.index_view()
        .iter()
        .map(|idx| tuple_alloy(universe, arity, idx))
        .collect::<Vec<_>>()
        .join(" + ")
}

/// An instance in Alloy style: one `name = expr` line per relation.
pub fn instance_alloy(inst: &Instance) -> String {
    let mut out = String::from("relations:");
    for (r, ts) in inst.relation_tuples() {
        let name = inst.pool().name(r);
        let expr = set_alloy(inst.universe(), ts.arity(), ts);
        out.push_str(&format!("\n {name} = {expr}"));
    }
    out.push_str("\nints:");
    for (i, ts) in inst.int_tuples() {
        let expr = set_alloy(inst.universe(), ts.arity(), ts);
        out.push_str(&format!("\n {i} = {expr}"));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    fn u2() -> Arc<Universe> {
        Universe::new(["A$0", "B$0"]).unwrap()
    }

    #[test]
    fn empty_is_none() {
        let u = u2();
        let ts = TupleSet::new(&u, 1).unwrap();
        assert_eq!(set_alloy(&u, 1, &ts), "none");
    }

    #[test]
    fn unary_joins_with_plus() {
        let u = u2();
        let mut ts = TupleSet::new(&u, 1).unwrap();
        ts.insert_index(0);
        ts.insert_index(1);
        assert_eq!(set_alloy(&u, 1, &ts), "A$0 + B$0");
    }

    #[test]
    fn binary_uses_arrow() {
        // universe size 2: flat 0*2+1 = 1 -> A$0->B$0
        let u = u2();
        let mut ts = TupleSet::new(&u, 2).unwrap();
        ts.insert_index(1);
        assert_eq!(set_alloy(&u, 2, &ts), "A$0->B$0");
    }

    #[test]
    fn instance_lines_use_equals() {
        let u = u2();
        let pool = std::sync::Arc::new(alloy_kodkod_rs::relation::RelationPool::new());
        let r = pool.intern("A.f", 2);
        let mut inst = Instance::new(&u, &pool);
        let mut ts = TupleSet::new(&u, 2).unwrap();
        ts.insert_index(1);
        inst.add(r, &ts).unwrap();
        let s = instance_alloy(&inst);
        assert!(s.contains("A.f = A$0->B$0"), "got: {s}");
        assert!(!s.contains("->["), "old bracket style leaked: {s}");
    }
}
