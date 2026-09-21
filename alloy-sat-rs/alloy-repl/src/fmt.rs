//! REPL-only Alloy-style formatter.
//!
//! `Display` impls stay untouched (`als`, Java bridge, tests); this module
//! renders `A.f = {A$0->B$0, ...}`, empty sets as `{}`.

use std::collections::{BTreeMap, HashSet};

use alloy_front_rs::{Instance, TupleSet};
use alloy_kodkod_rs::universe::Universe;

/// Display hints: which names render unary int-atom sets as integers.
#[derive(Default)]
pub struct DisplayHints {
    /// Unary sig names rooted at `Signed`.
    pub signed_sigs: HashSet<String>,
    /// Field keys `Owner.field` with `Signed` range.
    pub signed_fields: HashSet<String>,
}

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

/// A tuple set in Alloy style: `{A$0, B$0}`, empty as `{}`.
///
/// Commas separate literal elements, so (unlike the old ` + ` style)
/// n-ary `->` tuples need no parentheses to survive re-parsing.
pub fn set_alloy(universe: &Universe, arity: u32, ts: &TupleSet) -> String {
    if ts.is_empty() {
        return "{}".to_string();
    }
    let inner = ts
        .index_view()
        .iter()
        .map(|idx| tuple_alloy(universe, arity, idx))
        .collect::<Vec<_>>()
        .join(", ");
    format!("{{{inner}}}")
}

/// Count of non-negative numeric atoms in the universe (`W`); the top
/// atom `W-1` carries the signed weight `-2^(W-1)`.
fn int_width(universe: &Universe) -> Option<i64> {
    let mut w: i64 = 0;
    for i in 0..universe.size() {
        match universe.atom(i).ok()?.parse::<i64>() {
            Ok(v) if v >= 0 => w += 1,
            _ => {}
        }
    }
    (w > 0 && w <= 62).then_some(w)
}

/// Bitmask sum over universe atom indices with signed MSB weight.
fn mask_indices(universe: &Universe, w: i64, idxs: impl Iterator<Item = i64>) -> Option<i64> {
    let mut total: i64 = 0;
    for idx in idxs {
        let v: i64 = universe.atom(idx as usize).ok()?.parse().ok()?;
        if v < 0 || v >= w {
            return None;
        }
        let weight = if v == w - 1 {
            -(1i64 << (w - 1))
        } else {
            1i64 << v
        };
        total = total.checked_add(weight)?;
    }
    Some(total)
}

/// Bitmask value of a unary int-atom set (signed MSB weight), or `None`
/// when the set is not a pure int-atom set — the same rule as the
/// solver's bitmask. Empty sets read as 0.
pub fn mask_value(universe: &Universe, ts: &TupleSet) -> Option<i64> {
    if ts.arity() != 1 {
        return None;
    }
    let w = int_width(universe)?;
    mask_indices(universe, w, ts.index_view().iter())
}

/// A tuple set, rendered as an integer when `as_int` and the set is a
/// pure int-atom set (Signed display); otherwise the `{...}` set shape.
pub fn set_alloy_maybe_int(
    universe: &Universe,
    arity: u32,
    ts: &TupleSet,
    as_int: bool,
) -> String {
    if as_int {
        if let Some(v) = mask_value(universe, ts) {
            return format!("{v}");
        }
    }
    set_alloy(universe, arity, ts)
}

/// One `owner.field` row group per owner atom: `X$0.s = 123` for
/// all-numeric rows (Signed display), `{X$0->...}` set shape otherwise.
/// Owner atoms come from the `owner` sig relation when present, else
/// from the first column seen. Empty rows read as 0.
pub fn field_rows_alloy(inst: &Instance, owner: &str, field: &str, ts: &TupleSet) -> String {
    if ts.arity() != 2 {
        return format!(
            "\n {owner}.{field} = {}",
            set_alloy(inst.universe(), ts.arity(), ts)
        );
    }
    let universe = inst.universe();
    let size = universe.size() as i64;
    let mut groups: BTreeMap<u32, Vec<u32>> = BTreeMap::new();
    for flat in ts.index_view().iter() {
        let d = digits(size, ts.arity(), flat);
        if d.len() >= 2 {
            groups.entry(d[0]).or_default().push(d[1]);
        }
    }
    // Owner atoms in instance order: the sig relation if present.
    let mut owners: Vec<u32> = Vec::new();
    for (r, ots) in inst.relation_tuples() {
        if inst.pool().name(r).as_ref() == owner && ots.arity() == 1 {
            for idx in ots.index_view().iter() {
                owners.push(idx as u32);
            }
            break;
        }
    }
    if owners.is_empty() {
        owners = groups.keys().copied().collect();
    }
    let w = int_width(universe);
    let mut out = String::new();
    for o in owners {
        let oname = atom_name(universe, o);
        // Missing group = empty row, whose bitmask value is 0.
        let empty: Vec<u32> = Vec::new();
        let cols = groups.get(&o).unwrap_or(&empty);
        let line = match w {
            Some(w) => match mask_indices(universe, w, cols.iter().map(|&c| c as i64)) {
                Some(v) => format!("{oname}.{field} = {v}"),
                None => {
                    let inner = cols
                        .iter()
                        .map(|&c| format!("{oname}->{}", atom_name(universe, c)))
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("{oname}.{field} = {{{inner}}}")
                }
            },
            None => format!("{oname}.{field} = {{}}"),
        };
        out.push_str(&format!("\n {line}"));
    }
    out
}

/// An instance in Alloy style: one `name = expr` line per relation.
/// Relations named in `signed` (Signed-rooted sigs) render unary int-atom
/// sets as their bitmask value (`S = 85`); binary `Owner.field` relations
/// in `signed_fields` decompose per owner atom (`X$0.s = 123`).
/// Everything else keeps the `{...}` set shape.
pub fn instance_alloy_hinted(inst: &Instance, hints: &DisplayHints) -> String {
    let mut out = String::from("relations:");
    for (r, ts) in inst.relation_tuples() {
        let name = inst.pool().name(r);
        let name_s: &str = &name;
        if ts.arity() == 2 {
            if let Some((owner, field)) = name_s.split_once('.') {
                if hints.signed_fields.contains(&format!("{owner}.{field}")) {
                    out.push_str(&field_rows_alloy(inst, owner, field, ts));
                    continue;
                }
            }
        }
        let as_int = ts.arity() == 1 && hints.signed_sigs.contains(name_s);
        let expr = set_alloy_maybe_int(inst.universe(), ts.arity(), ts, as_int);
        out.push_str(&format!("\n {name} = {expr}"));
    }
    out.push_str("\nints:");
    for (i, ts) in inst.int_tuples() {
        let expr = set_alloy(inst.universe(), ts.arity(), ts);
        out.push_str(&format!("\n {i} = {expr}"));
    }
    out
}

pub fn instance_alloy_signed(inst: &Instance, signed: &HashSet<String>) -> String {
    instance_alloy_hinted(
        inst,
        &DisplayHints {
            signed_sigs: signed.clone(),
            signed_fields: HashSet::new(),
        },
    )
}

/// An instance in Alloy style: one `name = expr` line per relation.
/// Kept for callers without sig info; Signed-aware rendering lives in
/// `instance_alloy_signed`.
#[allow(dead_code)]
pub fn instance_alloy(inst: &Instance) -> String {
    instance_alloy_signed(inst, &HashSet::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    fn u2() -> Arc<Universe> {
        Universe::new(["A$0", "B$0"]).unwrap()
    }

    #[test]
    fn empty_is_braces() {
        let u = u2();
        let ts = TupleSet::new(&u, 1).unwrap();
        assert_eq!(set_alloy(&u, 1, &ts), "{}");
    }

    #[test]
    fn unary_uses_braces() {
        let u = u2();
        let mut ts = TupleSet::new(&u, 1).unwrap();
        ts.insert_index(0);
        ts.insert_index(1);
        assert_eq!(set_alloy(&u, 1, &ts), "{A$0, B$0}");
        let mut one = TupleSet::new(&u, 1).unwrap();
        one.insert_index(0);
        assert_eq!(set_alloy(&u, 1, &one), "{A$0}");
    }

    #[test]
    fn binary_uses_arrow() {
        // universe size 2: flat 0*2+1 = 1 -> A$0->B$0
        let u = u2();
        let mut ts = TupleSet::new(&u, 2).unwrap();
        ts.insert_index(1);
        assert_eq!(set_alloy(&u, 2, &ts), "{A$0->B$0}");
    }

    #[test]
    fn set_shape_covers_save_cases() {
        // The old `:save` shapes (n-ary, empty, singleton) now come from
        // the single `{...}` display path.
        let u = u2();
        let mut ts = TupleSet::new(&u, 2).unwrap();
        ts.insert_index(1);
        assert_eq!(set_alloy(&u, 2, &ts), "{A$0->B$0}");
        let empty = TupleSet::new(&u, 2).unwrap();
        assert_eq!(set_alloy(&u, 2, &empty), "{}");
        let mut one = TupleSet::new(&u, 1).unwrap();
        one.insert_index(0);
        assert_eq!(set_alloy(&u, 1, &one), "{A$0}");
    }

    #[test]
    fn formatted_sets_reparse() {
        // `{...}` display output must survive re-parsing (`:query {...}`
        // accepts the same literal shape the REPL prints).
        let u = u2();
        let mut ts = TupleSet::new(&u, 2).unwrap();
        ts.insert_index(1);
        let s = set_alloy(&u, 2, &ts);
        assert_eq!(s, "{A$0->B$0}");
        assert!(alloy_front_rs::parse_expr(&s).is_ok(), "reparse {s}");
        let mut multi = TupleSet::new(&u, 1).unwrap();
        multi.insert_index(0);
        multi.insert_index(1);
        let m = set_alloy(&u, 1, &multi);
        assert_eq!(m, "{A$0, B$0}");
        assert!(alloy_front_rs::parse_expr(&m).is_ok(), "reparse {m}");
        let empty = TupleSet::new(&u, 1).unwrap();
        let e = set_alloy(&u, 1, &empty);
        assert_eq!(e, "{}");
        assert!(alloy_front_rs::parse_expr(&e).is_ok(), "reparse {e}");
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
        assert!(s.contains("A.f = {A$0->B$0}"), "got: {s}");
        assert!(!s.contains("->["), "old bracket style leaked: {s}");
    }

    fn u8() -> Arc<Universe> {
        Universe::new(["0", "1", "2", "3", "4", "5", "6", "7"]).unwrap()
    }

    fn mask_ts(u: &Arc<Universe>, idxs: &[i64]) -> TupleSet {
        let mut ts = TupleSet::new(u, 1).unwrap();
        for &i in idxs {
            ts.insert_index(i);
        }
        ts
    }

    #[test]
    fn mask_value_signed_weights() {
        let u = u8();
        // 1 + 4 + 16 + 64 = 85 (the user's example).
        assert_eq!(mask_value(&u, &mask_ts(&u, &[0, 2, 4, 6])), Some(85));
        // MSB atom carries -2^(W-1).
        assert_eq!(mask_value(&u, &mask_ts(&u, &[7])), Some(-128));
        assert_eq!(mask_value(&u, &mask_ts(&u, &[0, 7])), Some(-127));
        // empty set is 0.
        assert_eq!(mask_value(&u, &TupleSet::new(&u, 1).unwrap()), Some(0));
        // non-numeric atoms are not int sets.
        let u2 = u2();
        assert_eq!(mask_value(&u2, &mask_ts(&u2, &[0, 1])), None);
        // wrong arity is not an integer.
        let wide = TupleSet::new(&u, 2).unwrap();
        assert_eq!(mask_value(&u, &wide), None);
    }

    #[test]
    fn signed_instance_renders_integer() {
        let u = u8();
        let pool = std::sync::Arc::new(alloy_kodkod_rs::relation::RelationPool::new());
        let r = pool.intern("S", 1);
        let mut inst = Instance::new(&u, &pool);
        inst.add(r, &mask_ts(&u, &[0, 2, 4, 6])).unwrap();
        let signed: HashSet<String> = ["S".to_string()].into_iter().collect();
        let s = instance_alloy_signed(&inst, &signed);
        assert!(s.contains("S = 85"), "got: {s}");
        // unnamed relations keep the set shape.
        let plain = instance_alloy_signed(&inst, &HashSet::new());
        assert!(plain.contains("S = {0, 2, 4, 6}"), "got: {plain}");
    }

    fn field_inst() -> (
        Arc<Universe>,
        std::sync::Arc<alloy_kodkod_rs::relation::RelationPool>,
        Instance,
    ) {
        let mut full = vec!["X$0".to_string()];
        for i in 0..8 {
            full.push(i.to_string());
        }
        let u = Universe::new(full).unwrap();
        let pool = std::sync::Arc::new(alloy_kodkod_rs::relation::RelationPool::new());
        let inst = Instance::new(&u, &pool);
        (u, pool, inst)
    }

    /// Flat tuple index of (owner, value) in a size-`n` universe.
    fn flat(n: i64, owner: i64, val: i64) -> i64 {
        owner * n + val
    }

    #[test]
    fn signed_field_renders_per_owner_integer() {
        let (u, pool, mut inst) = field_inst();
        let n = u.size() as i64; // 9: X$0, 0..7
        let rel = pool.intern("X.s", 2);
        let mut ts = TupleSet::new(&u, 2).unwrap();
        for v in [0, 2, 4, 6] {
            ts.insert_index(flat(n, 0, 1 + v));
        }
        inst.add(rel, &ts).unwrap();
        let hints = DisplayHints {
            signed_sigs: HashSet::new(),
            signed_fields: ["X.s".to_string()].into_iter().collect(),
        };
        let s = instance_alloy_hinted(&inst, &hints);
        assert!(s.contains("X$0.s = 85"), "got: {s}");
        assert!(!s.contains("X.s = {"), "whole-relation shape leaked: {s}");
    }

    #[test]
    fn signed_field_empty_row_is_zero() {
        let (u, pool, mut inst) = field_inst();
        let sig = pool.intern("X", 1);
        let mut xs = TupleSet::new(&u, 1).unwrap();
        xs.insert_index(0);
        inst.add(sig, &xs).unwrap();
        let rel = pool.intern("X.s", 2);
        inst.add(rel, &TupleSet::new(&u, 2).unwrap()).unwrap();
        let hints = DisplayHints {
            signed_sigs: HashSet::new(),
            signed_fields: ["X.s".to_string()].into_iter().collect(),
        };
        let s = instance_alloy_hinted(&inst, &hints);
        assert!(s.contains("X$0.s = 0"), "got: {s}");
    }

    #[test]
    fn unsigned_field_keeps_relation_shape() {
        let (u, pool, mut inst) = field_inst();
        let n = u.size() as i64;
        let rel = pool.intern("A.f", 2);
        let mut ts = TupleSet::new(&u, 2).unwrap();
        ts.insert_index(flat(n, 0, 1));
        inst.add(rel, &ts).unwrap();
        let hints = DisplayHints::default();
        let s = instance_alloy_hinted(&inst, &hints);
        assert!(s.contains("A.f = {X$0->0}"), "got: {s}");
    }

    #[test]
    fn signed_field_multi_owner_rows() {
        let u = u8();
        let pool = std::sync::Arc::new(alloy_kodkod_rs::relation::RelationPool::new());
        let n = u.size() as i64; // 8
        let rel = pool.intern("Y.v", 2);
        let mut ts = TupleSet::new(&u, 2).unwrap();
        ts.insert_index(flat(n, 0, 0)); // owner 0 ("0"), row {0} -> 1
        ts.insert_index(flat(n, 1, 1)); // owner 1 ("1"), row {1} -> 2
        ts.insert_index(flat(n, 1, 2)); // owner 1, row {1,2} -> 6
        let mut inst = Instance::new(&u, &pool);
        inst.add(rel, &ts).unwrap();
        let hints = DisplayHints {
            signed_sigs: HashSet::new(),
            signed_fields: ["Y.v".to_string()].into_iter().collect(),
        };
        let s = instance_alloy_hinted(&inst, &hints);
        assert!(s.contains("0.v = 1"), "got: {s}");
        assert!(s.contains("1.v = 6"), "got: {s}");
    }
}
