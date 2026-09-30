//! REPL-only Alloy-style formatter.
//!
//! `Display` impls stay untouched (`als`, Java bridge, tests); this module
//! renders `A.f = {A$0->B$0, ...}`, empty sets as `{}`.

use std::collections::{BTreeMap, HashSet};

use alloy_front_rs::{Instance, TupleSet};
use alloy_kodkod_rs::mepk::Mepk;
use alloy_kodkod_rs::real::RealCenter;
use alloy_kodkod_rs::universe::Universe;

/// Display hints: which names render unary int-atom sets as integers.
#[derive(Default)]
pub struct DisplayHints {
    /// Unary sig names rooted at `Signed`.
    pub signed_sigs: HashSet<String>,
    /// Field keys `Owner.field` with `Signed` range.
    pub signed_fields: HashSet<String>,
    /// Field keys `Owner.field` whose range is a `Real`/`EReal` value
    /// (rows decode to `c` or `c ± R` alongside the raw bit set).
    /// Unary sig names denoting value bit sets (`in Real` / `in EReal`
    /// and friends): empty sets read as the Real zero, not raw.
    pub real_sigs: HashSet<String>,
    /// Field keys `Owner.field` with flat `Real` range: empty rows read
    /// as the Real zero instead of staying raw.
    pub real_fields: HashSet<String>,
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

/// Bit position of a lane atom (`M$3` -> 3) with the expected prefix.
fn lane_pos(universe: &Universe, idx: u32, prefix: &str) -> Option<i64> {
    let atom = universe.atom(idx as usize).ok()?;
    let (pre, suf) = atom.split_once('$')?;
    if pre != prefix {
        return None;
    }
    suf.parse::<i64>().ok()
}

/// Lane width = top bit position + 1, from the lane atoms present in the
/// universe (mirrors the solver's `W = top + 1` over the bound set).
fn lane_width(universe: &Universe, prefix: &str) -> Option<i64> {
    let mut top: Option<i64> = None;
    for i in 0..universe.size() {
        if let Some(v) = lane_pos(universe, i as u32, prefix) {
            top = Some(top.map_or(v, |t: i64| t.max(v)));
        }
    }
    top.map(|t| t + 1).filter(|&w| w > 0 && w < 63)
}

/// Two's-complement value of a lane-bit set: +2^v, MSB weighs -2^(W-1).
fn lane_value(width: i64, bits: impl Iterator<Item = i64>) -> Option<i64> {
    let mut total: i64 = 0;
    for v in bits {
        if v < 0 || v >= width {
            return None;
        }
        let w = if v == width - 1 {
            -(1i64 << (width - 1))
        } else {
            1i64 << v
        };
        total = total.checked_add(w)?;
    }
    Some(total)
}

/// True for the builtin bit-domain sigs (`$M`/`$E`/`$P`/`$K`) and the
/// `Real`/`EReal` type domains themselves: shown raw, never decoded as
/// values (an exact `Real` line otherwise gains a junk bitmask value).
fn is_lane_domain(name: &str) -> bool {
    matches!(name, "$M" | "$E" | "$P" | "$K" | "Real" | "EReal")
}

/// Real-number reading of a bit set (`{M$0, E$0, ...}` as `0.5 [m=..]`).
/// `None` for empty sets and unless every atom is a lane atom (`M$` /
/// `E$` / `P$` / `K$`). Sets with `p`/`k` bits read as `EReal`
/// intervals, the rest as exact centres; lane groups absent from the
/// set read as 0.
pub fn decode_bitset(universe: &Universe, idxs: &[u32]) -> Option<String> {
    if idxs.is_empty() {
        return None;
    }
    const PRES: [&str; 4] = ["M", "E", "P", "K"];
    let mut bits: [Vec<i64>; 4] = Default::default();
    for &i in idxs {
        let mut placed = false;
        for (li, pre) in PRES.iter().enumerate() {
            if let Some(v) = lane_pos(universe, i, pre) {
                bits[li].push(v);
                placed = true;
                break;
            }
        }
        if !placed {
            return None;
        }
    }
    // Widths are only needed for groups present in the set (their atoms
    // live in the universe, so the width lookup cannot fail there).
    let mut widths = [0i64; 4];
    for (li, pre) in PRES.iter().enumerate() {
        if bits[li].is_empty() {
            continue;
        }
        widths[li] = lane_width(universe, pre)?;
    }
    let val = |li: usize| -> Option<i64> {
        if bits[li].is_empty() {
            Some(0)
        } else {
            lane_value(widths[li], bits[li].iter().copied())
        }
    };
    let (m, e) = (val(0)?, val(1)?);
    if bits[2].is_empty() && bits[3].is_empty() {
        match RealCenter::new(m as i128, e as i32) {
            Some(v) => Some(format!("{} [m={m} e={e}]", v.centre_short())),
            None => Some(format!("(ill-formed lanes m={m} e={e})")),
        }
    } else {
        let (p, k) = (val(2)?, val(3)?);
        if p < 0 {
            return Some(format!("(ill-formed lanes m={m} e={e} p={p} k={k})"));
        }
        match Mepk::new(m as i128, e as i32, p as u32, k as i32) {
            Some(v) => Some(format!(
                "{} [m={m} e={e} p={p} k={k}]",
                v.interval_string(0)
            )),
            None => Some(format!("(ill-formed lanes m={m} e={e} p={p} k={k})")),
        }
    }
}

/// `decode_bitset` plus the Real zero: an empty set reads as
/// `0 [m=0 e=0]` when known Real-typed (via hints); otherwise empty
/// stays raw (`None`), so plain empty sigs gain no reading.
pub fn decode_bitset_typed(
    universe: &Universe,
    idxs: &[u32],
    is_real: bool,
) -> Option<String> {
    if idxs.is_empty() {
        if !is_real {
            return None;
        }
        return match RealCenter::new(0, 0) {
            Some(v) => Some(format!("{} [m=0 e=0]", v.centre_short())),
            None => Some("(ill-formed lanes m=0 e=0)".to_string()),
        };
    }
    decode_bitset(universe, idxs)
}

/// Per-owner rows for a binary relation whose value columns decode as
/// bit sets: `X$0.r = {M$0, ...} = 0.5 [m=.. e=..]`. Rows that do not
/// decode keep the per-owner `{X$0->...}` shape. `None` when no row
/// decodes at all (callers keep the legacy full-relation shape).
/// `owners` overrides the row list (empty = first columns seen).
/// `is_real` lets empty rows read as the Real zero.
pub fn bitset_field_rows_ts(
    universe: &Universe,
    _owner: &str,
    field: &str,
    ts: &TupleSet,
    owners: Vec<u32>,
    is_real: bool,
) -> Option<String> {
    if ts.arity() != 2 {
        return None;
    }
    let size = universe.size() as i64;
    let mut groups: BTreeMap<u32, Vec<u32>> = BTreeMap::new();
    for flat in ts.index_view().iter() {
        let d = digits(size, ts.arity(), flat);
        if d.len() >= 2 {
            groups.entry(d[0]).or_default().push(d[1]);
        }
    }
    let owners = if owners.is_empty() {
        groups.keys().copied().collect()
    } else {
        owners
    };
    let empty: Vec<u32> = Vec::new();
    let mut any = false;
    let mut rows: Vec<(u32, String, Option<String>)> = Vec::new();
    for o in owners {
        let cols = groups.get(&o).unwrap_or(&empty);
        let raw = cols
            .iter()
            .map(|&c| atom_name(universe, c))
            .collect::<Vec<_>>()
            .join(", ");
        let text = decode_bitset_typed(universe, cols, is_real);
        any |= text.is_some();
        rows.push((o, raw, text));
    }
    if !any {
        return None;
    }
    let mut out = String::new();
    for (o, raw, text) in rows {
        let oname = atom_name(universe, o);
        match text {
            Some(t) => out.push_str(&format!("\n {oname}.{field} = {{{raw}}} = {t}")),
            None => out.push_str(&format!("\n {oname}.{field} = {{{raw}}}")),
        }
    }
    Some(out)
}

/// Per-owner rows over the solved instance (owners from the `owner` sig
/// relation when present). `is_real` lets empty rows read as the Real
/// zero.
pub fn bitset_field_rows(
    inst: &Instance,
    owner: &str,
    field: &str,
    ts: &TupleSet,
    is_real: bool,
) -> Option<String> {
    let mut owners: Vec<u32> = Vec::new();
    for (r, ots) in inst.relation_tuples() {
        if inst.pool().name(r).as_ref() == owner && ots.arity() == 1 {
            for idx in ots.index_view().iter() {
                owners.push(idx as u32);
            }
            break;
        }
    }
    bitset_field_rows_ts(inst.universe(), owner, field, ts, owners, is_real)
}

/// Relations named in `signed` (Signed-rooted sigs) render unary int-atom
/// sets as their bitmask value (`S = 85`); binary `Owner.field` relations
/// in `signed_fields` decompose per owner atom (`X$0.s = 123`).
/// A `Real`/`EReal` value is a set of lane bits, so `real_fields` rows
/// (and `real_sigs` sets) gain its real-number or interval reading.
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
                // Value rows read their lane-bit set as a real/interval.
                if let Some(s) = bitset_field_rows(
                    inst,
                    owner,
                    field,
                    ts,
                    hints.real_fields.contains(&format!("{owner}.{field}")),
                ) {
                    out.push_str(&s);
                    continue;
                }
            }
        }
        let as_int = ts.arity() == 1 && hints.signed_sigs.contains(name_s);
        let expr = set_alloy_maybe_int(inst.universe(), ts.arity(), ts, as_int);
        // Flat bit sets gain their real-number reading alongside
        // (empty sets only when Real-typed via hints).
        let mut line = format!("\n {name} = {expr}");
        if ts.arity() == 1 && !as_int && !is_lane_domain(name_s) {
            let idxs: Vec<u32> = ts.index_view().iter().map(|i| i as u32).collect();
            let is_real = hints.real_sigs.contains(name_s);
            if let Some(t) = decode_bitset_typed(inst.universe(), &idxs, is_real) {
                line.push_str(&format!(" = {t}"));
            }
        }
        out.push_str(&line);
    }
    out.push_str("\nints:");
    // Builtin ints render as one `Int = {0, 1, ...}` set line like every
    // other sig (empty layer keeps the bare header).
    let mut nums: Vec<String> = Vec::new();
    for (_, ts) in inst.int_tuples() {
        for i in ts.index_view().iter() {
            nums.push(atom_name(inst.universe(), i as u32));
        }
    }
    if !nums.is_empty() {
        out.push_str(&format!("\n Int = {{{}}}", nums.join(", ")));
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
        let s = instance_alloy_hinted(&inst, &DisplayHints::default());
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

    fn signed() -> HashSet<String> {
        ["S".to_string()].into_iter().collect()
    }

    #[test]
    fn signed_instance_renders_integer() {
        let u = u8();
        let pool = std::sync::Arc::new(alloy_kodkod_rs::relation::RelationPool::new());
        let r = pool.intern("S", 1);
        let mut inst = Instance::new(&u, &pool);
        inst.add(r, &mask_ts(&u, &[0, 2, 4, 6])).unwrap();
        let s = instance_alloy_hinted(&inst, &DisplayHints { signed_sigs: signed(), ..Default::default() });
        assert!(s.contains("S = 85"), "got: {s}");
        // unnamed relations keep the set shape.
        let plain = instance_alloy_hinted(&inst, &DisplayHints::default());
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
            real_sigs: HashSet::new(),
            real_fields: HashSet::new(),
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
            real_sigs: HashSet::new(),
            real_fields: HashSet::new(),
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
    fn signed_field_multi_owner_rows() {        let u = u8();
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
            real_sigs: HashSet::new(),
            real_fields: HashSet::new(),
            signed_fields: ["Y.v".to_string()].into_iter().collect(),
        };
        let s = instance_alloy_hinted(&inst, &hints);
        assert!(s.contains("0.v = 1"), "got: {s}");
        assert!(s.contains("1.v = 6"), "got: {s}");
    }

    #[test]
    fn ereal_row_reads_as_an_interval() {
        // A value is the set of its lane bits, so a holder field row shows
        // the raw bits and gains the `c ± R` reading. There is no lane
        // relation left to hide.
        let src = "one sig X { r: EReal }\nfact { setEReal[X.r, 0.5] }\nrun {}";
        let inst = solve_first(src);
        let s = instance_alloy_hinted(&inst, &DisplayHints::default_for_test());
        assert!(!s.contains("Real.m ="), "raw lanes leaked: {s}");
        assert!(!s.contains("EReal.p ="), "raw lanes leaked: {s}");
        assert!(
            s.contains("X$0.r = {M$3,"),
            "raw bit set missing from the row: {s}"
        );
        assert!(
            s.contains("[m=8 e=-1 p=4 k=0]"),
            "interval reading missing: {s}"
        );
    }

    impl DisplayHints {
        fn default_for_test() -> Self {
            DisplayHints {
                signed_sigs: HashSet::new(),
                signed_fields: HashSet::new(),
                real_sigs: HashSet::new(),
                real_fields: HashSet::new(),
            }
        }
    }

    #[test]
    fn no_ereal_keeps_legacy_shape() {
        // Instances without lane relations render exactly as before.
        let u = u2();
        let pool = std::sync::Arc::new(alloy_kodkod_rs::relation::RelationPool::new());
        let r = pool.intern("A.f", 2);
        let mut inst = Instance::new(&u, &pool);
        let mut ts = TupleSet::new(&u, 2).unwrap();
        ts.insert_index(1);
        inst.add(r, &ts).unwrap();
        let s = instance_alloy_hinted(&inst, &DisplayHints::default());
        assert!(s.contains("A.f = {A$0->B$0}"), "got: {s}");
    }

    fn solve_first(src: &str) -> alloy_front_rs::Instance {
        let m = alloy_front_rs::parse_module(src).unwrap();
        let cnf = alloy_front_rs::run(&m, 0).unwrap();
        alloy_front_rs::solve(&cnf).unwrap().expect("SAT")
    }

    #[test]
    fn flat_bitset_appends_real_reading() {
        // Reported case: `X = {M$0, ...}` gains `= 0.5 [m=1 e=-1]`.
        let inst = solve_first("sig X in Real {}\nfact { setReal[X, 0.5] }\nrun {}");
        let s = instance_alloy_hinted(&inst, &DisplayHints::default());
        assert!(s.contains("X = {"), "raw set missing: {s}");
        assert!(
            s.contains("= 0.5 [m=1 e=-1]"),
            "real reading missing: {s}"
        );
        // Lane-domain lines themselves stay raw.
        assert!(s.contains("$M = {"), "got: {s}");
    }

    #[test]
    fn flat_bitset_normalizes_on_display() {
        // Even mantissae display normalized (2 = 1*2^1), lanes echoed raw.
        let inst = solve_first("sig X in Real {}\nfact { X = mbit[1] }\nrun {}");
        let s = instance_alloy_hinted(&inst, &DisplayHints::default());
        assert!(s.contains("X = {M$1} = 2 [m=2 e=0]"), "got: {s}");
    }

    #[test]
    fn flat_bitset_field_rows_decode() {
        // Holder fields decode per owner row.
        let inst = solve_first(
            "some sig H { r: Real }\nfact { setReal[H.r, 0.5] }\nrun {}",
        );
        let s = instance_alloy_hinted(&inst, &DisplayHints::default());
        assert!(s.contains("H$0.r = {"), "raw row missing: {s}");
        assert!(
            s.contains("= 0.5 [m=1 e=-1]"),
            "real reading missing: {s}"
        );
    }

    #[test]
    fn flat_bitset_mixed_sets_stay_raw() {

        // Sets mixing lane and non-lane atoms gain no reading.
        let inst = solve_first(
            "sig A {}\nsig X in Real {}\nfact { setReal[X, 0.5] and some A }\nrun {}",
        );
        let u = inst.universe();
        let mi = u.index("M$0").unwrap() as u32;
        let ai = u.index("A$0").unwrap() as u32;
        assert_eq!(decode_bitset(u, &[mi, ai]), None);
        assert_eq!(decode_bitset(u, &[]), None);
    }

    #[test]
    fn flat_bitset_ereal_interval() {
        // Sets with p/k bits read as EReal intervals (direct decode).
        let inst = solve_first("sig R1 in EReal {}\nfact { setEReal[R1, 0.5] }\nrun {}");
        let u = inst.universe();
        let idx = |n: &str| u.index(n).unwrap() as u32;
        // 0.5 is (m=8, e=-1, p=4, k=0): e=-1 needs E$0..E$3 at width 4.
        let bits = vec![
            idx("M$3"),
            idx("E$0"),
            idx("E$1"),
            idx("E$2"),
            idx("E$3"),
            idx("P$2"),
        ];
        let t = decode_bitset(u, &bits).expect("decodes");
        assert!(t.contains("[m=8 e=-1 p=4 k=0]"), "got: {t}");
        assert!(t.contains("±"), "got: {t}");
    }

    fn real_hints() -> DisplayHints {
        DisplayHints {
            real_sigs: ["X".to_string()].into_iter().collect(),
            real_fields: ["H.r".to_string()].into_iter().collect(),
            ..DisplayHints::default()
        }
    }

    #[test]
    fn flat_empty_real_reads_zero() {
        // The empty bit set is the Real zero 0.0.
        let inst = solve_first("sig X in Real {}\nfact { no X }\nrun {}");
        let s = instance_alloy_hinted(&inst, &real_hints());
        assert!(s.contains("X = {} = 0 [m=0 e=0]"), "got: {s}");
        // Plain empty sigs stay raw.
        let inst = solve_first("sig A {}\nfact { no A }\nrun {}");
        let s = instance_alloy_hinted(&inst, &real_hints());
        assert!(s.contains("A = {}"), "got: {s}");
        assert!(!s.contains("= 0 [m=0 e=0]"), "got: {s}");
    }

    #[test]
    fn flat_empty_holder_row_reads_zero() {
        let inst = solve_first("some sig H { r: Real }\nfact { no H.r }\nrun {}");
        let s = instance_alloy_hinted(&inst, &real_hints());
        assert!(s.contains("H$0.r = {} = 0 [m=0 e=0]"), "got: {s}");
    }

    #[test]
    fn ints_aggregate_as_int_set() {
        let inst = solve_first("sig A {}\nrun {} for 8 Int");
        let s = instance_alloy_hinted(&inst, &DisplayHints::default());
        assert!(
            s.contains("Int = {0, 1, 2, 3, 4, 5, 6, 7}"),
            "got: {s}"
        );
        // Empty int layer keeps the bare header.
        let inst = solve_first("sig A {}\nrun {}");
        let s = instance_alloy_hinted(&inst, &DisplayHints::default());
        assert!(!s.contains("Int ="), "got: {s}");
    }
}
