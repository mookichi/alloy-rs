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
    /// Field keys `Owner.field` with `EReal` range (rows decode to
    /// `c ± R` instead of raw `->EReal$i` tuples).
    pub ereal_fields: HashSet<String>,
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

/// True for the builtin lane relations (`Real.m`/`Real.e` shared centre
/// lanes plus the `EReal`-only `EReal.p`/`EReal.k`).
fn is_ereal_lane(name: &str) -> bool {
    matches!(name, "Real.m" | "Real.e" | "EReal.p" | "EReal.k")
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

/// True for the builtin bit-domain sigs (`$M`/`$E`/`$P`/`$K`):
/// domains, never decoded as values themselves.
fn is_lane_domain(name: &str) -> bool {
    matches!(name, "$M" | "$E" | "$P" | "$K")
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

/// Per-owner rows for a binary relation whose value columns decode as
/// bit sets: `X$0.r = {M$0, ...} = 0.5 [m=.. e=..]`. Rows that do not
/// decode keep the per-owner `{X$0->...}` shape. `None` when no row
/// decodes at all (callers keep the legacy full-relation shape).
/// `owners` overrides the row list (empty = first columns seen).
pub fn bitset_field_rows_ts(
    universe: &Universe,
    _owner: &str,
    field: &str,
    ts: &TupleSet,
    owners: Vec<u32>,
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
        let text = decode_bitset(universe, cols);
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
/// relation when present).
pub fn bitset_field_rows(
    inst: &Instance,
    owner: &str,
    field: &str,
    ts: &TupleSet,
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
    bitset_field_rows_ts(inst.universe(), owner, field, ts, owners)
}

/// Decode every `Real$i`/`EReal$i` atom to its lanes plus a one-line
/// display: `EReal` members with full lanes show `c ± R`, pure-`Real`
/// members show the exact centre `c`.
/// `None` when the instance carries no `Real` lanes (legacy path kept).
fn decode_ereal(inst: &Instance) -> Option<BTreeMap<u32, ((i64, i64, i64, i64), String)>> {
    let universe = inst.universe();
    let size = universe.size() as i64;
    // Lane relations present?
    let mut lanes: BTreeMap<&str, &TupleSet> = BTreeMap::new();
    for (r, ts) in inst.relation_tuples() {
        let name = inst.pool().name(r);
        match name.as_ref() {
            "Real.m" => {
                lanes.insert("m", ts);
            }
            "Real.e" => {
                lanes.insert("e", ts);
            }
            "EReal.p" => {
                lanes.insert("p", ts);
            }
            "EReal.k" => {
                lanes.insert("k", ts);
            }
            _ => {}
        }
    }
    if lanes.get("m").is_none() || lanes.get("e").is_none() {
        return None;
    }
    let me_prefixes = [("m", "M"), ("e", "E")];
    let me_widths: Vec<i64> = me_prefixes
        .iter()
        .map(|(_, pre)| lane_width(universe, pre))
        .collect::<Option<_>>()?;
    let pk_prefixes = [("p", "P"), ("k", "K")];
    let pk_widths: Option<Vec<i64>> = pk_prefixes
        .iter()
        .map(|(_, pre)| lane_width(universe, pre))
        .collect();
    // Owner atom -> (m/e bits, p/k bits).
    let mut rows: BTreeMap<u32, ([Vec<i64>; 2], [Vec<i64>; 2])> = BTreeMap::new();
    for (li, (lane, _)) in me_prefixes.iter().enumerate() {
        let ts = lanes[lane];
        if ts.arity() != 2 {
            return None;
        }
        for flat in ts.index_view().iter() {
            let d = digits(size, 2, flat);
            if d.len() < 2 {
                return None;
            }
            let bit = lane_pos(universe, d[1], me_prefixes[li].1)?;
            rows.entry(d[0]).or_default().0[li].push(bit);
        }
    }
    if lanes.contains_key("p") && lanes.contains_key("k") && pk_widths.is_some() {
        for (li, (lane, _)) in pk_prefixes.iter().enumerate() {
            let ts = lanes[lane];
            if ts.arity() != 2 {
                return None;
            }
            for flat in ts.index_view().iter() {
                let d = digits(size, 2, flat);
                if d.len() < 2 {
                    return None;
                }
                let bit = lane_pos(universe, d[1], pk_prefixes[li].1)?;
                rows.entry(d[0]).or_default().1[li].push(bit);
            }
        }
    }
    let mut out: BTreeMap<u32, ((i64, i64, i64, i64), String)> = BTreeMap::new();
    // Only atoms actually in the `Real`/`EReal` relations decode; sibling
    // atoms outside the solved extents (e.g. excluded by an extender's
    // `one`) have unconstrained lanes and would print as noise.
    let mut members: HashSet<u32> = HashSet::new();
    let mut ereal_members: HashSet<u32> = HashSet::new();
    for (r, ts) in inst.relation_tuples() {
        let name = inst.pool().name(r);
        if ts.arity() != 1 {
            continue;
        }
        if name.as_ref() == "Real" || name.as_ref() == "EReal" {
            members.extend(ts.index_view().iter().map(|i| i as u32));
        }
        if name.as_ref() == "EReal" {
            ereal_members.extend(ts.index_view().iter().map(|i| i as u32));
        }
    }
    for (owner, (me_bits, pk_bits)) in rows {
        if !members.contains(&owner) {
            continue;
        }
        // `EReal`-population atoms (`EReal$i`) outside the solved `EReal`
        // extent are scope leftovers with unconstrained lanes (legacy
        // ghost-lane rule); genuine `Real` members always decode.
        let atom = atom_name(universe, owner);
        if atom.starts_with("EReal$") && !ereal_members.contains(&owner) {
            continue;
        }
        let me_vals: Vec<i64> = me_bits
            .iter()
            .zip(me_widths.iter())
            .map(|(b, w)| lane_value(*w, b.iter().copied()))
            .collect::<Option<_>>()?;
        let (m, e) = (me_vals[0], me_vals[1]);
        let pk_vals: Option<(i64, i64)> = match (&pk_widths, ereal_members.contains(&owner)) {
            (Some(ws), true) => {
                let vs: Option<Vec<i64>> = pk_bits
                    .iter()
                    .zip(ws.iter())
                    .map(|(b, w)| lane_value(*w, b.iter().copied()))
                    .collect();
                vs.map(|v| (v[0], v[1]))
            }
            _ => None,
        };
        let (lanes4, text) = match pk_vals {
            Some((p, k)) => match Mepk::new(m as i128, e as i32, p as u32, k as i32) {
                Some(v) => ((m, e, p, k), format!("{} [m={m} e={e} p={p} k={k}]", v.interval_string(0))),
                None => ((m, e, p, k), format!("(ill-formed lanes m={m} e={e} p={p} k={k})")),
            },
            None => match alloy_kodkod_rs::real::RealCenter::new(m as i128, e as i32) {
                Some(v) => ((m, e, 0, 0), format!("{} [m={m} e={e}]", v.centre_short())),
                None => ((m, e, 0, 0), format!("(ill-formed lanes m={m} e={e})")),
            },
        };
        out.insert(owner, (lanes4, text));
    }
    Some(out)
}

/// Per-owner rows for an `Owner.field` relation whose range is `EReal`:
/// `X$0.r = <c ± R>`, multi-mapped rows list each value in `{...}`.
fn ereal_field_rows(
    inst: &Instance,
    owner: &str,
    field: &str,
    ts: &TupleSet,
    ev: &BTreeMap<u32, ((i64, i64, i64, i64), String)>,
) -> String {
    let universe = inst.universe();
    let size = universe.size() as i64;
    let mut groups: BTreeMap<u32, Vec<u32>> = BTreeMap::new();
    for flat in ts.index_view().iter() {
        let d = digits(size, ts.arity(), flat);
        if d.len() >= 2 {
            groups.entry(d[0]).or_default().push(d[1]);
        }
    }
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
    let mut out = String::new();
    for o in owners {
        let oname = atom_name(universe, o);
        let empty: Vec<u32> = Vec::new();
        let cols = groups.get(&o).unwrap_or(&empty);
        let vals: Vec<String> = cols
            .iter()
            .map(|c| {
                ev.get(c)
                    .map(|(_, t)| t.clone())
                    .unwrap_or_else(|| atom_name(universe, *c))
            })
            .collect();
        let line = if vals.len() == 1 {
            format!("{oname}.{field} = {}", vals[0])
        } else {
            format!("{oname}.{field} = {{{}}}", vals.join(", "))
        };
        out.push_str(&format!("\n {line}"));
    }
    out
}

/// Relations named in `signed` (Signed-rooted sigs) render unary int-atom
/// sets as their bitmask value (`S = 85`); binary `Owner.field` relations
/// in `signed_fields` decompose per owner atom (`X$0.s = 123`).
/// `EReal` lanes decode to `c ± R` per atom; `ereal_fields` decompose
/// per owner atom the same way. Everything else keeps the `{...}` set shape.
pub fn instance_alloy_hinted(inst: &Instance, hints: &DisplayHints) -> String {
    let ereal = decode_ereal(inst);
    let mut out = String::from("relations:");
    for (r, ts) in inst.relation_tuples() {
        let name = inst.pool().name(r);
        let name_s: &str = &name;
        // Raw `Real.m`/`Real.e`/`EReal.p`/`EReal.k` lane tuples are
        // unreadable bit sets; the decoded per-atom lines (emitted after
        // `Real = {...}` / `EReal = {...}`) replace them whenever decoding
        // succeeds.
        if ereal.is_some() && is_ereal_lane(name_s) {
            continue;
        }
        if ts.arity() == 2 {
            if let Some((owner, field)) = name_s.split_once('.') {
                if hints.signed_fields.contains(&format!("{owner}.{field}")) {
                    out.push_str(&field_rows_alloy(inst, owner, field, ts));
                    continue;
                }
                if let Some(ref ev) = ereal {
                    if hints.ereal_fields.contains(&format!("{owner}.{field}")) {
                        out.push_str(&ereal_field_rows(inst, owner, field, ts, ev));
                        continue;
                    }
                }
                // Flat bit-set rows decode alongside the raw tuples.
                if let Some(s) = bitset_field_rows(inst, owner, field, ts) {
                    out.push_str(&s);
                    continue;
                }
            }
        }
        let as_int = ts.arity() == 1 && hints.signed_sigs.contains(name_s);
        let expr = set_alloy_maybe_int(inst.universe(), ts.arity(), ts, as_int);
        // Flat bit sets gain their real-number reading alongside.
        let mut line = format!("\n {name} = {expr}");
        if ts.arity() == 1 && !as_int && !is_lane_domain(name_s) {
            let idxs: Vec<u32> = ts.index_view().iter().map(|i| i as u32).collect();
            if let Some(t) = decode_bitset(inst.universe(), &idxs) {
                line.push_str(&format!(" = {t}"));
            }
        }
        out.push_str(&line);
        // Decoded `Real$i`/`EReal$i` lines follow their own atom set.
        if name_s == "Real" || name_s == "EReal" {
            if let Some(ref ev) = ereal {
                for (idx, (_, text)) in ev.iter() {
                    let atom = atom_name(inst.universe(), *idx);
                    let is_ereal_atom = atom.starts_with("EReal$");
                    if (name_s == "EReal") != is_ereal_atom {
                        continue;
                    }
                    out.push_str(&format!("\n {atom} = {text}"));
                }
            }
        }
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
            ereal_fields: HashSet::new(),
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
            ereal_fields: HashSet::new(),
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
            ereal_fields: HashSet::new(),
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
            ereal_fields: HashSet::new(),
            signed_fields: ["Y.v".to_string()].into_iter().collect(),
        };
        let s = instance_alloy_hinted(&inst, &hints);
        assert!(s.contains("0.v = 1"), "got: {s}");
        assert!(s.contains("1.v = 6"), "got: {s}");
    }

    #[test]
    fn ereal_decodes_to_interval() {
        let src = "one sig X { r: one EReal }\nfact { all x: X | setEReal[x.r, 0.5] }\nrun {} for 1 EReal";
        let m = alloy_front_rs::parse_module(src).unwrap();
        let cnf = alloy_front_rs::run(&m, 0).unwrap();
        let inst = alloy_front_rs::solve(&cnf)
            .unwrap()
            .expect("SAT");
        let hints = DisplayHints {
            signed_sigs: HashSet::new(),
            signed_fields: HashSet::new(),
            ereal_fields: ["X.r".to_string()].into_iter().collect(),
        };
        let s = instance_alloy_hinted(&inst, &hints);
        assert!(!s.contains("Real.m ="), "raw lanes leaked: {s}");
        assert!(!s.contains("Real.e ="), "raw lanes leaked: {s}");
        assert!(!s.contains("EReal.p ="), "raw lanes leaked: {s}");
        assert!(!s.contains("EReal.k ="), "raw lanes leaked: {s}");
        // `$M`/`$E`/`$P`/`$K` are public builtin sigs: their atoms may
        // only appear inside their own lines, never in lane tuples.
        assert!(
            s.lines()
                .filter(|l| {
                    let t = l.trim_start();
                    !(t.starts_with("$M")
                        || t.starts_with("$E")
                        || t.starts_with("$P")
                        || t.starts_with("$K"))
                })
                .all(|l| !l.contains("M$")
                    && !l.contains("E$")
                    && !l.contains("P$")
                    && !l.contains("K$")),
            "raw lane atoms leaked outside $M/$E/$P/$K lines: {s}"
        );
        assert!(s.contains("EReal$0 = 0.5"), "got: {s}");
        assert!(s.contains("X$0.r = 0.5"), "got: {s}");
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
        let inst = solve_first(
            "one sig R1 extends EReal {}\nfact { setEReal[R1, 0.5] }\nrun {} for 2 EReal",
        );
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
}
