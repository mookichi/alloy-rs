//! Real/EReal-aware solution display for the `als` CLI.
//!
//! Port of the REPL decoder (`alloy-repl/src/fmt.rs`): raw
//! `Real.m`/`Real.e`/`EReal.p`/`EReal.k` lane tuples are unreadable bit
//! sets (and carry ghost tuples for atoms outside the solved extent,
//! which the solver leaves unconstrained), so they are hidden whenever
//! decoding succeeds and member atoms print as `Real$i = c` /
//! `EReal$i = c ± R [m=.. e=.. p=.. k=..]`.
//! The surrounding shape intentionally matches the kodkod `Instance`
//! `Display` (`relations:` / `ints:` with `[[...]]` tuple sets) so
//! non-Real output is byte-identical.

use std::collections::{BTreeMap, HashSet};

use alloy_kodkod_rs::instance::Instance;
use alloy_kodkod_rs::mepk::Mepk;
use alloy_kodkod_rs::real::RealCenter;
use alloy_kodkod_rs::tupleset::TupleSet;
use alloy_kodkod_rs::universe::Universe;

/// One decoded member atom: raw lanes plus the one-line guarantee reading.
#[derive(Clone, Debug)]
pub struct DecodedEreal {
    /// `(m, e, p, k)` lane values (`p`/`k` are 0 for pure-`Real` atoms).
    pub lanes: (i64, i64, i64, i64),
    /// `c ± R [m=.. e=.. p=.. k=..]` for `EReal` members, `c [m=.. e=..]`
    /// for pure-`Real` members (or an ill-formed-lanes note).
    pub text: String,
}

fn atom_name(universe: &Universe, idx: u32) -> String {
    universe
        .atom(idx as usize)
        .map(|s| s.to_string())
        .unwrap_or_else(|_| "?".to_string())
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
/// Empty bit sets read as 0 (unconstrained lanes).
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

/// Decode every member `Real$i`/`EReal$i` atom to its lanes plus a
/// one-line display (`None` when the instance carries no `Real` lanes).
/// `EReal` members with full lanes show `c ± R`; pure-`Real` members
/// show the exact centre `c`. Tuples owned by atoms outside the solved
/// extents (solver leftovers on unused scope atoms) are skipped, never shown.
pub fn decode_ereal(inst: &Instance) -> Option<BTreeMap<u32, DecodedEreal>> {
    let universe = inst.universe();
    let size = universe.size() as i64;
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
    let mut out: BTreeMap<u32, DecodedEreal> = BTreeMap::new();
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
        // `EReal` members with decodable `p`/`k` lanes keep the legacy
        // `c ± R` reading; everything else reads the exact centre.
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
        let (text, lanes) = match pk_vals {
            Some((p, k)) => match Mepk::new(m as i128, e as i32, p as u32, k as i32) {
                Some(v) => (
                    format!("{} [m={m} e={e} p={p} k={k}]", v.interval_string(0)),
                    (m, e, p, k),
                ),
                None => (
                    format!("(ill-formed lanes m={m} e={e} p={p} k={k})"),
                    (m, e, p, k),
                ),
            },
            None => match RealCenter::new(m as i128, e as i32) {
                Some(v) => (format!("{} [m={m} e={e}]", v.centre_short()), (m, e, 0, 0)),
                None => (format!("(ill-formed lanes m={m} e={e})"), (m, e, 0, 0)),
            },
        };
        out.insert(owner, DecodedEreal { lanes, text });
    }
    Some(out)
}

/// Instance display with Real/EReal decoding: same `relations:`/`ints:`
/// shape as the kodkod `Display`, except raw lane relations are hidden
/// when decoding succeeds and member atoms gain `Real$i = ...` /
/// `EReal$i = ...` lines after the `Real = ...` / `EReal = ...` lines.
pub fn format_instance(inst: &Instance) -> String {
    let ereal = decode_ereal(inst);
    let mut out = String::from("relations:");
    for (r, ts) in inst.relation_tuples() {
        let name = inst.pool().name(r);
        let name_s: &str = &name;
        if ereal.is_some() && is_ereal_lane(name_s) {
            continue;
        }
        // Newline shape mirrors the kodkod `Display` (`writeln!` per line)
        // so lane-free output stays byte-identical.
        out.push_str(&format!("\n {name}->{ts}\n"));
        if name_s == "Real" || name_s == "EReal" {
            if let Some(ref ev) = ereal {
                for (idx, dec) in ev.iter() {
                    let atom = atom_name(inst.universe(), *idx);
                    // Decoded lines belong to their own sig block only
                    // (`Real` members under `Real`, `EReal` under `EReal`).
                    let is_ereal_atom = atom.starts_with("EReal$");
                    if (name_s == "EReal") != is_ereal_atom {
                        continue;
                    }
                    out.push_str(&format!(" {atom} = {}\n", dec.text));
                }
            }
        }
    }
    out.push_str("\nints:");
    for (i, ts) in inst.int_tuples() {
        out.push_str(&format!("\n {i}->{ts}\n"));
    }
    out
}

/// Render a `:query` value against `inst`: integers and booleans print
/// plainly; unary sets decode `EReal` members (`{EReal$0 = c ± R ...}`);
/// n-ary sets print raw `A->B` tuples (column types are unavailable here);
/// empty sets print `{}`.
pub fn format_query_value(inst: &Instance, v: &crate::snippet::QueryValue) -> String {
    use crate::snippet::QueryValue;
    match v {
        QueryValue::Int(i) => format!("{i}"),
        QueryValue::Bool(b) => format!("{b}"),
        QueryValue::Real(c) => format!("{} [m={} e={}]", c.centre_short(), c.m, c.e),
        QueryValue::Set(1, ts) => {
            let decoded = decode_ereal(inst).unwrap_or_default();
            format_atom_set(inst, &decoded, ts.index_view().iter().map(|i| i as u32))
        }
        QueryValue::Set(n, ts) => {
            let size = inst.universe().size() as i64;
            let inner = ts
                .index_view()
                .iter()
                .map(|flat| {
                    digits(size, *n, flat)
                        .iter()
                        .map(|&d| atom_name(inst.universe(), d))
                        .collect::<Vec<_>>()
                        .join("->")
                })
                .collect::<Vec<_>>()
                .join(", ");
            format!("{{{inner}}}")
        }
    }
}

/// `false` query answers fail the process (mirrors the old `run {expr}`
/// UNSAT exit code, so `-e` keeps working as a scripted assertion).
pub fn query_exit_ok(v: &crate::snippet::QueryValue) -> bool {
    !matches!(v, crate::snippet::QueryValue::Bool(false))
}

/// Render the atoms of a unary instance relation, decoding `EReal` members
/// via `decoded` (missing entry = plain atom name).
pub fn format_atom_set(
    inst: &Instance,
    decoded: &BTreeMap<u32, DecodedEreal>,
    idxs: impl Iterator<Item = u32>,
) -> String {
    let parts: Vec<String> = idxs
        .map(|i| match decoded.get(&i) {
            Some(d) => format!("{} = {}", atom_name(inst.universe(), i), d.text),
            None => atom_name(inst.universe(), i),
        })
        .collect();
    format!("{{{}}}", parts.join(", "))
}
