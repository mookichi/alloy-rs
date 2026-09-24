//! EReal-aware solution display for the `als` CLI.
//!
//! Port of the REPL decoder (`alloy-repl/src/fmt.rs`): raw
//! `EReal.m/e/p/k` lane tuples are unreadable bit sets (and carry ghost
//! tuples for atoms outside the solved `EReal` extent, which the solver
//! leaves unconstrained), so they are hidden whenever decoding succeeds
//! and member atoms print as `EReal$i = c ± R [m=.. e=.. p=.. k=..]`.
//! The surrounding shape intentionally matches the kodkod `Instance`
//! `Display` (`relations:` / `ints:` with `[[...]]` tuple sets) so
//! non-EReal output is byte-identical.

use std::collections::{BTreeMap, HashSet};

use alloy_kodkod_rs::instance::Instance;
use alloy_kodkod_rs::mepk::Mepk;
use alloy_kodkod_rs::tupleset::TupleSet;
use alloy_kodkod_rs::universe::Universe;

/// One decoded member atom: raw lanes plus the one-line guarantee reading.
#[derive(Clone, Debug)]
pub struct DecodedEreal {
    /// `(m, e, p, k)` lane values.
    pub lanes: (i64, i64, i64, i64),
    /// `c ± R [m=.. e=.. p=.. k=..]` (or an ill-formed-lanes note).
    pub text: String,
}

fn atom_name(universe: &Universe, idx: u32) -> String {
    universe
        .atom(idx as usize)
        .map(|s| s.to_string())
        .unwrap_or_else(|_| "?".to_string())
}

/// True for the builtin lane relations (`EReal.m/e/p/k`).
fn is_ereal_lane(name: &str) -> bool {
    matches!(name, "EReal.m" | "EReal.e" | "EReal.p" | "EReal.k")
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

/// Decode every member `EReal$i` atom to its lanes plus a one-line
/// `c ± R` display (`None` when the instance carries no EReal lanes).
/// Tuples owned by atoms outside the solved `EReal` extent (solver leftovers
/// on unused scope atoms) are skipped, never shown.
pub fn decode_ereal(inst: &Instance) -> Option<BTreeMap<u32, DecodedEreal>> {
    let universe = inst.universe();
    let size = universe.size() as i64;
    let mut lanes: BTreeMap<&str, &TupleSet> = BTreeMap::new();
    for (r, ts) in inst.relation_tuples() {
        let name = inst.pool().name(r);
        match name.as_ref() {
            "EReal.m" => {
                lanes.insert("m", ts);
            }
            "EReal.e" => {
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
    if lanes.len() != 4 {
        return None;
    }
    let prefixes = [("m", "M"), ("e", "E"), ("p", "P"), ("k", "K")];
    let widths: Vec<i64> = prefixes
        .iter()
        .map(|(_, pre)| lane_width(universe, pre))
        .collect::<Option<_>>()?;
    let mut rows: BTreeMap<u32, [Vec<i64>; 4]> = BTreeMap::new();
    for (li, (lane, _)) in prefixes.iter().enumerate() {
        let ts = lanes[lane];
        if ts.arity() != 2 {
            return None;
        }
        for flat in ts.index_view().iter() {
            let d = digits(size, 2, flat);
            if d.len() < 2 {
                return None;
            }
            let bit = lane_pos(universe, d[1], prefixes[li].1)?;
            rows.entry(d[0]).or_default()[li].push(bit);
        }
    }
    let mut members: Option<HashSet<u32>> = None;
    for (r, ts) in inst.relation_tuples() {
        if inst.pool().name(r).as_ref() == "EReal" && ts.arity() == 1 {
            members = Some(ts.index_view().iter().map(|i| i as u32).collect());
            break;
        }
    }
    let mut out: BTreeMap<u32, DecodedEreal> = BTreeMap::new();
    for (owner, bits) in rows {
        if let Some(ref m) = members {
            if !m.contains(&owner) {
                continue;
            }
        }
        let vals: Vec<i64> = bits
            .iter()
            .zip(widths.iter())
            .map(|(b, w)| lane_value(*w, b.iter().copied()))
            .collect::<Option<_>>()?;
        let (m, e, p, k) = (vals[0], vals[1], vals[2], vals[3]);
        let text = match Mepk::new(m as i128, e as i32, p as u32, k as i32) {
            Some(v) => format!("{} [m={m} e={e} p={p} k={k}]", v.interval_string(0)),
            None => format!("(ill-formed lanes m={m} e={e} p={p} k={k})"),
        };
        out.insert(owner, DecodedEreal { lanes: (m, e, p, k), text });
    }
    Some(out)
}

/// Instance display with EReal decoding: same `relations:`/`ints:` shape
/// as the kodkod `Display`, except raw lane relations are hidden when
/// decoding succeeds and member atoms gain `EReal$i = ...` lines after
/// the `EReal = ...` line.
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
        if name_s == "EReal" {
            if let Some(ref ev) = ereal {
                for (idx, dec) in ev.iter() {
                    out.push_str(&format!(
                        " {} = {}\n",
                        atom_name(inst.universe(), *idx),
                        dec.text
                    ));
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
