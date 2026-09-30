//! Real/EReal-aware solution display for the `als` CLI.
//!
//! A value *is* the set of its lane bits, so there is nothing to
//! reify: a unary set of `M$`/`E$` atoms reads as an exact centre
//! (`0.5 [m=1 e=-1]`) and one carrying `P$`/`K$` atoms as an error
//! interval (`2.5 ± 0.125 [m=10 e=1 p=4 k=0]`). The type domains
//! (`Real`, `EReal`) and the lane sigs themselves stay raw.
//! The surrounding shape intentionally matches the kodkod `Instance`
//! `Display` (`relations:` / `ints:` with `[[...]]` tuple sets) so
//! non-Real output is byte-identical.


use std::collections::BTreeMap;

use alloy_kodkod_rs::instance::Instance;
use alloy_kodkod_rs::mepk::Mepk;
use alloy_kodkod_rs::real::RealCenter;
use alloy_kodkod_rs::tupleset::TupleSet;
use alloy_kodkod_rs::universe::Universe;

fn atom_name(universe: &Universe, idx: u32) -> String {
    universe
        .atom(idx as usize)
        .map(|s| s.to_string())
        .unwrap_or_else(|_| "?".to_string())
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
/// set read as 0. Mirrors the REPL decoder (`alloy-repl/src/fmt.rs`).
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
/// bit sets: `X$0.r = {M$0, ...} = 0.5 [m=.. e=..]`. `None` when no row
/// decodes at all (callers keep the legacy full-relation shape), so
/// lane-free output stays byte-identical.
pub fn bitset_field_rows(
    inst: &Instance,
    owner: &str,
    field: &str,
    ts: &TupleSet,
) -> Option<String> {
    if ts.arity() != 2 {
        return None;
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
    // Owner atoms in instance order: the owner sig relation if present.
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
            Some(t) => out.push_str(&format!(" {oname}.{field} = {{{raw}}} = {t}\n")),
            None => out.push_str(&format!(" {oname}.{field} = {{{raw}}}\n")),
        }
    }
    Some(out)
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

/// Instance display: same `relations:`/`ints:` shape as the kodkod
/// `Display`, except a value (a set of lane bits) gains its real-number
/// or interval reading alongside the raw set.
pub fn format_instance(inst: &Instance) -> String {
    let mut out = String::from("relations:");
    for (r, ts) in inst.relation_tuples() {
        let name = inst.pool().name(r);
        let name_s: &str = &name;
        // Flat bit-set rows decode alongside the raw tuples (fields);
        // untouched relations keep the legacy shape (byte-identical).
        if ts.arity() == 2 {
            if let Some((owner, field)) = name_s.split_once('.') {
                if let Some(s) = bitset_field_rows(inst, owner, field, ts) {
                    out.push_str(&s);
                    continue;
                }
            }
        }
        // Newline shape mirrors the kodkod `Display` (`writeln!` per line)
        // so lane-free output stays byte-identical.
        // Flat bit sets gain their real-number reading alongside.
        if ts.arity() == 1 && !is_lane_domain(name_s) {
            let idxs: Vec<u32> = ts.index_view().iter().map(|i| i as u32).collect();
            if let Some(t) = decode_bitset(inst.universe(), &idxs) {
                out.push_str(&format!("\n {name}->{ts} = {t}\n"));
                continue;
            }
        }
        out.push_str(&format!("\n {name}->{ts}\n"));
    }
    out.push_str("\nints:");
    for (i, ts) in inst.int_tuples() {
        out.push_str(&format!("\n {i}->{ts}\n"));
    }
    out
}

/// Render a `:query` value against `inst`: integers and booleans print
/// plainly; unary sets of lane bits gain their real-number / interval
/// reading (`{M$0, E$0} = 2 [m=1 e=1]`); n-ary sets print raw `A->B`
/// tuples (column types are unavailable here); empty sets print `{}`.
pub fn format_query_value(inst: &Instance, v: &crate::snippet::QueryValue) -> String {
    use crate::snippet::QueryValue;
    match v {
        QueryValue::Int(i) => format!("{i}"),
        QueryValue::Bool(b) => format!("{b}"),
        QueryValue::Real(c) => format!("{} [m={} e={}]", c.centre_short(), c.m, c.e),
        QueryValue::Set(1, ts) => {
            // A value is a set of lane bits, so it gains its real-number
            // or interval reading alongside the raw atom list.
            let idxs: Vec<u32> = ts.index_view().iter().map(|i| i as u32).collect();
            let inner = format_atom_set(inst, idxs.iter().copied());
            match decode_bitset(inst.universe(), &idxs) {
                Some(t) => format!("{inner} = {t}"),
                None => inner,
            }
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

/// Render the atoms of a unary instance relation as a set.
pub fn format_atom_set(inst: &Instance, idxs: impl Iterator<Item = u32>) -> String {
    let parts: Vec<String> = idxs.map(|i| atom_name(inst.universe(), i)).collect();
    format!("{{{}}}", parts.join(", "))
}
