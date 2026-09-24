//! `:mepk` REPL command: evaluate `(m, e, p, k)` error-tracking arithmetic.
//!
//! Each invocation runs the **concrete oracle** (`mepk_add/mul/div`) and
//! cross-checks the **symbolic exponent layer** (`mepk_*_c` over constant
//! circuits), printing both plus a MATCH/MISMATCH verdict.
//!
//! Usage:
//! ```text
//! :mepk [-v] add|sub|mul|div (<m,e,p,k>|lit <dec>) (<m,e,p,k>|lit <dec>) [p <maxp>] [n <n>]
//! :mepk [-v] lit <decimal> [p <maxp>] [n <intcount>]
//! :mepk widths [n]
//! ```
//! Normal output is one guarantee line per result (`7 ± 1 (tau=2)`);
//! `-v` adds widths, raw tuples, full digits, and symbolic detail.
//!
//! Widths come from `MepkWidths::from_env(int_count)` (`MEPK_*_WIDTH`
//! overrides, else the `for n Int` rule; default `n = 4`). The `m` lane is
//! auto-widened past the rule when the inputs don't fit (echoed in `-v`). `lit` converts a decimal real literal with optimal
//! precision (exact when dyadic, else rounded); its default cap is the
//! usable mantissa precision `m_width - 1`.

use alloy_kodkod_rs::mepk::{
    decimal_to_mepk, mepk_add, mepk_add_c, mepk_div, mepk_div_c, mepk_mul, mepk_mul_c, Mepk,
    MepkCircuit, MepkWidths,
};
use alloy_kodkod_rs::BoolCtx;

pub const USAGE: &str = "usage: :mepk [-v] add|sub|mul|div (<m,e,p,k>|lit <decimal>) (<m,e,p,k>|lit <decimal>) [p <maxp>] [n <intcount>] | :mepk [-v] lit <decimal> [p <maxp>] [n <intcount>] | :mepk widths [n]";
pub const SENS_USAGE: &str = "usage: :sens [-v] add|sub|mul|div (<m,e,p,k>|lit <decimal>) (<m,e,p,k>|lit <decimal>) [p <maxp>] [n <intcount>]";

fn parse_tuple(s: &str) -> Option<Mepk> {
    let parts: Vec<&str> = s.split(',').collect();
    if parts.len() != 4 {
        return None;
    }
    let m: i128 = parts[0].trim().parse().ok()?;
    let e: i32 = parts[1].trim().parse().ok()?;
    let p: u32 = parts[2].trim().parse().ok()?;
    let k: i32 = parts[3].trim().parse().ok()?;
    Mepk::new(m, e, p, k)
}

/// Minimum signed two's-complement width holding `v`.
fn signed_need(v: i128) -> u32 {
    if v == 0 {
        1
    } else {
        let mag = v.unsigned_abs();
        (128 - mag.leading_zeros()) + 1
    }
}

/// Effective widths: rule/env base, widened so the inputs fit
/// (m lane exactly; e/k lanes with +2 headroom for computed growth).
fn effective_widths(base: &MepkWidths, x1: &Mepk, x2: &Mepk) -> MepkWidths {
    let need_m = signed_need(x1.m).max(signed_need(x2.m)).max(2);
    let need_e = signed_need(x1.e as i128)
        .max(signed_need(x2.e as i128))
        .max(2);
    let need_k = signed_need(x1.k as i128)
        .max(signed_need(x2.k as i128))
        .max(2);
    let need_p = (x1.p.max(x2.p) + 1).max(2);
    base.clone()
        .with_m_width(base.m_width.max(need_m))
        .with_e_width(base.e_width.max(need_e + 2))
        .with_p_width(base.p_width.max(need_p))
        .with_k_width(base.k_width.max(need_k + 2))
}

fn fmt_mepk(x: &Mepk) -> String {
    format!("(m={}, e={}, p={}, k={})", x.m, x.e, x.p, x.k)
}

fn parse_n(args: &[&str]) -> Result<(Vec<String>, u32), String> {
    let mut rest: Vec<String> = args.iter().map(|s| s.to_string()).collect();
    let mut n = 4u32;
    if let Some(pos) = rest.iter().position(|s| s == "n") {
        if pos + 1 >= rest.len() {
            return Err(USAGE.to_string());
        }
        n = rest[pos + 1].parse().map_err(|_| USAGE.to_string())?;
        if n == 0 || n > 30 {
            return Err("intcount n must satisfy 1 <= n <= 30".to_string());
        }
        rest.drain(pos..pos + 2);
    }
    Ok((rest, n))
}

/// Split off a `key value` option (e.g. `p 8`), returning the remaining
/// args and the parsed value (or `None` when absent).
fn take_option(args: &mut Vec<String>, key: &str) -> Result<Option<u32>, String> {
    let Some(pos) = args.iter().position(|s| s == key) else {
        return Ok(None);
    };
    if pos + 1 >= args.len() {
        return Err(USAGE.to_string());
    }
    let v: u32 = args[pos + 1].parse().map_err(|_| USAGE.to_string())?;
    args.drain(pos..pos + 2);
    Ok(Some(v))
}

/// Split off a bare `-v` flag, returning the remaining args and presence.
fn take_flag(args: &mut Vec<String>, flag: &str) -> bool {
    if let Some(pos) = args.iter().position(|s| s == flag) {
        args.remove(pos);
        true
    } else {
        false
    }
}
/// Run a `:mepk` command body (tokens after `:mepk`), returning output lines.
pub fn run_mepk(args: &[&str]) -> Vec<String> {
    if args.is_empty() {
        return vec![USAGE.to_string()];
    }
    // `:mepk lit <decimal> [p <maxp>] [n <intcount>]`
    if args[0] == "lit" {
        return lit_command(&args[1..]);
    }
    // `:mepk widths [n <intcount>]`
    if args[0] == "widths" {
        let (rest, n) = match parse_n(&args[1..]) {
            Ok(v) => v,
            Err(e) => return vec![e],
        };
        if !rest.is_empty() {
            return vec![USAGE.to_string()];
        }
        match MepkWidths::from_env(n) {
            Err(e) => vec![format!("widths error: {e}")],
            Ok(w) => vec![format!(
                "n={n}: m={} e={} p={} k={} guard={}",
                w.m_width, w.e_width, w.p_width, w.k_width, w.guard
            )],
        }
    } else {
        op_command(args)
    }
}

/// `:mepk [-v] lit <decimal> [p <maxp>] [n <intcount>]`: convert a decimal
/// real literal with optimal precision (exact when dyadic, else rounded
/// to nearest). The default cap is the usable mantissa precision
/// `m_width - 1` from the active widths. `-v` adds the raw tuple and
/// full centre digits.
fn lit_command(args: &[&str]) -> Vec<String> {
    let (mut rest, n) = match parse_n(args) {
        Ok(v) => v,
        Err(e) => return vec![e],
    };
    let verbose = take_flag(&mut rest, "-v");
    let max_p_opt = match take_option(&mut rest, "p") {
        Ok(v) => v,
        Err(e) => return vec![e],
    };
    if rest.len() != 1 {
        return vec![USAGE.to_string()];
    }
    let lit = rest[0].as_str();
    let widths = match MepkWidths::from_env(n) {
        Err(e) => return vec![format!("widths error: {e}")],
        Ok(w) => w,
    };
    let max_p = match resolve_max_p(max_p_opt, &widths) {
        Ok(p) => p,
        Err(e) => return vec![e],
    };
    match decimal_to_mepk(lit, max_p) {
        None => vec![format!(
            "cannot convert {lit:?}: malformed literal or outside the i128 oracle range (e.g. 3.14, -0.1, 2.5, 1e-3)"
        )],
        Some(conv) => {
            let note = conv_note(&conv);
            let mut out = vec![
                format!("max_p={max_p} (n={n})"),
                format!("{} -> {} {note}", lit, conv.v.interval_string(0)),
            ];
            if verbose {
                out.push(format!("raw {}", fmt_mepk(&conv.v)));
                out.push(format!("full {}", conv.v.interval_string_full(0)));
            }
            out
        }
    }
}

/// Resolve the precision cap: explicit `p` (validated) or the usable
/// mantissa precision `m_width - 1` for normalized values.
fn resolve_max_p(max_p_opt: Option<u32>, widths: &MepkWidths) -> Result<u32, String> {
    match max_p_opt {
        Some(p) => {
            if p == 0 || p > 127 {
                return Err("precision cap p must satisfy 1 <= p <= 127".to_string());
            }
            Ok(p)
        }
        None => Ok(widths.m_width.saturating_sub(1).max(1)),
    }
}

/// One-line exactness note shared by `lit` output and operand expansion.
fn conv_note(conv: &alloy_kodkod_rs::mepk::DecimalConv) -> String {
    if conv.exact {
        match conv.min_p {
            Some(mp) if mp < conv.v.p => {
                format!("exact, padded to {} (minimal {mp})", conv.v.p)
            }
            _ => "exact, minimal precision".to_string(),
        }
    } else if conv.v.k == 1 {
        "rounded to nearest (not dyadic; k=1 guard)".to_string()
    } else {
        match conv.min_p {
            Some(mp) => format!("rounded to nearest at precision cap (needs p={mp})"),
            None => "rounded to nearest at precision cap".to_string(),
        }
    }
}

/// Parse one operand at `tokens[i]`: either a `<m,e,p,k>` tuple or
/// `lit <decimal>` (converted with `max_p`). Returns the value, the next
/// unconsumed index, an optional expansion note for `lit`, and whether the
/// operand came from a `lit` conversion (for `:sens` cap hints).
fn parse_operand(
    tokens: &[String],
    i: usize,
    max_p: u32,
) -> Result<(Mepk, usize, Option<String>, bool), String> {
    if i >= tokens.len() {
        return Err(USAGE.to_string());
    }
    if tokens[i] == "lit" {
        if i + 1 >= tokens.len() {
            return Err(USAGE.to_string());
        }
        let lit = tokens[i + 1].as_str();
        match decimal_to_mepk(lit, max_p) {
            None => Err(format!(
                "cannot convert {lit:?}: malformed literal or outside the i128 oracle range"
            )),
            Some(conv) => {
                let note = format!("lit {lit} -> {} {}", conv.v.interval_string(0), conv_note(&conv));
                Ok((conv.v, i + 2, Some(note), true))
            }
        }
    } else {
        match parse_tuple(&tokens[i]) {
            Some(v) => Ok((v, i + 1, None, false)),
            None => Err("bad tuple: expected <m,e,p,k> with p >= 1".to_string()),
        }
    }
}

/// Shared operand resolution for `:mepk` arithmetic and `:sens`.
/// Returns the op, both operands, effective widths, guard,
/// `lit` expansion notes, `lit`-origin flags, and the `-v` flag.
struct ResolvedOperands {
    op: String,
    x1: Mepk,
    x2: Mepk,
    widths: MepkWidths,
    guard: u32,
    note1: Option<String>,
    note2: Option<String>,
    lit1: bool,
    lit2: bool,
    verbose: bool,
}

fn resolve_operands(args: &[&str], usage: &str) -> Result<ResolvedOperands, String> {
    let (mut rest, n) = parse_n(args).map_err(|e| e)?;
    let verbose = take_flag(&mut rest, "-v");
    let max_p_opt = take_option(&mut rest, "p").map_err(|e| e)?;
    if rest.len() < 3 {
        return Err(usage.to_string());
    }
    let op = rest[0].clone();
    if !matches!(op.as_str(), "add" | "sub" | "mul" | "div") {
        return Err(usage.to_string());
    }
    let base = MepkWidths::from_env(n).map_err(|e| format!("widths error: {e}"))?;
    let max_p = resolve_max_p(max_p_opt, &base)?;
    let (x1, next, note1, lit1) = parse_operand(&rest, 1, max_p)?;
    let (x2, end, note2, lit2) = parse_operand(&rest, next, max_p)?;
    if end != rest.len() {
        return Err(usage.to_string());
    }
    let w = effective_widths(&base, &x1, &x2);
    let guard = w.guard;
    Ok(ResolvedOperands {
        op,
        x1,
        x2,
        widths: w,
        guard,
        note1,
        note2,
        lit1,
        lit2,
        verbose,
    })
}

/// Concrete oracle dispatch shared by `:mepk` and `:sens`.
fn apply_concrete(op: &str, x1: &Mepk, x2: &Mepk, guard: u32) -> Option<Mepk> {
    match op {
        "add" => mepk_add(x1, x2, 1),
        "sub" => mepk_add(x1, x2, -1),
        "mul" => mepk_mul(x1, x2),
        "div" => mepk_div(x1, x2, guard),
        _ => None,
    }
}

fn op_command(args: &[&str]) -> Vec<String> {
    let r = match resolve_operands(args, USAGE) {
        Ok(v) => v,
        Err(e) => return vec![e],
    };
    let w = r.widths;
    let guard = r.guard;
    let mut out = Vec::new();
    if r.verbose {
        out.push(format!(
            "widths: m={} e={} p={} k={} guard={}",
            w.m_width, w.e_width, w.p_width, w.k_width, w.guard
        ));
    }
    // Echo `lit` expansions so the converted operands are visible.
    for note in [r.note1, r.note2].into_iter().flatten() {
        out.push(note);
    }

    // Concrete oracle.
    let concrete = apply_concrete(&r.op, &r.x1, &r.x2, guard);
    match concrete {
        Some(v) => {
            out.push(v.interval_string(0));
            if r.verbose {
                out.push(format!("raw {}", fmt_mepk(&v)));
                out.push(format!("full {}", v.interval_string_full(0)));
            }
        }
        None => out.push("concrete DivisionUndefined (k2 >= p2) or overflow".to_string()),
    }

    // Symbolic cross-check over constant circuits.
    let ctx = BoolCtx::new();
    let x1 = r.x1;
    let x2 = r.x2;
    let op = r.op.as_str();
    let verbose = r.verbose;
    let a = MepkCircuit::constant(x1.m as i64, x1.e as i64, x1.p as i64, x1.k as i64, &w, &ctx);
    let b = MepkCircuit::constant(x2.m as i64, x2.e as i64, x2.p as i64, x2.k as i64, &w, &ctx);
    // Inputs must fit the lanes for the check to be meaningful.
    if x1.m as i64 as i128 != x1.m || x2.m as i64 as i128 != x2.m {
        out.push("symbolic skipped: |m| exceeds i64 demo range".to_string());
        return out;
    }
    let (se, sp, sk, undef) = match op {
        "add" => {
            let r = mepk_add_c(&a, &b, 1, &w);
            (r.e.value_of(&[]), r.p.value_of(&[]), r.k.value_of(&[]), false)
        }
        "sub" => {
            let r = mepk_add_c(&a, &b, -1, &w);
            (r.e.value_of(&[]), r.p.value_of(&[]), r.k.value_of(&[]), false)
        }
        "mul" => {
            let r = mepk_mul_c(&a, &b, &w);
            (r.e.value_of(&[]), r.p.value_of(&[]), r.k.value_of(&[]), false)
        }
        "div" => {
            let (r, u) = mepk_div_c(&a, &b, &w);
            (
                r.e.value_of(&[]),
                r.p.value_of(&[]),
                r.k.value_of(&[]),
                ctx.eval(u, &[]),
            )
        }
        _ => unreachable!(),
    };
    if verbose {
        out.push(format!("symbolic e={se} p={sp} k={sk} undef={undef}"));
    }
    // Verdict under the carry contract: exact agreement, or symbolic
    // within one round-up carry (`oracle_e - sym_e ∈ {0,1}`,
    // `sym_k - oracle_k ∈ {0,1}`).
    match (&concrete, op) {
        (Some(r), _) => {
            let exact = se == r.e as i64 && sp == r.p as i64 && sk == r.k as i64 && !undef;
            let tolerant = (r.e as i64 - se == 0 || r.e as i64 - se == 1)
                && (sk - r.k as i64 == 0 || sk - r.k as i64 == 1)
                && sp == r.p as i64
                && !undef;
            out.push(if exact {
                "MATCH: symbolic exponents agree with concrete".to_string()
            } else if tolerant {
                "MATCH (within carry tolerance: e/k conservative)".to_string()
            } else {
                "MISMATCH: symbolic exponents differ (width overflow?)".to_string()
            });
        }
        (None, "div") => out.push(if undef {
            "MATCH: both report DivisionUndefined (k2 >= p2)".to_string()
        } else {
            "MISMATCH: concrete undefined but symbolic undef=false".to_string()
        }),
        (None, _) => out.push("concrete overflow; symbolic result above for reference".to_string()),
    }
    out
}

// ---------------------------------------------------------------------------
// `:sens`: single-parameter sensitivity ranking (top 3) over the concrete
// oracle. Candidates are p1+1, p2+1, k1-1, k2-1 (guard excluded by design).
// Ranked by radius-exponent improvement (dR), tau change shown alongside.
// ---------------------------------------------------------------------------

/// Run a `:sens` command body (tokens after `:sens`), returning output lines.
pub fn run_sens(args: &[&str]) -> Vec<String> {
    if args.is_empty() {
        return vec![SENS_USAGE.to_string()];
    }
    sens_command(args)
}

/// Dominant error term of the op for the given inputs, naming the max
/// branch of A/C/D that governs `k'` (see `int_ext::{add_a,mul_c,div_d}`).
fn dominant_term(op: &str, x1: &Mepk, x2: &Mepk) -> String {
    match op {
        "add" | "sub" => {
            let ell = x1.lsb().min(x2.lsb());
            let d1 = x1.lsb() - ell;
            let d2 = x2.lsb() - ell;
            let t1 = x1.k + d1;
            let t2 = x2.k + d2;
            if t1 >= t2 {
                format!("dominant error term: k1+d1={t1} (op1 side; A=ell+max over k+d)")
            } else {
                format!("dominant error term: k2+d2={t2} (op2 side; A=ell+max over k+d)")
            }
        }
        "mul" => {
            let t1 = x1.k - x1.p as i32 + 1;
            let t2 = x2.k - x2.p as i32 + 1;
            let t3 = (x1.k + x2.k) - (x1.p as i32 + x2.p as i32);
            let m = t1.max(t2).max(t3);
            let which = if m == t3 && t3 >= t1 && t3 >= t2 {
                "k1+k2-p1-p2 (joint; raise p1 AND p2 together)"
            } else if m == t1 && t1 >= t2 {
                "k1-p1+1 (op1 side)"
            } else {
                "k2-p2+1 (op2 side)"
            };
            format!("dominant error term: {which} (C=e1+e2+max+2)")
        }
        "div" => {
            let u1 = x1.k - x1.p as i32;
            let u2 = x2.k - x2.p as i32;
            if u1 >= u2 {
                format!("dominant error term: k1-p1={u1} (numerator side; D=e1-e2+max+3)")
            } else {
                format!("dominant error term: k2-p2={u2} (denominator side; D=e1-e2+max+3)")
            }
        }
        _ => "dominant error term: unknown op".to_string(),
    }
}

struct SensRow {
    name: String,
    result: Mepk,
    dr: i32,
    dtau: i32,
    from_lit: bool,
}

fn sens_command(args: &[&str]) -> Vec<String> {
    let r = match resolve_operands(args, SENS_USAGE) {
        Ok(v) => v,
        Err(e) => return vec![e],
    };
    let mut out = Vec::new();
    if r.verbose {
        out.push(format!(
            "widths: m={} e={} p={} k={} guard={}",
            r.widths.m_width,
            r.widths.e_width,
            r.widths.p_width,
            r.widths.k_width,
            r.widths.guard
        ));
    }
    for note in [r.note1.clone(), r.note2.clone()].into_iter().flatten() {
        out.push(note);
    }
    let base = match apply_concrete(&r.op, &r.x1, &r.x2, r.guard) {
        Some(v) => v,
        None => {
            return vec![
                "base is undefined (DivisionUndefined k2>=p2 or overflow): no sensitivity to rank"
                    .to_string(),
            ]
        }
    };
    let base_r = base.radius_exp();
    let base_tau = base.tau(0);
    out.push(format!(
        "base: {} [r_exp={base_r}, tau={base_tau}] (guard={})",
        base.interval_string(0),
        r.guard
    ));
    out.push(dominant_term(&r.op, &r.x1, &r.x2));

    // Candidates: p+1 (cap 127), k-1 (floor at wellformed k>=0).
    let mut cands: Vec<(String, Mepk, bool)> = Vec::with_capacity(4);
    if r.x1.p < 127 {
        let mut v = r.x1;
        v.p += 1;
        cands.push(("p1+1".to_string(), v, r.lit1));
    } else {
        out.push("p1+1: skipped (at p cap 127)".to_string());
    }
    if r.x2.p < 127 {
        let mut v = r.x2;
        v.p += 1;
        cands.push(("p2+1".to_string(), v, r.lit2));
    } else {
        out.push("p2+1: skipped (at p cap 127)".to_string());
    }
    if r.x1.k > 0 {
        let mut v = r.x1;
        v.k -= 1;
        cands.push(("k1-1".to_string(), v, false));
    } else {
        out.push("k1-1: skipped (at floor wellformed k>=0)".to_string());
    }
    if r.x2.k > 0 {
        let mut v = r.x2;
        v.k -= 1;
        cands.push(("k2-1".to_string(), v, false));
    } else {
        out.push("k2-1: skipped (at floor wellformed k>=0)".to_string());
    }

    let mut rows: Vec<SensRow> = Vec::new();
    let mut failed: Vec<String> = Vec::new();
    for (name, pert, from_lit) in cands {
        // Name convention: p1/k1 perturb x1, p2/k2 perturb x2.
        let (qx1, qx2) = if name == "p1+1" || name == "k1-1" {
            (pert, r.x2)
        } else {
            (r.x1, pert)
        };
        match apply_concrete(&r.op, &qx1, &qx2, r.guard) {
            Some(res) => rows.push(SensRow {
                name,
                result: res,
                dr: res.radius_exp() - base_r,
                dtau: res.tau(0) - base_tau,
                from_lit,
            }),
            None => failed.push(name),
        }
    }
    for name in failed {
        out.push(format!("{name}: perturbs to undefined (overflow/div-guard); excluded"));
    }
    // Rank: dR ascending, then dTau descending, then name for stability.
    rows.sort_by(|a, b| {
        a.dr
            .cmp(&b.dr)
            .then(b.dtau.cmp(&a.dtau))
            .then(a.name.cmp(&b.name))
    });
    let improved: Vec<&SensRow> = rows
        .iter()
        .filter(|row| row.dr < 0 || row.dtau > 0)
        .collect();
    let unchanged: Vec<&SensRow> = rows
        .iter()
        .filter(|row| row.dr == 0 && row.dtau == 0)
        .collect();
    let worsened: Vec<&SensRow> = rows
        .iter()
        .filter(|row| !(row.dr < 0 || row.dtau > 0) && !(row.dr == 0 && row.dtau == 0))
        .collect();

    if improved.is_empty() {
        out.push(
            "note: saturated (err-dominated). No single p/k step shrinks R; try raising p1 AND p2 together, or lowering the dominant k".to_string(),
        );
    }
    // Top 3 improved with tie notation (`1t.` for equal (dR,dTau)).
    let mut prev_key: Option<(i32, i32)> = None;
    let mut prev_rank: usize = 0;
    for (i, row) in improved.iter().take(3).enumerate() {
        let key = (row.dr, row.dtau);
        let rank = if prev_key == Some(key) {
            format!("{prev_rank}t.")
        } else {
            prev_rank = i + 1;
            format!("{}.", prev_rank)
        };
        prev_key = Some(key);
        let lit_hint = if row.from_lit {
            " (lit: raise cap via `p <maxp>` / `n <n>`)".to_string()
        } else {
            String::new()
        };
        let dr_s = if row.dr == 0 {
            "0".to_string()
        } else {
            format!("{:+}", row.dr)
        };
        let dtau_s = if row.dtau == 0 {
            "0".to_string()
        } else {
            format!("{:+}", row.dtau)
        };
        let mut line = format!(
            "{rank} {}: {} [dR={dr_s}bit, dTau={dtau_s}]{lit_hint}",
            row.name,
            row.result.interval_string(0),
        );
        if r.verbose {
            line.push_str(&format!(" raw {}", fmt_mepk(&row.result)));
        }
        out.push(line);
    }
    for row in unchanged {
        out.push(format!(
            "— {}: no change ({})",
            row.name,
            row.result.interval_string(0)
        ));
    }
    for row in worsened {
        let dr_s = if row.dr == 0 {
            "0".to_string()
        } else {
            format!("{:+}", row.dr)
        };
        let dtau_s = if row.dtau == 0 {
            "0".to_string()
        } else {
            format!("{:+}", row.dtau)
        };
        out.push(format!(
            "— {}: worsens {} [dR={dr_s}bit, dTau={dtau_s}]",
            row.name,
            row.result.interval_string(0),
        ));
    }
    out.push("note: p' = min(p1,p2); only the minimum-p side (or dominant k-p term) moves R".to_string());
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sens_prefers_min_p_side() {
        // p1=4 < p2=8: p1+1 moves p'=min, p2+1 is a no-op.
        let lines = run_sens(&["add", "10,3,4,1", "50,5,8,1"]);
        assert!(lines.iter().any(|l| l.starts_with("base:")), "{lines:?}");
        assert!(lines.iter().any(|l| l.contains("dominant error term")), "{lines:?}");
        let top: Vec<&String> = lines.iter().filter(|l| l.starts_with("1")).collect();
        assert!(!top.is_empty(), "{lines:?}");
        assert!(top.iter().any(|l| l.contains("p1+1") && l.contains("dR=-1bit")), "{lines:?}");
        assert!(
            lines.iter().any(|l| l.starts_with("— p2+1: no change")),
            "{lines:?}"
        );
    }

    #[test]
    fn sens_k_floor_and_dominant_term() {
        // k=0 on both sides: k-1 candidates are skipped, not recommended.
        let lines = run_sens(&["add", "100,6,8,0", "50,5,8,0"]);
        assert!(
            lines.iter().any(|l| l.contains("k1-1: skipped (at floor wellformed k>=0)")),
            "{lines:?}"
        );
        assert!(
            lines.iter().any(|l| l.contains("k2-1: skipped (at floor wellformed k>=0)")),
            "{lines:?}"
        );
        // mul names the dominant max branch.
        let lines = run_sens(&["mul", "100,6,8,1", "50,5,8,2"]);
        assert!(
            lines.iter().any(|l| l.contains("dominant error term: k2-p2+1 (op2 side)")),
            "{lines:?}"
        );
        assert!(lines.iter().any(|l| l.contains("k2-1") && l.contains("dR=-1bit")), "{lines:?}");
    }

    #[test]
    fn sens_saturation_and_undef() {
        // Err-dominated: no single step shrinks R; saturation hint appears.
        let lines = run_sens(&["add", "100,6,8,1", "50,5,8,2"]);
        assert!(lines.iter().any(|l| l.contains("saturated (err-dominated)")), "{lines:?}");
        // Undefined base: single message, no ranking.
        let lines = run_sens(&["div", "100,6,8,1", "50,5,4,4"]);
        assert_eq!(lines.len(), 1);
        assert!(lines[0].contains("base is undefined"), "{lines:?}");
        // Usage.
        assert_eq!(run_sens(&[]), vec![SENS_USAGE.to_string()]);
        assert!(run_sens(&["add", "1,2,3"]).iter().any(|l| l.contains("usage:")), "{lines:?}");
    }

    #[test]
    fn sens_lit_hint_and_verbose() {
        let lines = run_sens(&["add", "lit", "0.1", "lit", "0.2", "p", "8"]);
        assert!(
            lines.iter().any(|l| l.contains("lit: raise cap via `p <maxp>` / `n <n>`")),
            "{lines:?}"
        );
        let lines = run_sens(&["-v", "add", "10,3,4,1", "50,5,8,1"]);
        assert!(lines.iter().any(|l| l.starts_with("widths:")), "{lines:?}");
        assert!(lines.iter().any(|l| l.contains("raw (m=")), "{lines:?}");
    }

    #[test]
    fn tuple_parsing() {
        let x = parse_tuple("100,6,8,1").unwrap();
        assert_eq!((x.m, x.e, x.p, x.k), (100, 6, 8, 1));
        assert!(parse_tuple("1,2,0,3").is_none()); // p >= 1
        assert!(parse_tuple("1,2,3").is_none());
    }

    #[test]
    fn add_demo_matches() {
        let lines = run_mepk(&["add", "100,6,8,1", "50,5,8,2"]);
        assert!(lines.iter().any(|l| l.contains("62.5 ± 2 (tau=4)")), "{lines:?}");
        assert!(lines.iter().any(|l| l.starts_with("MATCH")), "{lines:?}");
        // Verbose adds widths, raw tuple, full digits, symbolic detail.
        let lines = run_mepk(&["-v", "add", "100,6,8,1", "50,5,8,2"]);
        assert!(lines.iter().any(|l| l.starts_with("widths:")), "{lines:?}");
        assert!(
            lines.iter().any(|l| l.contains("raw (m=250, e=5, p=8, k=4)")),
            "{lines:?}"
        );
        assert!(lines.iter().any(|l| l.starts_with("symbolic ")), "{lines:?}");
    }

    #[test]
    fn div_guard_demo_matches() {
        let lines = run_mepk(&["div", "100,6,8,1", "50,5,4,4"]);
        assert!(lines.iter().any(|l| l.contains("DivisionUndefined")), "{lines:?}");
        assert!(lines.iter().any(|l| l.starts_with("MATCH")), "{lines:?}");
    }

    #[test]
    fn widths_demo() {
        let lines = run_mepk(&["widths"]);
        assert_eq!(lines.len(), 1);
        assert!(lines[0].starts_with("n=4:"), "{lines:?}");
        let lines = run_mepk(&["widths", "n", "10"]);
        assert!(lines[0].starts_with("n=10: m=11"), "{lines:?}");
    }

    #[test]
    fn lit_in_operands() {
        // Padded lits keep full precision: 3.5 + 3.25 at max_p=4
        // ((14,1,4,0) and (13,1,4,0); total 27/4 rounds to (14,2,4)).
        let lines = run_mepk(&["add", "lit", "3.5", "lit", "3.25"]);
        assert!(
            lines.iter().any(|l| l.contains("lit 3.5 -> 3.5 ± 0.125 (tau=4)")),
            "{lines:?}"
        );
        assert!(
            lines.iter().any(|l| l.contains("lit 3.25 -> 3.25 ± 0.125 (tau=4)")),
            "{lines:?}"
        );
        assert!(lines.iter().any(|l| l.contains("7 ± 0.5 (tau=3)")), "{lines:?}");
        assert!(lines.iter().any(|l| l.starts_with("MATCH")), "{lines:?}");
        // Mixed tuple + lit (carry-tolerant MATCH), and option parsing.
        let lines = run_mepk(&["add", "100,6,8,1", "lit", "0.5"]);
        assert!(lines.iter().any(|l| l.starts_with("MATCH")), "{lines:?}");
        let lines = run_mepk(&["add", "lit", "0.1", "lit", "0.2", "p", "8"]);
        assert!(lines.iter().any(|l| l.contains("rounded")), "{lines:?}");
        // Errors.
        let lines = run_mepk(&["add", "lit", "abc", "lit", "1"]);
        assert!(lines.iter().any(|l| l.contains("cannot convert")), "{lines:?}");
        let lines = run_mepk(&["add", "lit", "1"]);
        assert!(lines.iter().any(|l| l.contains("usage:")), "{lines:?}");
        let lines = run_mepk(&["add", "lit", "1", "lit"]);
        assert!(lines.iter().any(|l| l.contains("usage:")), "{lines:?}");
    }

    #[test]
    fn lit_demo() {
        // n=4 → m=5 → default max_p=4; 0.5 pads to p=4 (exact).
        let lines = run_mepk(&["lit", "0.5"]);
        assert!(lines.iter().any(|l| l.contains("0.5 -> 0.5 ± 2^-5 (tau=4)")), "{lines:?}");
        assert!(lines.iter().any(|l| l.contains("exact, padded to 4 (minimal 1)")), "{lines:?}");
        // Non-dyadic rounds with k=1.
        let lines = run_mepk(&["lit", "0.1"]);
        assert!(lines.iter().any(|l| l.contains("0.1015625 ± 2^-7 (tau=3)")), "{lines:?}");
        assert!(lines.iter().any(|l| l.contains("rounded")), "{lines:?}");
        // Explicit cap.
        let lines = run_mepk(&["lit", "0.1", "p", "8"]);
        assert!(lines.iter().any(|l| l.contains("± 2^-11 (tau=7)")), "{lines:?}");
        let lines = run_mepk(&["lit", "2.5", "p", "8", "n", "10"]);
        assert!(lines.iter().any(|l| l.contains("2.5 -> 2.5 ± 2^-7 (tau=8)")), "{lines:?}");
        // Errors.
        let lines = run_mepk(&["lit", "abc"]);
        assert!(lines.iter().any(|l| l.contains("cannot convert")), "{lines:?}");
        let lines = run_mepk(&["lit"]);
        assert!(lines.iter().any(|l| l.contains("usage:")), "{lines:?}");
        let lines = run_mepk(&["lit", "0.5", "p", "0"]);
        assert!(lines.iter().any(|l| l.contains("1 <= p <= 127")), "{lines:?}");
    }
}
