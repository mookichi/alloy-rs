//! Expression-tree (CEGAR) evaluation over the `(m, e, p, k)` oracle
//! (`docs/mepk_formal_rev2.md` §9).
//!
//! [`MepkExpr`] is a small AST: `Leaf` holds an exact rational input plus
//! its initial precision `p`, `Bin` holds an operator and two children.
//! [`evaluate`] computes centres bottom-up with the concrete oracle only
//! ([`mepk_add`]/[`mepk_mul`]/[`mepk_div`]); [`true_value`] propagates the
//! exact rational truth independently (verification only — never read by
//! `evaluate`, see §9.3); [`verify`] checks `|truth − centre| ≤ R`.
//!
//! [`cegar_evaluate`] is the refinement loop: while some node reports
//! precision loss (`k ≥ p`, `τ = p − k − g ≤ 0`) or a division-precondition
//! violation, it refines either leaf precisions or the division guard:
//!
//! - the default step finds the traced node with the smallest `p − k`
//!   margin and raises `p` by `delta` on **all** leaves beneath it
//!   (§9.1(b): raising a single leaf cannot move the `p' = min(p1, p2)`
//!   bottleneck, so the old largest-`k` heuristic diverges on cancelling
//!   subtractions);
//! - when the worst node is a division whose margin is `Q`-blocked
//!   (`Q + 1 > max(D, B)` with `Q = q_lsb − 1`: the scaled pre-rounding
//!   error dominates), raising `p` cannot help — the centre accuracy is
//!   capped by the guard (`E1 ≤ 2^(q_lsb−1)` is `p`-independent since both
//!   `lsb`s shift together). The loop then raises the ambient `guard`
//!   instead (mirrors `MepkWidths::guard`, shared by all divisions).

use crate::int_ext;
use crate::mepk::{mepk_add, mepk_div, mepk_mul, Mepk};

/// First guard value used when the caller does not specify one.
pub const DEFAULT_GUARD: u32 = 4;
/// Hard cap for guard co-refinement (mirrors `MEPK_GUARD` range `0..=64`).
pub const MAX_GUARD: u32 = 64;

// ---------------------------------------------------------------------------
// Exact rationals (verification / leaf inputs only)
// ---------------------------------------------------------------------------

/// Exact rational `num / den` with `den > 0`. Checked `i128` arithmetic;
/// `None` on overflow (reported as [`CegarError::OracleRange`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Rat {
    pub num: i128,
    pub den: i128,
}

impl Rat {
    pub fn new(num: i128, den: i128) -> Option<Self> {
        if den <= 0 {
            return None;
        }
        Some(Rat { num, den })
    }

    fn add(self, o: Rat) -> Option<Rat> {
        Rat::new(
            self.num.checked_mul(o.den)?.checked_add(o.num.checked_mul(self.den)?)?,
            self.den.checked_mul(o.den)?,
        )
    }

    fn sub(self, o: Rat) -> Option<Rat> {
        Rat::new(
            self.num.checked_mul(o.den)?.checked_sub(o.num.checked_mul(self.den)?)?,
            self.den.checked_mul(o.den)?,
        )
    }

    fn mul(self, o: Rat) -> Option<Rat> {
        Rat::new(
            self.num.checked_mul(o.num)?,
            self.den.checked_mul(o.den)?,
        )
    }

    fn div(self, o: Rat) -> Option<Rat> {
        if o.num == 0 {
            return None;
        }
        let (n, d) = if o.num > 0 {
            (self.num.checked_mul(o.den)?, self.den.checked_mul(o.num)?)
        } else {
            (
                self.num.checked_mul(o.den)?.checked_neg()?,
                self.den.checked_mul(o.num.checked_neg()?)?,
            )
        };
        Rat::new(n, d)
    }
}

/// `floor(log2(num/den))` for `num > 0`, `den > 0`, via an exact bounded
/// scan around the bit-length difference (the true value is within ±1).
fn floor_log2_rat(num: u128, den: u128) -> Option<i32> {
    if den == 0 {
        return None;
    }
    let base = int_ext::bit_len(num) as i32 - int_ext::bit_len(den) as i32;
    // `2^e ≤ num/den` ⟺ `den·2^e ≤ num` (e ≥ 0) or `den ≤ num·2^-e`
    // (e < 0); overflows decide the order (product past `u128::MAX`
    // exceeds the other side).
    let le = |e: i32| -> bool {
        if e >= 0 {
            match den.checked_mul(1u128.checked_shl(e as u32).unwrap_or(u128::MAX)) {
                Some(v) => v <= num,
                None => false,
            }
        } else {
            match num.checked_shl((-e) as u32) {
                Some(v) => v >= den,
                None => true,
            }
        }
    };
    let mut want = base - 2;
    for e in (base - 2)..=(base + 2) {
        if le(e) {
            want = e;
        } else {
            break;
        }
    }
    Some(want)
}

/// Round the exact input `num/den` (`den > 0`) to a `p`-bit normalized
/// mantissa with `k = 0` (Lemma 1 itself: `R = 2^(e−p)` covers the
/// rounding error). This is ordinary input representation, not an oracle
/// peek: only the leaf's own input value is used.
fn leaf_round(num: i128, den: i128, p: u32) -> Option<Mepk> {
    if p == 0 || p > 127 || den <= 0 {
        return None;
    }
    if num == 0 {
        let (m, e) = int_ext::round_to_precision_raw(0, 0, p)?;
        return Mepk::new(m, e, p, 0);
    }
    let neg = num < 0;
    let mag = num.unsigned_abs();
    let e_est = floor_log2_rat(mag, den as u128)?;
    // `m0 = round(mag·2^(p−1−e) / den)` for the candidate `e = e_est`;
    // renormalize when the rounded magnitude leaves `[2^(p−1), 2^p]`.
    let mut e = e_est;
    let shift = (p as i32 - 1 - e).checked_neg()?;
    // Scale numerator/denominator so the quotient is `mag·2^(p−1−e)/den`.
    let (n_scaled, d_scaled) = if shift <= 0 {
        (mag.checked_mul(2u128.checked_pow((-shift) as u32)?)?, den as u128)
    } else {
        (mag, (den as u128).checked_mul(2u128.checked_pow(shift as u32)?)?)
    };
    let q0 = n_scaled.checked_div(d_scaled)?;
    let rem = n_scaled.checked_rem(d_scaled)?;
    let mut m0 = int_ext::round_half_even_step(q0, rem, d_scaled)?;
    let two_p = 1u128.checked_shl(p)?;
    let half_p = 1u128.checked_shl(p - 1)?;
    if m0 >= two_p {
        // Carry-out (at most one bit past): renormalize to `2^(p−1)`.
        m0 = half_p;
        e = e.checked_add(1)?;
    }
    if m0 < half_p {
        // `V` sat just below `2^e_est`: step the exponent down once.
        // (Reachable only when `e_est` overshoots by one; the loop-free
        // single step suffices because `V ∈ [2^e_est, 2^(e_est+1))`.)
        e = e.checked_sub(1)?;
        let shift2 = (p as i32 - 1 - e).checked_neg()?;
        let (n2, d2) = if shift2 <= 0 {
            (
                mag.checked_mul(2u128.checked_pow((-shift2) as u32)?)?,
                den as u128,
            )
        } else {
            (
                mag,
                (den as u128).checked_mul(2u128.checked_pow(shift2 as u32)?)?,
            )
        };
        let q2 = n2.checked_div(d2)?;
        let r2 = n2.checked_rem(d2)?;
        m0 = int_ext::round_half_even_step(q2, r2, d2)?;
        if m0 < half_p || m0 > two_p {
            return None;
        }
        if m0 == two_p {
            m0 = half_p;
            e = e.checked_add(1)?;
        }
    }
    if m0 > i128::MAX as u128 {
        return None;
    }
    let m = if neg { -(m0 as i128) } else { m0 as i128 };
    let lsb = e.checked_sub(p as i32)?.checked_add(1)?;
    // Reuse the oracle rounding path shape: centre `(m, e')` with
    // `e' = lsb + p − 1 = e`. (Direct construction; identical result.)
    let _ = lsb;
    Mepk::new(m, e, p, 0)
}

// ---------------------------------------------------------------------------
// Expression trees
// ---------------------------------------------------------------------------

/// Binary `(m, e, p, k)` operators.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MepkOp {
    Add,
    Sub,
    Mul,
    Div,
}

/// Expression tree: exact-rational leaves plus operator nodes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MepkExpr {
    Leaf { num: i128, den: i128, p: u32 },
    Bin {
        op: MepkOp,
        left: Box<MepkExpr>,
        right: Box<MepkExpr>,
    },
}

impl MepkExpr {
    pub fn leaf(num: i128, den: i128, p: u32) -> Self {
        MepkExpr::Leaf { num, den, p }
    }

    pub fn bin(op: MepkOp, left: MepkExpr, right: MepkExpr) -> Self {
        MepkExpr::Bin {
            op,
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    /// Add `delta` to every leaf precision in this subtree (saturates at
    /// 127; returns `false` when some leaf cannot grow — CEGAR gives up).
    fn bump_leaves(&mut self, delta: u32) -> bool {
        match self {
            MepkExpr::Leaf { p, .. } => {
                let np = (*p).saturating_add(delta).min(127);
                if np <= *p {
                    return false;
                }
                *p = np;
                true
            }
            MepkExpr::Bin { left, right, .. } => {
                left.bump_leaves(delta) && right.bump_leaves(delta)
            }
        }
    }
}

/// Per-node trace of one [`evaluate`] pass.
#[derive(Clone, Debug)]
pub struct TracedNode {
    /// Operator that produced this node (`None` for leaves).
    pub op: Option<MepkOp>,
    pub v: Mepk,
}

/// Why [`evaluate_traced`] stopped.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EvalError {
    /// Denominator out of domain (`k2 ≥ p2` or `m2 == 0`): CEGAR refines.
    DivUndefined,
    /// `i128` oracle range exceeded (or bad precision): CEGAR bails.
    OracleRange,
}

fn eval_leaf(num: i128, den: i128, p: u32) -> Result<TracedNode, EvalError> {
    if den <= 0 {
        return Err(EvalError::OracleRange);
    }
    let v = leaf_round(num, den, p).ok_or(EvalError::OracleRange)?;
    Ok(TracedNode { op: None, v })
}

/// Bottom-up centre evaluation with the concrete oracle only.
/// `DivUndefined` on `k2 ≥ p2` / `m2 == 0` (refineable);
/// `OracleRange` on `i128` overflow (fatal). `guard` is the ambient
/// scaled-division guard (mirrors `MepkWidths::guard`).
pub fn evaluate_traced(e: &MepkExpr, guard: u32) -> Result<TracedNode, EvalError> {
    match e {
        MepkExpr::Leaf { num, den, p } => eval_leaf(*num, *den, *p),
        MepkExpr::Bin { op, left, right } => {
            let l = evaluate_traced(left, guard)?;
            let r = evaluate_traced(right, guard)?;
            let v = match op {
                MepkOp::Add => mepk_add(&l.v, &r.v, 1).ok_or(EvalError::OracleRange)?,
                MepkOp::Sub => mepk_add(&l.v, &r.v, -1).ok_or(EvalError::OracleRange)?,
                MepkOp::Mul => mepk_mul(&l.v, &r.v).ok_or(EvalError::OracleRange)?,
                MepkOp::Div => {
                    if !r.v.div_guard() || r.v.m == 0 {
                        return Err(EvalError::DivUndefined);
                    }
                    mepk_div(&l.v, &r.v, guard).ok_or(EvalError::OracleRange)?
                }
            };
            Ok(TracedNode { op: Some(*op), v })
        }
    }
}

/// Centre-only evaluation (drops the trace wrapper).
pub fn evaluate(e: &MepkExpr, guard: u32) -> Result<Mepk, EvalError> {
    evaluate_traced(e, guard).map(|t| t.v)
}

/// Exact rational truth propagation (verification only; never read by
/// [`evaluate_traced`]). `None` on overflow or division by an exact zero.
pub fn true_value(e: &MepkExpr) -> Option<Rat> {
    match e {
        MepkExpr::Leaf { num, den, .. } => Rat::new(*num, *den),
        MepkExpr::Bin { op, left, right } => {
            let (l, r) = (true_value(left)?, true_value(right)?);
            match op {
                MepkOp::Add => l.add(r),
                MepkOp::Sub => l.sub(r),
                MepkOp::Mul => l.mul(r),
                MepkOp::Div => l.div(r),
            }
        }
    }
}

/// Check `|truth − centre| ≤ R` in exact scaled-integer arithmetic:
/// `|t.num/t.den − m·2^lsb| ≤ 2^rexp` cross-multiplied by `t.den > 0`
/// and scaled into `2^lo` units (`lo = min(lsb, rexp, 0)` keeps every
/// shift non-negative). `None` on overflow (test values are small).
pub fn verify(v: &Mepk, t: Rat) -> Option<bool> {
    let lsb = v.e - v.p as i32 + 1;
    let rexp = v.e - v.p as i32 + v.k;
    let lo = 0.min(lsb).min(rexp);
    // `|t.num − m·2^lsb·t.den| ≤ 2^rexp·t.den`, both sides scaled by
    // `2^-lo`: `|t.num·2^-lo − m·t.den·2^(lsb−lo)| ≤ 2^(rexp−lo)·t.den`.
    let tn = t.num.checked_mul(1i128.checked_shl((-lo) as u32)?)?;
    let cm = v
        .m
        .checked_mul(t.den)?
        .checked_mul(1i128.checked_shl((lsb - lo) as u32)?)?;
    let lhs = tn.checked_sub(cm)?.abs();
    let rhs = t
        .den
        .checked_mul(1i128.checked_shl((rexp - lo) as u32)?)?;
    Some(lhs <= rhs)
}

// ---------------------------------------------------------------------------
// CEGAR loop
// ---------------------------------------------------------------------------

/// Evaluate every subtree, returning traced `(is_bin, value)` nodes in
/// left-post-order plus the overall status. Unlike [`evaluate_traced`],
/// nodes successfully evaluated before a mid-tree `DivUndefined` are
/// kept, so refinement can still pick the worst evaluated margin
/// (§9.1(b)) instead of blindly bumping everything.
fn trace_all(e: &MepkExpr, guard: u32) -> (Vec<(bool, Mepk)>, Result<Mepk, EvalError>) {
    // `(is_bin, value)` per node, root last.
    let mut out = Vec::new();
    fn go(
        e: &MepkExpr,
        guard: u32,
        out: &mut Vec<(bool, Mepk)>,
    ) -> Result<Mepk, EvalError> {
        match e {
            MepkExpr::Leaf { num, den, p } => {
                let v = eval_leaf(*num, *den, *p)?.v;
                out.push((false, v));
                Ok(v)
            }
            MepkExpr::Bin { op, left, right } => {
                let l = go(left, guard, out)?;
                let r = go(right, guard, out)?;
                let v = match op {
                    MepkOp::Add => mepk_add(&l, &r, 1).ok_or(EvalError::OracleRange)?,
                    MepkOp::Sub => mepk_add(&l, &r, -1).ok_or(EvalError::OracleRange)?,
                    MepkOp::Mul => mepk_mul(&l, &r).ok_or(EvalError::OracleRange)?,
                    MepkOp::Div => {
                        if !r.div_guard() || r.m == 0 {
                            return Err(EvalError::DivUndefined);
                        }
                        mepk_div(&l, &r, guard).ok_or(EvalError::OracleRange)?
                    }
                };
                out.push((true, v));
                Ok(v)
            }
        }
    }
    // On `DivUndefined` the failing node's children are already traced
    // (pushed before the check), so margins stay available.
    let status = go(e, guard, &mut out);
    (out, status)
}

/// A descent step from a [`Bin`] node to a child.
#[derive(Clone, Copy)]
enum Step {
    L,
    R,
}

/// Shape-matched path to the `target`-th [`Bin`] node in left-post-order
/// (same order as [`trace_all`]): left-subtree bins, right-subtree bins,
/// then self. The path is built bottom-up (reverse before following).
fn find_bin_path(e: &MepkExpr, target: usize, counter: &mut usize, path: &mut Vec<Step>) -> bool {
    match e {
        MepkExpr::Leaf { .. } => false,
        MepkExpr::Bin { left, right, .. } => {
            if find_bin_path(left, target, counter, path) {
                path.push(Step::L);
                return true;
            }
            if find_bin_path(right, target, counter, path) {
                path.push(Step::R);
                return true;
            }
            if *counter == target {
                return true;
            }
            *counter += 1;
            false
        }
    }
}

/// Follow a [`find_bin_path`] path immutably (top-down).
fn follow<'a>(e: &'a MepkExpr, path: &[Step]) -> &'a MepkExpr {
    let mut cur = e;
    for s in path.iter().rev() {
        cur = match (cur, s) {
            (MepkExpr::Bin { left, .. }, Step::L) => left,
            (MepkExpr::Bin { right, .. }, Step::R) => right,
            _ => unreachable!("bin path out of sync with tree shape"),
        };
    }
    cur
}

/// Follow a [`find_bin_path`] path mutably (top-down).
fn follow_mut<'a>(e: &'a mut MepkExpr, path: &[Step]) -> &'a mut MepkExpr {
    let mut cur = e;
    for s in path.iter().rev() {
        cur = match (cur, s) {
            (MepkExpr::Bin { left, .. }, Step::L) => left,
            (MepkExpr::Bin { right, .. }, Step::R) => right,
            _ => unreachable!("bin path out of sync with tree shape"),
        };
    }
    cur
}

/// Outcome of [`cegar_evaluate`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CegarOutcome {
    pub root: Mepk,
    pub iters: u32,
    /// Ambient guard at success (raised above `guard0` iff some division
    /// was `Q`-blocked during refinement).
    pub guard: u32,
}

/// Why [`cegar_evaluate`] gave up.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CegarError {
    /// A denominator left the domain and its leaves cannot grow further
    /// (or the tree is a bare leaf).
    UnrefineableDiv,
    /// Precision loss persists but leaves cannot grow further.
    UnrefineablePrecision,
    /// `i128` oracle range exceeded (precision cannot help).
    OracleRange,
    /// `max_iters` exhausted.
    MaxIters,
    /// A `Q`-blocked division needs more guard than [`MAX_GUARD`].
    GuardExhausted,
}

/// CEGAR evaluation with goal `g` (target guarantee bits), starting guard
/// `guard0`, and optional absolute tolerance `abs_tol` (a radius-exponent
/// bound: keep refining while some node has `R = 2^r` with `r > abs_tol`;
/// `None` disables it): while some node reports precision loss
/// (`k ≥ p` or `τ = p − k − g ≤ 0`), absolute looseness, or a
/// division-precondition violation, refine and re-evaluate. Each
/// refinement either raises `p` by `delta` on **all** leaves beneath the
/// smallest-`p − k`-margin node (§9.1(b)), or — when that node is a
/// `Q`-blocked division (`Q + 1 > max(D, B)`, i.e. the scaled pre-rounding
/// error dominates and raising `p` cannot help) — raises the ambient
/// `guard` by `delta` instead.
///
/// Absolute tolerance covers the `m = 0` blind spot of the `τ` criterion:
/// a zero centre has no relative error, so `τ > 0` can coexist with an
/// enormous absolute `R` (e.g. exact cancellation at a large scale, or a
/// zero-path quotient). Unreachable tolerances stop honestly at the caps
/// (`p ≤ 127`, `guard ≤ 64`, `max_iters`).
///
/// Mutates leaf precisions in place; returns the final root on success
/// (success implies both loss-free and, when given, abs-met nodes).
pub fn cegar_evaluate(
    expr: &mut MepkExpr,
    g: i32,
    delta: u32,
    max_iters: u32,
    guard0: u32,
    abs_tol: Option<i32>,
) -> Result<CegarOutcome, CegarError> {
    if delta == 0 {
        return Err(CegarError::UnrefineablePrecision);
    }
    let mut guard = guard0.min(MAX_GUARD);
    for it in 0..=max_iters {
        let (nodes, status) = trace_all(expr, guard);
        match status {
            Err(EvalError::DivUndefined) => {
                if it >= max_iters {
                    return Err(CegarError::MaxIters);
                }
                // Guard cannot fix domain violations: leaf-bump only.
                if !refine_leaves(expr, &nodes, delta) {
                    return Err(CegarError::UnrefineableDiv);
                }
            }
            Err(EvalError::OracleRange) => return Err(CegarError::OracleRange),
            Ok(root) => {
                // Precision loss anywhere? (`k ≥ p` or `τ ≤ 0`.)
                let lost = nodes.iter().any(|(is_bin, v)| {
                    *is_bin && (v.k >= v.p as i32 || v.p as i32 - v.k - g <= 0)
                });
                // Absolute looseness anywhere (all nodes incl. leaves)?
                let loose = match abs_tol {
                    Some(a) => nodes
                        .iter()
                        .any(|(_, v)| v.e - v.p as i32 + v.k > a),
                    None => false,
                };
                if !lost && !loose {
                    return Ok(CegarOutcome { root, iters: it, guard });
                }
                if it >= max_iters {
                    return Err(CegarError::MaxIters);
                }
                match pick_refine(expr, &nodes, guard) {
                    Pick::Guard => {
                        if guard >= MAX_GUARD {
                            return Err(CegarError::GuardExhausted);
                        }
                        guard = guard.saturating_add(delta).min(MAX_GUARD);
                    }
                    Pick::Leaves => {
                        if !refine_leaves(expr, &nodes, delta) {
                            return Err(CegarError::UnrefineablePrecision);
                        }
                    }
                }
            }
        }
    }
    Err(CegarError::MaxIters)
}

/// Refinement direction chosen by [`pick_refine`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Pick {
    Leaves,
    Guard,
}

/// Choose the refinement direction: `Guard` iff the worst-margin node is
/// a division whose `Q` dominates (`Q + 1 > max(D, B)`); `Leaves`
/// otherwise.
fn pick_refine(expr: &MepkExpr, nodes: &[(bool, Mepk)], guard: u32) -> Pick {
    let mut worst: Option<(usize, i32)> = None;
    let mut bin_idx = 0usize;
    for (is_bin, v) in nodes {
        if *is_bin {
            let margin = v.p as i32 - v.k;
            match worst {
                None => worst = Some((bin_idx, margin)),
                Some((_, m)) if margin < m => worst = Some((bin_idx, margin)),
                _ => {}
            }
            bin_idx += 1;
        }
    }
    let (target, _) = match worst {
        Some(w) => w,
        None => return Pick::Leaves,
    };
    let mut counter = 0usize;
    let mut path = Vec::new();
    if !find_bin_path(expr, target, &mut counter, &mut path) {
        return Pick::Leaves;
    }
    let sub = follow(expr, &path);
    let (op, l, r) = match sub {
        MepkExpr::Bin { op, left, right } => (op, left, right),
        MepkExpr::Leaf { .. } => return Pick::Leaves,
    };
    if *op != MepkOp::Div {
        return Pick::Leaves;
    }
    // Recompute the division's exponents from its (already evaluated)
    // children and its own traced value.
    let (lv, rv, vv) = match (
        evaluate_traced(l, guard),
        evaluate_traced(r, guard),
        evaluate_traced(sub, guard),
    ) {
        (Ok(l), Ok(r), Ok(v)) => (l.v, r.v, v.v),
        _ => return Pick::Leaves,
    };
    let d = int_ext::div_d(lv.e, rv.e, lv.k, lv.p as i32, rv.k, rv.p as i32);
    let q = lv
        .lsb()
        .checked_sub(rv.lsb())
        .and_then(|v| v.checked_sub(guard as i32));
    let b = vv.e - vv.p as i32;
    match q {
        Some(qv) if qv + 1 > d.max(b) => Pick::Guard,
        _ => Pick::Leaves,
    }
}

/// Find the [`Bin`] node with the smallest `p − k` margin in the given
/// trace and bump all leaves beneath it by `delta`. Returns `false` when
/// nothing can grow (bare leaf, or every leaf saturated at 127).
fn refine_leaves(expr: &mut MepkExpr, nodes: &[(bool, Mepk)], delta: u32) -> bool {
    // Bin nodes in trace order with margins; pick the minimum `p − k`.
    let mut worst: Option<(usize, i32)> = None;
    let mut bin_idx = 0usize;
    for (is_bin, v) in nodes {
        if *is_bin {
            let margin = v.p as i32 - v.k;
            match worst {
                None => worst = Some((bin_idx, margin)),
                Some((_, m)) if margin < m => worst = Some((bin_idx, margin)),
                _ => {}
            }
            bin_idx += 1;
        }
    }
    let (target, _) = match worst {
        Some(w) => w,
        None => return false, // bare leaf: nothing to refine beneath.
    };
    let mut counter = 0usize;
    let mut path = Vec::new();
    if !find_bin_path(expr, target, &mut counter, &mut path) {
        return false;
    }
    follow_mut(expr, &path).bump_leaves(delta)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn leaf_i(n: i128, p: u32) -> MepkExpr {
        MepkExpr::leaf(n, 1, p)
    }

    #[test]
    fn leaf_rounding_and_verify() {
        // 1/3 at p = 8: centre within R, k = 0 (Lemma 1 itself).
        let e = MepkExpr::leaf(1, 3, 8);
        let v = evaluate(&e, DEFAULT_GUARD).unwrap();
        assert_eq!(v.k, 0);
        assert_eq!(verify(&v, Rat::new(1, 3).unwrap()), Some(true));
        // Exact dyadic leaf: zero error.
        let e = MepkExpr::leaf(3, 2, 8);
        let v = evaluate(&e, DEFAULT_GUARD).unwrap();
        assert_eq!(verify(&v, Rat::new(3, 2).unwrap()), Some(true));
        // Zero leaf.
        let e = MepkExpr::leaf(0, 5, 8);
        let v = evaluate(&e, DEFAULT_GUARD).unwrap();
        assert_eq!(verify(&v, Rat::new(0, 5).unwrap()), Some(true));
        // Negative leaf.
        let e = MepkExpr::leaf(-7, 2, 8);
        let v = evaluate(&e, DEFAULT_GUARD).unwrap();
        assert_eq!(verify(&v, Rat::new(-7, 2).unwrap()), Some(true));
    }

    #[test]
    fn basic_ops_verify() {
        // (1/2 + 1/3) * 6/1 = 5 (truth kept unreduced: 30/6).
        let e = MepkExpr::bin(
            MepkOp::Mul,
            MepkExpr::bin(
                MepkOp::Add,
                MepkExpr::leaf(1, 2, 8),
                MepkExpr::leaf(1, 3, 8),
            ),
            leaf_i(6, 8),
        );
        let v = evaluate(&e, DEFAULT_GUARD).unwrap();
        let t = true_value(&e).unwrap();
        assert_eq!((t.num, t.den), (30, 6));
        assert_eq!(verify(&v, t), Some(true));
    }

    /// rev2 §9.2 walkthrough shape: `(355·113 − 22·7) / (e−f)` with a
    /// cancelling denominator (`e ≈ f`), all leaves at `p = 8`. Must
    /// converge (no §9.1(b) infinite loop: the `p' = min` bottleneck is
    /// refined on both sides), end loss-free at the goal, and verify.
    #[test]
    fn cegar_cancelling_walkthrough_converges() {
        let mut e = MepkExpr::bin(
            MepkOp::Div,
            MepkExpr::bin(
                MepkOp::Sub,
                MepkExpr::bin(MepkOp::Mul, leaf_i(355, 8), leaf_i(113, 8)),
                MepkExpr::bin(MepkOp::Mul, leaf_i(22, 8), leaf_i(7, 8)),
            ),
            MepkExpr::bin(MepkOp::Sub, leaf_i(1000, 8), leaf_i(999, 8)),
        );
        let g = 3;
        let out = cegar_evaluate(&mut e, g, 6, 10, DEFAULT_GUARD, None).expect("must converge");
        assert!(out.iters >= 1, "expected at least one refinement, got {out:?}");
        // The root division is Q-blocked (pre-rounding dominates), so
        // convergence must have raised the guard, not just leaf `p`s.
        assert!(
            out.guard > DEFAULT_GUARD,
            "expected guard co-refinement, got {out:?}"
        );
        // Loss-free everywhere at the goal.
        let (nodes, status) = trace_all(&e, out.guard);
        assert!(status.is_ok());
        for (is_bin, v) in &nodes {
            if *is_bin {
                assert!(v.k < v.p as i32, "k>=p persists: {v:?}");
                assert!(v.p as i32 - v.k - g > 0, "tau<=0 persists: {v:?}");
            }
        }
        // Root verifies against the exact truth 39961/1.
        let t = true_value(&e).unwrap();
        assert_eq!((t.num, t.den), (39961, 1));
        assert_eq!(verify(&out.root, t), Some(true));
    }

    #[test]
    fn div_undefined_is_reported_not_hung() {
        // x / (y − y): exact-cancellation denominator.
        let e = MepkExpr::bin(
            MepkOp::Div,
            leaf_i(3, 8),
            MepkExpr::bin(MepkOp::Sub, leaf_i(5, 8), leaf_i(5, 8)),
        );
        assert_eq!(
            evaluate_traced(&e, DEFAULT_GUARD).map(|t| t.v),
            Err(EvalError::DivUndefined)
        );
        // CEGAR cannot fix a structurally-zero denominator: it must give
        // up (any error), never succeed and never hang.
        let mut e2 = e.clone();
        assert!(cegar_evaluate(&mut e2, 3, 6, 4, DEFAULT_GUARD, None).is_err());
    }

    #[test]
    fn already_precise_needs_no_refinement() {
        let mut e = MepkExpr::bin(MepkOp::Add, leaf_i(1, 8), leaf_i(2, 8));
        let out = cegar_evaluate(&mut e, 0, 6, 10, DEFAULT_GUARD, None).unwrap();
        assert_eq!(out.iters, 0);
    }

    /// `τ`-blind vacuity without division: `(x−x)` at `x ~ 2^100` gives
    /// `0 ± 2^94` with `τ > 0`, so plain CEGAR stops immediately —
    /// documenting the `m = 0` blind spot.
    #[test]
    fn sub_zero_vacuity_stops_without_abs() {
        let big = 1i128 << 100;
        let mut e = MepkExpr::bin(
            MepkOp::Sub,
            MepkExpr::leaf(big, 1, 8),
            MepkExpr::leaf(big, 1, 8),
        );
        let out = cegar_evaluate(&mut e, 3, 6, 10, DEFAULT_GUARD, None).unwrap();
        assert_eq!(out.iters, 0);
        assert_eq!(out.root.m, 0);
        let r_exp = out.root.e - out.root.p as i32 + out.root.k;
        assert!(r_exp > 64, "expected vacuous radius, got R=2^{r_exp}");
        assert_eq!(verify(&out.root, Rat::new(0, 1).unwrap()), Some(true));
    }

    /// The same shape converges under an absolute tolerance (`R ≤ 2^0`):
    /// `R` shrinks with `p` here (unlike `Q`-blocked divisions).
    #[test]
    fn sub_zero_vacuity_fixed_by_abs() {
        let big = 1i128 << 100;
        let mut e = MepkExpr::bin(
            MepkOp::Sub,
            MepkExpr::leaf(big, 1, 8),
            MepkExpr::leaf(big, 1, 8),
        );
        let out = cegar_evaluate(&mut e, 3, 6, 40, DEFAULT_GUARD, Some(0)).unwrap();
        assert!(out.iters > 0);
        let r_exp = out.root.e - out.root.p as i32 + out.root.k;
        assert!(r_exp <= 0, "R still loose: 2^{r_exp}");
        assert_eq!(verify(&out.root, Rat::new(0, 1).unwrap()), Some(true));
    }

    /// Unreachable absolute tolerance stops honestly at the `p` cap
    /// (not by hanging): `R ≤ 2^-200` needs `p ≥ 302 > 127`.
    #[test]
    fn abs_unreachable_stops_honestly() {
        let big = 1i128 << 100;
        let mut e = MepkExpr::bin(
            MepkOp::Sub,
            MepkExpr::leaf(big, 1, 8),
            MepkExpr::leaf(big, 1, 8),
        );
        assert_eq!(
            cegar_evaluate(&mut e, 3, 6, 40, DEFAULT_GUARD, Some(-200)),
            Err(CegarError::UnrefineablePrecision)
        );
    }
}
