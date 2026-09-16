//! Bounds simplifier: port of Java Alloy's `Simplifier` (Iter 14).
//!
//! Before translation, top-level `in` / `=` facts shrink relation upper
//! bounds (and grow lower bounds) so the CNF carries fewer primary
//! variables. Rules mirror `simplify_in` / `simplify_equal`:
//!
//! * `R in B` — replace `upper(R)` by `approx(B) ∩ upper(R)`; if the
//!   result no longer covers `lower(R)` the problem is UNSAT.
//! * `A = B` — run the `in` rule in both directions, plus lower-raising:
//!   when the other side's lower strictly extends ours within our upper,
//!   adopt it (and symmetrically shrink uppers).
//!
//! `approx` over-approximates an expression with the current uppers
//! (unions, products, `A - B ⊆ A`; joins/closures/variables/comprehensions
//! and everything else decline by returning `None`, which only skips).
//! Shrinking is iterated to a fixpoint (bounded rounds). This is purely
//! an optimization: it never changes the solution set.

use crate::ast::{
    AstArena, BinaryOp, ConstantExpr, ExprCompOp, ExprId, ExprNode, FormulaBinOp, FormulaId,
    FormulaNode,
};
use crate::bounds::{Bounds, BoundsError};
use crate::relation::RelationId;
use crate::tupleset::TupleSet;

/// Outcome of [`simplify_bounds`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SimplifyOutcome {
    /// Bounds unchanged (nothing applicable).
    Unchanged,
    /// At least one bound shrank (or grew, for lowers).
    Changed,
    /// A shrunk upper no longer covers its lower: UNSAT.
    Unsat,
}

/// Shrink `bounds` using the top-level conjuncts of `formula`.
///
/// Returns [`SimplifyOutcome::Unsat`] when shrinking proves
/// unsatisfiability (callers should replace the formula by false).
pub fn simplify_bounds(
    arena: &AstArena,
    bounds: &mut Bounds,
    formula: FormulaId,
) -> Result<SimplifyOutcome, BoundsError> {
    let mut conjuncts = Vec::new();
    flatten_ands(arena, formula, &mut conjuncts);
    let mut ever_changed = false;
    // Single pass suffices for Java (its loop returns after one round);
    // a short fixpoint is cheap and strictly stronger.
    for _ in 0..8 {
        let mut changed = false;
        for &c in &conjuncts {
            if let FormulaNode::Comparison { op, left, right } = arena.formula(c) {
                match op {
                    ExprCompOp::Subset => {
                        if simplify_in(arena, bounds, *left, *right)? {
                            return Ok(SimplifyOutcome::Unsat);
                        }
                        changed |= shrink_in(arena, bounds, *left, *right)?;
                    }
                    ExprCompOp::Equals => {
                        // Both directions, mirroring Java's eq-then-in order:
                        // simplify_equal first, then in-rules both ways.
                        changed |= simplify_equal(arena, bounds, *left, *right)?;
                        changed |= shrink_in(arena, bounds, *left, *right)?;
                        changed |= shrink_in(arena, bounds, *right, *left)?;
                    }
                }
            }
        }
        ever_changed |= changed;
        if !changed {
            break;
        }
    }
    Ok(if ever_changed {
        SimplifyOutcome::Changed
    } else {
        SimplifyOutcome::Unchanged
    })
}

fn flatten_ands(arena: &AstArena, f: FormulaId, out: &mut Vec<FormulaId>) {
    if let FormulaNode::Nary {
        op: FormulaBinOp::And,
        children,
    } = arena.formula(f)
    {
        let children = children.clone();
        for &c in &children {
            flatten_ands(arena, c, out);
        }
    } else {
        out.push(f);
    }
}

/// Java `simplify_in(a, b)` UNSAT check only: caller runs `shrink_in`
/// separately so eq-handling can interleave like the original.
fn simplify_in(
    arena: &AstArena,
    bounds: &Bounds,
    a: ExprId,
    b: ExprId,
) -> Result<bool, BoundsError> {
    let r = match arena.expr(a) {
        ExprNode::Relation(r) => *r,
        _ => return Ok(false),
    };
    let (lb, ub) = match bounds_pair(bounds, r) {
        Some(p) => p,
        None => return Ok(false),
    };
    let approx_b = match approx(arena, bounds, b) {
        Some(t) => t,
        None => return Ok(false),
    };
    let t = intersect(&approx_b, ub);
    // Shrunk below the lower bound: UNSAT.
    Ok(!t.covers(lb))
}

/// Java `simplify_in(a, b)` shrink step. Returns whether a bound changed.
/// UNSAT is reported by [`simplify_in`]; this only applies sound shrinks.
fn shrink_in(
    arena: &AstArena,
    bounds: &mut Bounds,
    a: ExprId,
    b: ExprId,
) -> Result<bool, BoundsError> {
    let r = match arena.expr(a) {
        ExprNode::Relation(r) => *r,
        _ => return Ok(false),
    };
    let (lb, ub) = match bounds_pair(bounds, r) {
        Some((lb, ub)) => (lb.clone(), ub.clone()),
        None => return Ok(false),
    };
    let approx_b = match approx(arena, bounds, b) {
        Some(t) => t,
        None => return Ok(false),
    };
    let t = intersect(&approx_b, &ub);
    if t.len() < ub.len() && t.covers(&lb) && ub.covers(&t) {
        bounds.bound(r, &lb, &t)?;
        return Ok(true);
    }
    Ok(false)
}

/// Java `simplify_equal(a, b)`: lower-raising when one side's lower
/// strictly extends the other's within the uppers, e.g. `A = B` with
/// `lower(B) ⊃ lower(A)` adopts `lower(B)` for `A`. Returns whether any
/// bound changed.
fn simplify_equal(
    arena: &AstArena,
    bounds: &mut Bounds,
    a: ExprId,
    b: ExprId,
) -> Result<bool, BoundsError> {
    let ra = match arena.expr(a) {
        ExprNode::Relation(r) => Some(*r),
        _ => None,
    };
    let rb = match arena.expr(b) {
        ExprNode::Relation(r) => Some(*r),
        _ => None,
    };
    if ra.is_none() && rb.is_none() {
        return Ok(false);
    }
    // Bound pairs, falling back to approx evaluation for compound sides
    // (Java `query()` handles union/product of relations the same way).
    let a0 = lower_of(arena, bounds, a);
    let a1 = approx(arena, bounds, a);
    let b0 = lower_of(arena, bounds, b);
    let b1 = approx(arena, bounds, b);
    let (a0, a1, b0, b1) = match (a0, a1, b0, b1) {
        (Some(a0), Some(a1), Some(b0), Some(b1)) => (a0, a1, b0, b1),
        _ => return Ok(false),
    };
    let mut changed = false;
    // Java order: a-lower, a-upper, b-lower, b-upper.
    if let Some(r) = ra {
        if b0.len() > a0.len() && b0.covers(&a0) && a1.covers(&b0) {
            bounds.bound(r, &b0, &a1)?;
            changed = true;
        }
        // Re-read: a1 may have changed above; use fresh pairs below.
        let (a0f, a1f) = match bounds_pair(bounds, r) {
            Some((l, u)) => (l.clone(), u.clone()),
            None => return Ok(changed),
        };
        if a1f.len() > b1.len() && b1.covers(&a0f) && a1f.covers(&b1) {
            bounds.bound(r, &a0f, &b1)?;
            changed = true;
        }
    }
    if let Some(r) = rb {
        if a0.len() > b0.len() && a0.covers(&b0) && b1.covers(&a0) {
            bounds.bound(r, &a0, &b1)?;
            changed = true;
        }
        let (b0f, b1f) = match bounds_pair(bounds, r) {
            Some((l, u)) => (l.clone(), u.clone()),
            None => return Ok(changed),
        };
        if b1f.len() > a1.len() && a1.covers(&b0f) && b1f.covers(&a1) {
            bounds.bound(r, &b0f, &a1)?;
            changed = true;
        }
    }
    Ok(changed)
}

/// Lower-bound evaluation mirroring `approx` (relations, unions,
/// products of lowers, atom sets; `None` to skip).
fn lower_of(arena: &AstArena, bounds: &Bounds, e: ExprId) -> Option<TupleSet> {
    match arena.expr(e).clone() {
        ExprNode::Relation(r) => bounds.lower_bound(r).cloned(),
        ExprNode::Atoms(atoms) => {
            let uni = bounds.universe();
            let mut ts = TupleSet::new(uni, 1).ok()?;
            for a in atoms {
                if (a as i64) < uni.size() as i64 {
                    ts.insert_index(a as i64);
                }
            }
            Some(ts)
        }
        ExprNode::Binary { op, left, right } => {
            let l = lower_of(arena, bounds, left)?;
            let r = lower_of(arena, bounds, right)?;
            match op {
                BinaryOp::Union => union_sets(&l, &r),
                BinaryOp::Product => l.product(&r).ok(),
                // A - B lower unknown: empty is always sound.
                BinaryOp::Difference => {
                    TupleSet::new(bounds.universe(), l.arity()).ok()
                }
                _ => None,
            }
        }
        ExprNode::Nary { op, children } => {
            if !matches!(op, BinaryOp::Union) {
                return None;
            }
            let mut acc: Option<TupleSet> = None;
            for &c in &children {
                let t = lower_of(arena, bounds, c)?;
                acc = Some(match acc {
                    Some(a) => union_sets(&a, &t)?,
                    None => t,
                });
            }
            acc
        }
        ExprNode::Constant(ConstantExpr::Empty) => TupleSet::new(bounds.universe(), 1).ok(),
        _ => None,
    }
}

/// Sound over-approximation of `e` under current uppers, or `None` to
/// skip (unknown constructs never shrink — always sound).
fn approx(arena: &AstArena, bounds: &Bounds, e: ExprId) -> Option<TupleSet> {
    match arena.expr(e).clone() {
        ExprNode::Relation(r) => bounds.upper_bound(r).cloned(),
        ExprNode::Constant(c) => {
            let uni = bounds.universe();
            let w = uni.size() as i64;
            match c {
                ConstantExpr::Univ => {
                    let mut ts = TupleSet::new(uni, 1).ok()?;
                    for i in 0..w {
                        ts.insert_index(i);
                    }
                    Some(ts)
                }
                ConstantExpr::Empty => TupleSet::new(uni, 1).ok(),
                ConstantExpr::Iden => {
                    let mut ts = TupleSet::new(uni, 2).ok()?;
                    for i in 0..w {
                        ts.insert_index(i * w + i);
                    }
                    Some(ts)
                }
                // Int sets: skip.
                ConstantExpr::Ints => None,
            }
        }
        ExprNode::Atoms(atoms) => {
            let uni = bounds.universe();
            let mut ts = TupleSet::new(uni, 1).ok()?;
            for a in atoms {
                if (a as i64) < uni.size() as i64 {
                    ts.insert_index(a as i64);
                }
            }
            Some(ts)
        }
        ExprNode::Binary { op, left, right } => {
            let l = approx(arena, bounds, left)?;
            let r = approx(arena, bounds, right)?;
            match op {
                BinaryOp::Union => union_sets(&l, &r),
                BinaryOp::Product => l.product(&r).ok(),
                // A - B ⊆ A: sound and often precise enough.
                BinaryOp::Difference => Some(l),
                // Joins/overrides need relational reasoning: skip.
                _ => None,
            }
        }
        ExprNode::Nary { op, children } => {
            if !matches!(op, BinaryOp::Union) {
                return None;
            }
            let mut acc: Option<TupleSet> = None;
            for &c in &children {
                let t = approx(arena, bounds, c)?;
                acc = Some(match acc {
                    Some(a) => union_sets(&a, &t)?,
                    None => t,
                });
            }
            acc
        }
        // Variables, unaries (transpose/closure need care), temporals,
        // if/comprehension/project/int: skip.
        _ => None,
    }
}

/// Bounds pair (lower, upper) of `r` when both exist.
fn bounds_pair(bounds: &Bounds, r: RelationId) -> Option<(&TupleSet, &TupleSet)> {
    bounds.bound_pair(r)
}

/// Union of two same-arity sets; `None` on arity mismatch.
fn union_sets(a: &TupleSet, b: &TupleSet) -> Option<TupleSet> {
    if a.arity() != b.arity() {
        return None;
    }
    let mut out = TupleSet::new(a.universe(), a.arity()).ok()?;
    for idx in a.index_view().iter().chain(b.index_view().iter()) {
        out.insert_index(idx);
    }
    Some(out)
}

/// Intersection of two same-arity sets; empty set on arity mismatch
/// (callers intersect approx results with existing uppers, so a
/// mismatch safely yields no shrink).
fn intersect(a: &TupleSet, b: &TupleSet) -> TupleSet {
    if a.arity() != b.arity() {
        return TupleSet::new(a.universe(), a.arity())
            .unwrap_or_else(|_| empty_fallback(a));
    }
    let mut out = TupleSet::new(a.universe(), a.arity()).unwrap_or_else(|_| empty_fallback(a));
    let (small, big) = if a.len() <= b.len() { (a, b) } else { (b, a) };
    for idx in small.index_view().iter() {
        if big.contains_index(idx) {
            out.insert_index(idx);
        }
    }
    out
}

fn empty_fallback(a: &TupleSet) -> TupleSet {
    // TupleSet::new only fails on capacity overflow; retry with arity 1
    // over the same universe (callers only use emptiness/size here).
    TupleSet::new(a.universe(), 1).expect("universe supports arity 1")
}
