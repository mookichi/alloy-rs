//! Skolemization (backlog item 2).
//!
//! Replaces positive existential quantifiers with fresh witness relations:
//!
//!   some x: D | F[x]      becomes      $sk ⊆ D  ∧  F[$sk]
//!   all u: U, some x: D | F[u,x]
//!                         becomes
//!   all u: U | $sk(u) ⊆ D  ∧  F[u, $sk(u)]
//!
//! The witness relation's arity grows by the total arity of the enclosing
//! universal variables (Skolem *functions*). Bounds for `$sk` are derived
//! from a conservative upper bound of the domain expression `D` computed
//! over the given bounds (see [`upper_bound_expr`]); when `D`'s upper bound
//! cannot be approximated the quantifier is left untouched.
//!
//! Temporal (HASLab-style) witnesses live in [`crate::temporal`]: inside a
//! temporal context the witness relation additionally carries a TIME column
//! and its constraint is quantified over all trace states. Nested
//! existentials are not skolemized (only outermost ones), which preserves
//! correctness at the cost of some optimization.

use std::collections::{HashMap, HashSet};

use crate::ast::{
    AstArena, BinaryOp, ConstantExpr, Decl, ExprCompOp, ExprId, FormulaBinOp, FormulaId, IntId,
    Multiplicity, Quantifier, VarId,
};
use crate::bounds::Bounds;
use crate::eval::{closure, cross, difference, intersection, join as ts_join, transpose, union};
use crate::relation::RelationId;
use crate::tupleset::TupleSet;

#[derive(Debug, thiserror::Error)]
pub enum SkolemError {
    #[error("ast error: {0}")]
    Ast(#[from] crate::ast::AstError),
    #[error("bounds error: {0}")]
    Bounds(#[from] crate::bounds::BoundsError),
    #[error("tuple set error: {0}")]
    Capacity(#[from] crate::tupleset::CapacityError),
    #[error("evaluation error: {0}")]
    Eval(#[from] crate::eval::EvalError),
}

/// Conservative upper bound of an expression over `bounds`.
///
/// Returns `None` for constructs whose upper bound we do not approximate
/// (comprehensions, if-expressions, projections, free variables, temporal
/// nodes). Monotone operators yield valid supersets.
pub fn upper_bound_expr(arena: &AstArena, e: ExprId, bounds: &Bounds) -> Option<TupleSet> {
    match arena.expr(e).clone() {
        crate::ast::ExprNode::Relation(r) => bounds.upper_bound(r).cloned(),
        crate::ast::ExprNode::Constant(c) => {
            let uni = bounds.universe();
            match c {
                ConstantExpr::Univ => {
                    let mut ts = TupleSet::new(uni, 1).ok()?;
                    for i in 0..uni.size() as i64 {
                        ts.insert_index(i);
                    }
                    Some(ts)
                }
                ConstantExpr::Empty => TupleSet::new(uni, 1).ok(),
                ConstantExpr::Iden => {
                    let mut ts = TupleSet::new(uni, 2).ok()?;
                    let sz = uni.size() as i64;
                    for i in 0..sz {
                        ts.insert_index(i * sz + i);
                    }
                    Some(ts)
                }
                ConstantExpr::Ints => None,
            }
        }
        crate::ast::ExprNode::Variable(_) | crate::ast::ExprNode::Temporal { .. } => None,
        crate::ast::ExprNode::Unary { op, child } => {
            let m = upper_bound_expr(arena, child, bounds)?;
            match op {
                crate::ast::UnaryExprOp::Transpose => transpose(&m).ok(),
                crate::ast::UnaryExprOp::Closure => closure(&m, false).ok(),
                crate::ast::UnaryExprOp::ReflexiveClosure => closure(&m, true).ok(),
            }
        }
        crate::ast::ExprNode::Binary { op, left, right } => {
            let a = upper_bound_expr(arena, left, bounds)?;
            let b = upper_bound_expr(arena, right, bounds)?;
            match op {
                BinaryOp::Union => union(&a, &b).ok(),
                BinaryOp::Intersection => intersection(&a, &b).ok(),
                // removing upper(right) from upper(left) is still an upper bound
                BinaryOp::Difference => difference(&a, &b).ok().or(Some(a)),
                BinaryOp::Override => union(&b, &a).ok(),
                BinaryOp::Product => cross(&a, &b).ok(),
                BinaryOp::Join => ts_join(&a, &b).ok(),
            }
        }
        crate::ast::ExprNode::Nary { op, children } => {
            let mut acc = upper_bound_expr(arena, children[0], bounds)?;
            for &c in &children[1..] {
                let m = upper_bound_expr(arena, c, bounds)?;
                acc = match op {
                    BinaryOp::Union => union(&acc, &m).ok()?,
                    BinaryOp::Intersection => intersection(&acc, &m).ok()?,
                    BinaryOp::Difference => difference(&acc, &m).unwrap_or(acc),
                    BinaryOp::Override => union(&m, &acc).ok()?,
                    BinaryOp::Product => cross(&acc, &m).ok()?,
                    BinaryOp::Join => ts_join(&acc, &m).ok()?,
                };
            }
            Some(acc)
        }
        crate::ast::ExprNode::If { then, els, .. } => {
            let t = upper_bound_expr(arena, then, bounds)?;
            let e = upper_bound_expr(arena, els, bounds)?;
            union(&t, &e).ok()
        }
        crate::ast::ExprNode::Comprehension { .. } | crate::ast::ExprNode::Project { .. } => None,
        crate::ast::ExprNode::FromInt(_) => None,
    }
}

struct StaticSkolemizer<'a> {
    arena: &'a mut AstArena,
    bounds: &'a mut Bounds,
    /// enclosing universals: (variable, arity, original domain expression)
    universals: Vec<(VarId, u32, ExprId)>,
    /// upper bounds of the universal domains, aligned with `universals`
    universal_uppers: Vec<TupleSet>,
    fresh: usize,
    created: Vec<RelationId>,
}

impl<'a> StaticSkolemizer<'a> {
    fn subst_expr(
        &mut self,
        e: ExprId,
        map: &HashMap<VarId, ExprId>,
        shadow: &mut HashSet<VarId>,
    ) -> ExprId {
        match self.arena.expr(e).clone() {
            crate::ast::ExprNode::Variable(v) => match map.get(&v) {
                Some(rep) if !shadow.contains(&v) => *rep,
                _ => e,
            },
            crate::ast::ExprNode::Relation(_)
            | crate::ast::ExprNode::Constant(_)
            | crate::ast::ExprNode::FromInt(_)
            | crate::ast::ExprNode::Temporal { .. } => e,
            crate::ast::ExprNode::Unary { op, child } => {
                let c = self.subst_expr(child, map, shadow);
                self.arena.unary_expr(op, c).unwrap_or(e)
            }
            crate::ast::ExprNode::Binary { op, left, right } => {
                let l = self.subst_expr(left, map, shadow);
                let r = self.subst_expr(right, map, shadow);
                self.arena.binary_expr(op, l, r).unwrap_or(e)
            }
            crate::ast::ExprNode::Nary { op, children } => {
                let out: Vec<ExprId> = children
                    .iter()
                    .map(|&c| self.subst_expr(c, map, shadow))
                    .collect();
                self.arena.compose_expr(op, &out).unwrap_or(e)
            }
            crate::ast::ExprNode::If { cond, then, els } => {
                let c = self.subst_formula(cond, map, shadow);
                let t = self.subst_expr(then, map, shadow);
                let el = self.subst_expr(els, map, shadow);
                self.arena.if_expr(c, t, el).unwrap_or(e)
            }
            crate::ast::ExprNode::Project { expr, columns } => {
                let c = self.subst_expr(expr, map, shadow);
                self.arena.project(c, &columns).unwrap_or(e)
            }
            crate::ast::ExprNode::Comprehension { decls, body } => {
                let list = self.arena.decls(decls).to_vec();
                for d in &list {
                    shadow.insert(d.variable);
                }
                let new_decls: Vec<Decl> = list
                    .iter()
                    .map(|d| Decl {
                        mult: d.mult,
                        variable: d.variable,
                        expr: self.subst_expr(d.expr, map, shadow),
                    })
                    .collect();
                let b = self.subst_formula(body, map, shadow);
                for d in &list {
                    shadow.remove(&d.variable);
                }
                let ds = self.arena.add_decls(new_decls);
                self.arena.comprehension(ds, b).unwrap_or(e)
            }
        }
    }

    fn subst_formula(
        &mut self,
        f: FormulaId,
        map: &HashMap<VarId, ExprId>,
        shadow: &mut HashSet<VarId>,
    ) -> FormulaId {
        match self.arena.formula(f).clone() {
            crate::ast::FormulaNode::Constant(_)
            | crate::ast::FormulaNode::TemporalBinary { .. }
            | crate::ast::FormulaNode::TemporalUnary { .. } => f,
            crate::ast::FormulaNode::Not(child) => {
                let c = self.subst_formula(child, map, shadow);
                self.arena.not(c)
            }
            crate::ast::FormulaNode::Nary { op, children } => {
                let out: Vec<FormulaId> = children
                    .iter()
                    .map(|&c| self.subst_formula(c, map, shadow))
                    .collect();
                match op {
                    FormulaBinOp::And => self.arena.and(&out),
                    FormulaBinOp::Or => self.arena.or(&out),
                }
            }
            crate::ast::FormulaNode::Comparison { op, left, right } => {
                let l = self.subst_expr(left, map, shadow);
                let r = self.subst_expr(right, map, shadow);
                self.arena.comparison(op, l, r).unwrap_or(f)
            }
            crate::ast::FormulaNode::IntComparison { op, left, right } => {
                let l = self.subst_int(left, map, shadow);
                let r = self.subst_int(right, map, shadow);
                self.arena.int_comparison(op, l, r)
            }
            crate::ast::FormulaNode::Multiplicity { mult, expr } => {
                let e = self.subst_expr(expr, map, shadow);
                self.arena.multiplicity_formula(mult, e).unwrap_or(f)
            }
            crate::ast::FormulaNode::Quantified { quant, decls, body } => {
                let list = self.arena.decls(decls).to_vec();
                for d in &list {
                    shadow.insert(d.variable);
                }
                let new_decls: Vec<Decl> = list
                    .iter()
                    .map(|d| Decl {
                        mult: d.mult,
                        variable: d.variable,
                        expr: self.subst_expr(d.expr, map, shadow),
                    })
                    .collect();
                let b = self.subst_formula(body, map, shadow);
                for d in &list {
                    shadow.remove(&d.variable);
                }
                let ds = self.arena.add_decls(new_decls);
                self.arena.quantified(quant, ds, b)
            }
        }
    }

    fn subst_int(
        &mut self,
        i: IntId,
        map: &HashMap<VarId, ExprId>,
        shadow: &mut HashSet<VarId>,
    ) -> IntId {
        match self.arena.int(i).clone() {
            crate::ast::IntNode::Constant(_) | crate::ast::IntNode::OfExpr { .. } => i,
            crate::ast::IntNode::Binary { op, left, right } => {
                let l = self.subst_int(left, map, shadow);
                let r = self.subst_int(right, map, shadow);
                self.arena.binary_int(op, l, r)
            }
            crate::ast::IntNode::If { cond, then, els } => {
                let c = self.subst_formula(cond, map, shadow);
                let t = self.subst_int(then, map, shadow);
                let e = self.subst_int(els, map, shadow);
                self.arena.if_int(c, t, e)
            }
            crate::ast::IntNode::Sum { decls, body } => {
                let list = self.arena.decls(decls).to_vec();
                for d in &list {
                    shadow.insert(d.variable);
                }
                let new_decls: Vec<Decl> = list
                    .iter()
                    .map(|d| Decl {
                        mult: d.mult,
                        variable: d.variable,
                        expr: self.subst_expr(d.expr, map, shadow),
                    })
                    .collect();
                let b = self.subst_int(body, map, shadow);
                for d in &list {
                    shadow.remove(&d.variable);
                }
                let ds = self.arena.add_decls(new_decls);
                self.arena.sum_int(ds, b)
            }
        }
    }

    /// Replacement expression for a witness: `$sk` or `join($sk, u1…uk)`.
    fn witness_expr(&mut self, rel: RelationId) -> ExprId {
        let mut acc = self.arena.expr_relation(rel);
        for &(u, _, _) in &self.universals {
            let ue = self.arena.expr_variable(u);
            acc = self.arena.binary_expr(BinaryOp::Join, acc, ue).unwrap();
        }
        acc
    }

    /// Range constraint tying the skolem relation to its domain. With
    /// universals this is `all u⃗: U⃗ | join($sk, u⃗) ⊆ D[u⃗]`.
    fn domain_constraint(
        &mut self,
        rel: RelationId,
        domain: ExprId,
    ) -> Result<FormulaId, SkolemError> {
        let mut acc = self.arena.expr_relation(rel);
        for &(u, _, _) in &self.universals {
            let ue = self.arena.expr_variable(u);
            acc = self.arena.binary_expr(BinaryOp::Join, acc, ue).unwrap();
        }
        let subset = self.arena.comparison(ExprCompOp::Subset, acc, domain)?;
        if self.universals.is_empty() {
            return Ok(subset);
        }
        let decls: Vec<Decl> = self
            .universals
            .iter()
            .map(|&(v, _, dom)| Decl {
                mult: Multiplicity::One,
                variable: v,
                expr: dom,
            })
            .collect();
        let ds = self.arena.add_decls(decls);
        Ok(self.arena.quantified(Quantifier::All, ds, subset))
    }

    fn skolemize_quantifier(
        &mut self,
        decls: &[Decl],
        body: FormulaId,
    ) -> Result<Option<(FormulaId, Vec<FormulaId>)>, SkolemError> {
        // Every declared variable needs a computable domain upper bound.
        let mut uppers = Vec::with_capacity(decls.len());
        for d in decls {
            match upper_bound_expr(self.arena, d.expr, self.bounds) {
                Some(ts) => uppers.push(ts),
                None => return Ok(None), // unsupported domain: leave intact
            }
        }

        let extra: u32 = self.universals.iter().map(|&(_, a, _)| a).sum();
        let mut rels = Vec::with_capacity(decls.len());
        for (d, ub) in decls.iter().zip(&uppers) {
            let k = self.arena.variable_arity(d.variable);
            let name = format!("$sk{}", self.fresh);
            self.fresh += 1;
            let rel = self.arena.relation(&name, k + extra);
            self.arena.set_skolem(rel, true);
            let mut full = ub.clone();
            for uu in &self.universal_uppers {
                // universal columns PRECEDE the witness columns
                full = cross(uu, &full)?;
            }
            let converted = crate::temporal::convert_to_univ_pub(&full, self.bounds.universe())?;
            self.bounds.bound_upper(rel, &converted)?;
            rels.push(rel);
        }

        // Substitute witnesses into the body simultaneously.
        let mut map = HashMap::new();
        for (d, rel) in decls.iter().zip(&rels) {
            let w = self.witness_expr(*rel);
            map.insert(d.variable, w);
        }
        let mut shadow = HashSet::new();
        let new_body = self.subst_formula(body, &map, &mut shadow);
        // inner quantifiers of the substituted body are processed in this
        // (now positive) context
        let new_body = sk_walk(self, new_body, true)?;

        let mut constraints = Vec::with_capacity(decls.len());
        for (d, rel) in decls.iter().zip(&rels) {
            constraints.push(self.domain_constraint(*rel, d.expr)?);
        }
        self.created.extend_from_slice(&rels);
        Ok(Some((new_body, constraints)))
    }
}

/// Result of a successful skolemization pass.
pub struct Skolemized {
    pub formula: FormulaId,
    pub relations: Vec<RelationId>,
}

/// Skolemizes positive existential quantifiers in `formula`, adding witness
/// relation bounds to `bounds`. Returns `None` when nothing was changed
/// (no existentials, or every candidate had an unsupported domain).
///
/// Only OUTERMOST existential quantifiers are replaced; nested ones remain
/// as quantifiers over their (possibly skolem-witnessed) domains.
pub fn skolemize_static(
    arena: &mut AstArena,
    bounds: &mut Bounds,
    formula: FormulaId,
) -> Result<Option<Skolemized>, SkolemError> {
    let mut sk = StaticSkolemizer {
        arena,
        bounds,
        universals: Vec::new(),
        universal_uppers: Vec::new(),
        fresh: 0,
        created: Vec::new(),
    };
    let out = sk_walk(&mut sk, formula, true)?;
    if sk.created.is_empty() {
        return Ok(None);
    }
    Ok(Some(Skolemized {
        formula: out,
        relations: sk.created,
    }))
}

fn sk_walk(
    sk: &mut StaticSkolemizer<'_>,
    f: FormulaId,
    pol: bool,
) -> Result<FormulaId, SkolemError> {
    Ok(match sk.arena.formula(f).clone() {
        crate::ast::FormulaNode::Constant(_)
        | crate::ast::FormulaNode::TemporalUnary { .. }
        | crate::ast::FormulaNode::TemporalBinary { .. }
        | crate::ast::FormulaNode::Comparison { .. }
        | crate::ast::FormulaNode::IntComparison { .. }
        | crate::ast::FormulaNode::Multiplicity { .. } => f,
        crate::ast::FormulaNode::Not(child) => {
            let c = sk_walk(sk, child, !pol)?;
            sk.arena.not(c)
        }
        crate::ast::FormulaNode::Nary { op, children } => {
            let out = children
                .iter()
                .map(|&c| sk_walk(sk, c, pol))
                .collect::<Result<Vec<_>, _>>()?;
            match op {
                FormulaBinOp::And => sk.arena.and(&out),
                FormulaBinOp::Or => sk.arena.or(&out),
            }
        }
        crate::ast::FormulaNode::Quantified { quant, decls, body } => {
            match (quant, pol) {
                // all x: D | F  (positive): scope universals, descend
                (Quantifier::All, true) => {
                    let list = sk.arena.decls(decls).to_vec();
                    for d in &list {
                        let ub = upper_bound_expr(sk.arena, d.expr, sk.bounds)
                            .expect("universal domains must have upper bounds to reach here");
                        sk.universal_uppers.push(ub);
                    }
                    sk.universals.extend(
                        list.iter()
                            .map(|d| (d.variable, sk.arena.variable_arity(d.variable), d.expr)),
                    );
                    let _b = sk_walk(sk, body, true)?;
                    for _ in &list {
                        sk.universals.pop();
                        sk.universal_uppers.pop();
                    }
                    f
                }
                // some x: D | F  (negative): ¬∃ ≡ ∀¬ — keep as quantifier
                (Quantifier::Some, false) => {
                    let list = sk.arena.decls(decls).to_vec();
                    for d in &list {
                        let ub = upper_bound_expr(sk.arena, d.expr, sk.bounds)
                            .expect("universal domains must have upper bounds to reach here");
                        sk.universal_uppers.push(ub);
                    }
                    sk.universals.extend(
                        list.iter()
                            .map(|d| (d.variable, sk.arena.variable_arity(d.variable), d.expr)),
                    );
                    let nb = sk.arena.not(body);
                    let _b = sk_walk(sk, nb, true)?;
                    for _ in &list {
                        sk.universals.pop();
                        sk.universal_uppers.pop();
                    }
                    f
                }
                // some x: D | F  (positive): SKOLEMIZE
                (Quantifier::Some, true) => {
                    let list = sk.arena.decls(decls).to_vec();
                    if let Some((new_body, constraints)) = sk.skolemize_quantifier(&list, body)? {
                        let mut parts = constraints;
                        parts.push(new_body);
                        sk.arena.and(&parts)
                    } else {
                        let b = sk_walk(sk, body, true)?;
                        let ds = sk.arena.add_decls(list);
                        sk.arena.quantified(Quantifier::Some, ds, b)
                    }
                }
                // all x: D | F  (negative): ¬∀ ≡ ∃¬ — flip to SOME and skolemize
                (Quantifier::All, false) => {
                    let list = sk.arena.decls(decls).to_vec();
                    let nb = sk.arena.not(body);
                    if let Some((new_body, constraints)) = sk.skolemize_quantifier(&list, nb)? {
                        let mut parts = constraints;
                        parts.push(new_body);
                        sk.arena.and(&parts)
                    } else {
                        let b = sk_walk(sk, nb, false)?;
                        let ds = sk.arena.add_decls(list);
                        sk.arena.quantified(Quantifier::All, ds, b)
                    }
                }
            }
        }
    })
}
