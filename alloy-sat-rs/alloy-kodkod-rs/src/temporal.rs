//! Temporal extension (Iter 7): ltl2fol-style bounded lasso unrolling.
//!
//! Port of Pardinus `TemporalBoundsExpander` + `LTL2FOLTranslator`
//! (ExplicitUnrolls=true, future-time fragment):
//!
//! 1. [`expand_bounds`] appends the trace state atoms `Time{i}_0` to the
//!    universe, gives every *variable* relation a time-extended expansion
//!    `r$t` of arity+1 (original tuples x state), and adds the helper
//!    relations `$t_first`/`$t_last`/`$t_next`/`$t_loop`.
//! 2. [`translate_temporal_formula`] rewrites the temporal AST into pure FOL
//!    over the expanded bounds: temporal operators become quantifiers over the
//!    reachable states (`t.*TRACE` where `TRACE = $t_next ∪ $t_last×$t_loop`),
//!    and variable leaves are joined with the current time.
//! 3. After solving, [`extract_temporal_instance`] projects the model back
//!    into a [`TemporalInstance`] lasso (one [`Instance`] per state + loop
//!    point).
//!
//! Supported: PRIME, ALWAYS, EVENTUALLY, UNTIL, RELEASES (+ NNF polarity
//! pushing). Past-time operators (HISTORICALLY/ONCE/BEFORE/SINCE/TRIGGERED)
//! require unrolls > 1 and are rejected.

use std::collections::{BTreeSet, HashMap};
use std::sync::Arc;

use crate::ast::{
    AstArena, BinaryOp, ConstantExpr, ExprCompOp, ExprId, FormulaBinOp, FormulaId, IntCompOp,
    IntId, Multiplicity, Quantifier, TemporalBinaryOp, TemporalExprOp, TemporalFormulaOp, VarId,
};
use crate::eval::{
    closure, cross, difference, intersection, join, override_sets, transpose, union, EvalError,
    Evaluator,
};
use crate::instance::Instance;
use crate::relation::{RelationId, RelationPool};
use crate::tupleset::TupleSet;
use crate::universe::Universe;

pub const STATE_ATOM: &str = "Time";
pub const STATE_SEP: &str = "_";

#[derive(Debug, thiserror::Error)]
pub enum TemporalError {
    #[error("steps and unrolls must be >= 1")]
    BadTraceLength,
    #[error("past-time operator {0} is not supported (requires unrolls > 1)")]
    UnsupportedPast(&'static str),
    #[error("unrolls > 1 is only meaningful with past operators; use unrolls = 1")]
    UnrollsWithoutPast,
    #[error("relation {0} is not bound")]
    UnboundRelation(u32),
    #[error("bounds error: {0}")]
    Bounds(#[from] crate::bounds::BoundsError),
    #[error("tuple set error: {0}")]
    Capacity(#[from] crate::tupleset::CapacityError),
    #[error("ast error: {0}")]
    Ast(#[from] crate::ast::AstError),
    #[error("evaluation failed: {0}")]
    Eval(#[from] EvalError),
    #[error("instance error: {0}")]
    Instance(#[from] crate::instance::InstanceError),
}

/// Helper relation ids created by the expander.
#[derive(Debug, Clone, Copy)]
pub struct TraceIds {
    /// unary `$t_state`: all trace states
    pub state: RelationId,
    /// unary `$t_first`: exact {Time0_0}
    pub first: RelationId,
    /// unary `$t_last`: exact {Time{steps-1}_0}
    pub last: RelationId,
    /// binary `$t_next`: chain edges; upper bound also allows every
    /// last→k loop-back edge
    pub prefix: RelationId,
    /// unary `$t_loop`: free (upper-only); constrained to exactly one state
    pub loop_: RelationId,
}

/// Result of bounds expansion.
#[derive(Debug)]
pub struct TemporalExpansion {
    /// expanded static bounds over the extended universe
    pub bounds: crate::bounds::Bounds,
    pub ids: TraceIds,
    /// variable relation -> its time-expanded relation `r$t`
    pub mapping: HashMap<RelationId, RelationId>,
    pub steps: usize,
    pub unrolls: usize,
    /// the original (pre-expansion) universe
    pub orig_universe: Arc<Universe>,
    pub pool: Arc<RelationPool>,
    /// number of atoms in the original universe (time block starts here)
    base: usize,
}

impl TemporalExpansion {
    /// The expanded universe (original atoms + trace state atoms).
    pub fn universe(&self) -> &Arc<Universe> {
        self.bounds.universe()
    }

    /// Pins an already-expanded relation to an exact tuple set (used by the
    /// dynamic decomposer to anchor stage-1 results).
    pub fn anchor_relation(
        &mut self,
        expanded: RelationId,
        ts: &TupleSet,
    ) -> Result<(), TemporalError> {
        let converted = convert_to_univ_pub(ts, self.bounds.universe())?;
        self.bounds.bound_exactly(expanded, &converted)?;
        Ok(())
    }
}

impl TemporalExpansion {
    /// flat index of state atom `Time{i}_{j}`
    pub fn state_index(&self, i: usize, j: usize) -> i64 {
        (self.base + j * self.steps + i) as i64
    }

    pub fn state_atom_name(i: usize, j: usize) -> String {
        format!("{STATE_ATOM}{i}{STATE_SEP}{j}")
    }
}

/// Re-encodes a flat tuple index from one universe size to another.
///
/// Appending atoms keeps every ORIGINAL atom's coordinate valid, but the
/// positional encoding base changes, so flat indices must be recomputed for
/// arity >= 2.
fn reencode(flat: i64, old_size: usize, new_size: usize, arity: u32, offset: usize) -> i64 {
    if arity == 0 {
        return 0;
    }
    let mut digits = vec![0i64; arity as usize];
    let mut cur = flat;
    for d in digits.iter_mut().rev() {
        *d = cur % old_size as i64;
        cur /= old_size as i64;
    }
    let mut out = 0i64;
    for d in digits {
        out = out * new_size as i64 + d + offset as i64;
    }
    out
}

/// Public re-export for the skolemizer: converts a tuple set into an
/// identical one over `uni` (re-encoding flat indices when sizes differ).
pub fn convert_to_univ_pub(
    ts: &TupleSet,
    uni: &Arc<Universe>,
) -> Result<TupleSet, crate::tupleset::CapacityError> {
    let old_size = ts.universe().size();
    let new_size = uni.size();
    let arity = ts.arity();
    let mut out = TupleSet::new(uni, arity)?;
    if old_size == new_size {
        for idx in ts.index_view().iter() {
            out.insert_index(idx);
        }
    } else {
        for idx in ts.index_view().iter() {
            out.insert_index(reencode(idx, old_size, new_size, arity, 0));
        }
    }
    Ok(out)
}

fn convert_to_univ(ts: &TupleSet, uni: &Arc<Universe>) -> Result<TupleSet, TemporalError> {
    let old_size = ts.universe().size();
    let new_size = uni.size();
    let arity = ts.arity();
    let mut out = TupleSet::new(uni, arity)?;
    if old_size == new_size {
        for idx in ts.index_view().iter() {
            out.insert_index(idx);
        }
    } else {
        for idx in ts.index_view().iter() {
            out.insert_index(reencode(idx, old_size, new_size, arity, 0));
        }
    }
    Ok(out)
}

/// Port of `TemporalBoundsExpander.expand` for the future-time fragment
/// (`unrolls == 1`, no UNROLL_MAP).
///
/// Relations must be marked variable with `pool.set_variable(r, true)` before
/// calling. The expanded relations keep the ORIGINAL flat atom indices (time
/// atoms are appended after the original ones).
pub fn expand_bounds(
    arena: &AstArena,
    bounds: &crate::bounds::Bounds,
    steps: usize,
    unrolls: usize,
) -> Result<TemporalExpansion, TemporalError> {
    if steps < 1 || unrolls < 1 {
        return Err(TemporalError::BadTraceLength);
    }
    if unrolls > 1 {
        return Err(TemporalError::UnrollsWithoutPast);
    }

    let orig_universe = bounds.universe().clone();
    let pool = bounds.pool().clone();

    // --- expanded universe: original atoms, then Time{i}_{j} ---
    let mut names: Vec<String> = orig_universe.iter().map(|a| a.to_string()).collect();
    for j in 0..unrolls {
        for i in 0..steps {
            names.push(TemporalExpansion::state_atom_name(i, j));
        }
    }
    let refs: Vec<&str> = names.iter().map(|s| s.as_str()).collect();
    let uni = Universe::new(refs).map_err(|_| TemporalError::BadTraceLength)?;
    let base = orig_universe.size();

    let state_rel = arena.relation("$t_state", 1);
    let first = arena.relation("$t_first", 1);
    let last = arena.relation("$t_last", 1);
    let prefix = arena.relation("$t_next", 2);
    let loop_ = arena.relation("$t_loop", 1);
    let ids = TraceIds {
        state: state_rel,
        first,
        last,
        prefix,
        loop_,
    };

    let mut new_bounds = crate::bounds::Bounds::new(&uni, &pool);

    // --- helper relations ---
    let all_states = state_set(&uni, base, steps, unrolls)?;
    new_bounds.bound_exactly(state_rel, &all_states)?;
    new_bounds.bound_exactly(first, &single(&uni, base)?)?;
    new_bounds.bound_exactly(last, &single(&uni, base + steps - 1)?)?;

    // PREFIX: lower = unroll-0 chain; upper = chains + all loop-backs from LAST
    let mut prefix_l = TupleSet::new(&uni, 2)?;
    let mut prefix_u = TupleSet::new(&uni, 2)?;
    let width = uni.size() as i64;
    for i in 0..steps - 1 {
        prefix_l.insert_index(((base + i) as i64) * width + (base + i + 1) as i64);
    }
    for idx in prefix_l.index_view().iter() {
        prefix_u.insert_index(idx);
    }
    for k in 0..steps {
        // LAST -> any k (the actual edge is selected through TRACE = PREFIX ∪ LAST×LOOP)
        prefix_u.insert_index(((base + steps - 1) as i64) * width + (base + k) as i64);
    }
    new_bounds.bound(prefix, &prefix_l, &prefix_u)?;

    // LOOP: free unary over all states; formula constrains it to one()
    new_bounds.bound_upper(loop_, &all_states)?;

    // --- user relations ---
    let mut mapping = HashMap::new();
    for r in bounds.relations() {
        if !pool.is_variable(r) {
            continue;
        }
        let arity = pool.arity(r);
        let name = pool.name(r);
        let exp = arena.relation(&format!("{name}$t"), arity + 1);
        if mapping.insert(r, exp).is_some() {
            return Err(TemporalError::UnboundRelation(r.0));
        }
    }

    for r in bounds.relations() {
        let lower = bounds
            .lower_bound(r)
            .ok_or(TemporalError::UnboundRelation(r.0))?;
        let upper = bounds
            .upper_bound(r)
            .ok_or(TemporalError::UnboundRelation(r.0))?;
        let lower = convert_to_univ(lower, &uni)?;
        let upper = convert_to_univ(upper, &uni)?;
        match mapping.get(&r) {
            None => {
                new_bounds.bound(r, &lower, &upper)?;
            }
            Some(&exp) => {
                // product with the first-unroll state column
                let mut low_exp = TupleSet::new(&uni, lower.arity() + 1)?;
                let mut up_exp = TupleSet::new(&uni, upper.arity() + 1)?;
                let width = uni.size() as i64;
                let base_i = base as i64;
                let old_size = orig_universe.size();
                let exp_arity = lower.arity() + 1;
                for idx in lower.index_view().iter() {
                    for s in 0..steps as i64 {
                        let row = reencode(idx, old_size, uni.size(), exp_arity - 1, 0);
                        low_exp.insert_index(row * width + base_i + s);
                    }
                }
                for idx in upper.index_view().iter() {
                    for s in 0..steps as i64 {
                        let row = reencode(idx, old_size, uni.size(), exp_arity - 1, 0);
                        up_exp.insert_index(row * width + base_i + s);
                    }
                }
                new_bounds.bound(exp, &low_exp, &up_exp)?;
            }
        }
    }

    // integer bounds carry over verbatim (atom indices unchanged)
    for (i, ts) in bounds.int_bounds() {
        let ts = convert_to_univ(ts, &uni)?;
        new_bounds.bound_exactly_int(i, &ts)?;
    }

    Ok(TemporalExpansion {
        bounds: new_bounds,
        ids,
        mapping,
        steps,
        unrolls,
        orig_universe,
        pool,
        base,
    })
}

fn state_set(
    uni: &Arc<Universe>,
    base: usize,
    steps: usize,
    unrolls: usize,
) -> Result<TupleSet, TemporalError> {
    let mut ts = TupleSet::new(uni, 1)?;
    for j in 0..unrolls {
        for i in 0..steps {
            ts.insert_index((base + j * steps + i) as i64);
        }
    }
    Ok(ts)
}

fn single(uni: &Arc<Universe>, index: usize) -> Result<TupleSet, TemporalError> {
    let mut ts = TupleSet::new(uni, 1)?;
    ts.insert_index(index as i64);
    Ok(ts)
}

/// Registers a temporal Skolem witness relation (HASLab-style): `$name` of
/// arity `value_arity + 1` whose last column ranges over trace states and
/// whose rows are bounded by `upper_orig × STATES`.
pub fn add_witness_relation(
    exp: &mut TemporalExpansion,
    arena: &mut AstArena,
    name: &str,
    value_arity: u32,
    upper_orig: &TupleSet,
) -> Result<RelationId, TemporalError> {
    let uni = exp.bounds.universe().clone();
    let width = uni.size() as i64;
    let rel = arena.relation(name, value_arity + 1);
    exp.pool.set_skolem(rel, true);
    let converted = convert_to_univ_pub(upper_orig, &uni)?;
    let mut up = TupleSet::new(&uni, value_arity + 1)?;
    for idx in converted.index_view().iter() {
        for s in 0..exp.steps as i64 {
            up.insert_index(idx * width + exp.base as i64 + s);
        }
    }
    exp.bounds.bound_upper(rel, &up)?;
    Ok(rel)
}

/// One collected temporal skolemization site.
#[derive(Clone)]
pub struct WitnessSpec {
    /// the quantified variable being replaced
    pub var: VarId,
    /// original (pre-expansion) domain expression
    pub domain: ExprId,
    /// witness relation name
    pub name: String,
    /// value arity of the witness
    pub value_arity: u32,
}

/// Collects OUTERMOST skolemizable existential quantifiers:
/// positive `some` under a totality context (top level / always), not under
/// FOL universals, with a computable domain upper bound.
#[allow(clippy::too_many_arguments)]
pub fn collect_witness_specs(
    arena: &mut AstArena,
    bounds: &crate::bounds::Bounds,
    f: FormulaId,
    pol: bool,
    total: bool,
    under_universal: bool,
    out: &mut Vec<WitnessSpec>,
    counter: &mut usize,
) {
    if !pol || under_universal {
        return;
    }
    match arena.formula(f).clone() {
        crate::ast::FormulaNode::Constant(_)
        | crate::ast::FormulaNode::Comparison { .. }
        | crate::ast::FormulaNode::IntComparison { .. }
        | crate::ast::FormulaNode::Multiplicity { .. }
        | crate::ast::FormulaNode::TemporalBinary { .. } => {}
        crate::ast::FormulaNode::Not(child) => {
            collect_witness_specs(
                arena,
                bounds,
                child,
                !pol,
                total,
                under_universal,
                out,
                counter,
            );
        }
        crate::ast::FormulaNode::Nary { children, .. } => {
            for c in children {
                collect_witness_specs(arena, bounds, c, pol, total, under_universal, out, counter);
            }
        }
        crate::ast::FormulaNode::TemporalUnary { op, child } => match op {
            TemporalFormulaOp::Always => collect_witness_specs(
                arena,
                bounds,
                child,
                pol,
                true,
                under_universal,
                out,
                counter,
            ),
            TemporalFormulaOp::Eventually => collect_witness_specs(
                arena,
                bounds,
                child,
                pol,
                false,
                under_universal,
                out,
                counter,
            ),
            _ => {}
        },
        crate::ast::FormulaNode::Quantified { quant, decls, body } => match quant {
            Quantifier::All => {
                collect_witness_specs(arena, bounds, body, pol, total, true, out, counter);
            }
            Quantifier::Some => {
                if !total || decls_len(arena, decls) != 1 {
                    return;
                }
                let d = arena.decls(decls)[0];
                if crate::skolem::upper_bound_expr(arena, d.expr, bounds).is_none() {
                    return;
                }
                let k = arena.variable_arity(d.variable);
                let name = format!("$sk{}", counter);
                *counter += 1;
                out.push(WitnessSpec {
                    var: d.variable,
                    domain: d.expr,
                    name,
                    value_arity: k,
                });
                // nested content is skipped: the whole quantifier disappears
            }
        },
    }
}

fn decls_len(arena: &AstArena, id: DeclsIdT) -> usize {
    arena.decls(id).len()
}

type DeclsIdT = crate::ast::DeclsId;

// ---------------------------------------------------------------------------
// LTL -> FOL rewrite
// ---------------------------------------------------------------------------

/// One step of the symbolic "current time": either the FIRST state, a bound
/// quantifier variable over states, or `t.join(TRACE)` (PRIME/AFTER).
#[derive(Clone)]
enum T {
    Init,
    Next(Box<T>),
    At(VarId),
}

struct Ltl2Fol<'a> {
    arena: &'a mut AstArena,
    ids: TraceIds,
    mapping: &'a HashMap<RelationId, RelationId>,
    /// temporal Skolem witnesses (HASLab): quantified var -> expanded rel
    skolems: HashMap<VarId, RelationId>,
    /// (witness relation, original domain expression)
    witness_specs: Vec<(RelationId, ExprId)>,
    fresh: usize,
}

impl<'a> Ltl2Fol<'a> {
    fn trace_expr(&mut self) -> ExprId {
        // TRACE = PREFIX ∪ (LAST × LOOP)
        let p = self.arena.expr_relation(self.ids.prefix);
        let l = self.arena.expr_relation(self.ids.last);
        let lo = self.arena.expr_relation(self.ids.loop_);
        let ll = self.arena.binary_expr(BinaryOp::Product, l, lo).unwrap();
        self.arena.binary_expr(BinaryOp::Union, p, ll).unwrap()
    }

    fn time_expr(&mut self, t: &T) -> ExprId {
        match t {
            T::Init => self.arena.expr_relation(self.ids.first),
            T::At(v) => self.arena.expr_variable(*v),
            T::Next(inner) => {
                let te = self.time_expr(inner);
                let tr = self.trace_expr();
                self.arena.binary_expr(BinaryOp::Join, te, tr).unwrap()
            }
        }
    }

    fn reach_expr(&mut self, t: &T) -> ExprId {
        // t .* TRACE  (reflexive-transitive closure)
        let te = self.time_expr(t);
        let tr = self.trace_expr();
        let rc = self
            .arena
            .unary_expr(crate::ast::UnaryExprOp::ReflexiveClosure, tr)
            .unwrap();
        self.arena.binary_expr(BinaryOp::Join, te, rc).unwrap()
    }

    fn fresh_var(&mut self, tag: &str) -> VarId {
        let v = self.arena.variable(&format!("$t_{tag}{}", self.fresh));
        self.fresh += 1;
        v
    }

    /// `upTo(t1, t2, incl)` port: all states between t1 and t2 considering
    /// loops, distinguishing in-prefix order from through-loop order.
    fn upto_expr(&mut self, t1: &T, r: VarId, incl: bool) -> ExprId {
        let e_t1 = self.time_expr(t1);
        let e_r = self.arena.expr_variable(r);
        let prefix = self.arena.expr_relation(self.ids.prefix);
        let prefix_t = self
            .arena
            .unary_expr(crate::ast::UnaryExprOp::Transpose, prefix)
            .unwrap();
        let trace = self.trace_expr();
        let trace_t = self
            .arena
            .unary_expr(crate::ast::UnaryExprOp::Transpose, trace)
            .unwrap();

        // c : t2 in t1.^PREFIX
        let p_rc = self
            .arena
            .unary_expr(crate::ast::UnaryExprOp::ReflexiveClosure, prefix)
            .unwrap();
        let c_lhs = self.arena.binary_expr(BinaryOp::Join, e_t1, p_rc).unwrap();
        let c = self
            .arena
            .comparison(ExprCompOp::Subset, e_r, c_lhs)
            .unwrap();

        // e1 : t1.^PREFIX ∩ t2.*~PREFIX
        let pt_cl = self
            .arena
            .unary_expr(crate::ast::UnaryExprOp::Closure, prefix_t)
            .unwrap();
        let a1 = self.arena.binary_expr(BinaryOp::Join, e_t1, p_rc).unwrap();
        let b1 = self.arena.binary_expr(BinaryOp::Join, e_r, pt_cl).unwrap();
        let e1 = self
            .arena
            .binary_expr(BinaryOp::Intersection, a1, b1)
            .unwrap();

        // e21 : t1.*TRACE ∩ t2.*~TRACE
        let t_rc = self
            .arena
            .unary_expr(crate::ast::UnaryExprOp::ReflexiveClosure, trace)
            .unwrap();
        let tt_cl = self
            .arena
            .unary_expr(crate::ast::UnaryExprOp::Closure, trace_t)
            .unwrap();
        let a21 = self.arena.binary_expr(BinaryOp::Join, e_t1, t_rc).unwrap();
        let b21 = self.arena.binary_expr(BinaryOp::Join, e_r, tt_cl).unwrap();
        let e21 = self
            .arena
            .binary_expr(BinaryOp::Intersection, a21, b21)
            .unwrap();

        // e22 : t2.^PREFIX ∩ t1.*~PREFIX
        let a22 = self.arena.binary_expr(BinaryOp::Join, e_r, p_rc).unwrap();
        let b22 = self.arena.binary_expr(BinaryOp::Join, e_t1, pt_cl).unwrap();
        let e22 = self
            .arena
            .binary_expr(BinaryOp::Intersection, a22, b22)
            .unwrap();

        let e2 = self
            .arena
            .binary_expr(BinaryOp::Difference, e21, e22)
            .unwrap();

        let mut e = self.arena.if_expr(c, e1, e2).unwrap();
        if incl {
            e = self.arena.binary_expr(BinaryOp::Union, e, e_r).unwrap();
        }
        e
    }

    fn formula(&mut self, f: FormulaId, pol: bool, t: &T) -> Result<FormulaId, TemporalError> {
        match self.arena.formula(f).clone() {
            crate::ast::FormulaNode::Constant(v) => Ok(self.arena.bool_formula(v == pol)),
            crate::ast::FormulaNode::Not(child) => self.formula(child, !pol, t),
            crate::ast::FormulaNode::Nary { op, children } => {
                let mut out = Vec::with_capacity(children.len());
                for &c in &children {
                    out.push(self.formula(c, pol, t)?);
                }
                let op = match op {
                    FormulaBinOp::And => {
                        if pol {
                            FormulaBinOp::And
                        } else {
                            FormulaBinOp::Or
                        }
                    }
                    FormulaBinOp::Or => {
                        if pol {
                            FormulaBinOp::Or
                        } else {
                            FormulaBinOp::And
                        }
                    }
                };
                Ok(match op {
                    FormulaBinOp::And => self.arena.and(&out),
                    FormulaBinOp::Or => self.arena.or(&out),
                })
            }
            crate::ast::FormulaNode::Comparison { op, left, right } => {
                let l = self.expr(left, t)?;
                let r = self.expr(right, t)?;
                let cmp = self.arena.comparison(op, l, r)?;
                Ok(if pol { cmp } else { self.arena.not(cmp) })
            }
            crate::ast::FormulaNode::IntComparison { op, left, right } => {
                let l = self.int_expr(left, t)?;
                let r = self.int_expr(right, t)?;
                let cmp = self.arena.int_comparison(op, l, r);
                Ok(if pol { cmp } else { self.arena.not(cmp) })
            }
            crate::ast::FormulaNode::Multiplicity { mult, expr } => {
                let e = self.expr(expr, t)?;
                let m = self.arena.multiplicity_formula(mult, e)?;
                Ok(if pol { m } else { self.arena.not(m) })
            }
            crate::ast::FormulaNode::Quantified { quant, decls, body }
                if quant == Quantifier::Some && !self.skolems.is_empty() =>
            {
                let decl_list = self.arena.decls(decls).to_vec();
                if decl_list.len() == 1 && self.skolems.contains_key(&decl_list[0].variable) {
                    // witness relation replaces the existential entirely
                    return self.formula(body, pol, t);
                }
                let mut new_decls = Vec::with_capacity(decl_list.len());
                for d in decl_list {
                    let e = self.expr(d.expr, t)?;
                    new_decls.push(self.arena.decl(d.variable, d.mult, e)?);
                }
                let ds = self.arena.add_decls(new_decls);
                let q = if pol {
                    quant
                } else {
                    match quant {
                        Quantifier::All => Quantifier::Some,
                        Quantifier::Some => Quantifier::All,
                    }
                };
                let b = self.formula(body, pol, t)?;
                Ok(self.arena.quantified(q, ds, b))
            }
            crate::ast::FormulaNode::Quantified { quant, decls, body } => {
                let decl_list = self.arena.decls(decls).to_vec();
                let mut new_decls = Vec::with_capacity(decl_list.len());
                for d in decl_list {
                    let e = self.expr(d.expr, t)?;
                    new_decls.push(self.arena.decl(d.variable, d.mult, e)?);
                }
                let ds = self.arena.add_decls(new_decls);
                let q = if pol {
                    quant
                } else {
                    match quant {
                        Quantifier::All => Quantifier::Some,
                        Quantifier::Some => Quantifier::All,
                    }
                };
                let body = self.formula(body, pol, t)?;
                Ok(self.arena.quantified(q, ds, body))
            }
            crate::ast::FormulaNode::TemporalUnary { op, child } => match op {
                TemporalFormulaOp::Always | TemporalFormulaOp::Eventually => {
                    let always = op == TemporalFormulaOp::Always;
                    // ALWAYS f ≡ all s: reach | f[s];  ¬◇g ≡ all ¬g; etc.
                    let positive_always = always == pol;
                    let v = self.fresh_var("q");
                    let domain = self.reach_expr(t);
                    let d = self.arena.decl(v, Multiplicity::One, domain)?;
                    let ds = self.arena.add_decls(vec![d]);
                    let body = self.formula(child, true, &T::At(v))?;
                    let q = if positive_always {
                        Quantifier::All
                    } else {
                        Quantifier::Some
                    };
                    Ok(self.arena.quantified(q, ds, body))
                }
                TemporalFormulaOp::After => {
                    let inner = self.formula(child, pol, &T::Next(Box::new(t.clone())))?;
                    Ok(if pol { inner } else { self.arena.not(inner) })
                }
                TemporalFormulaOp::Before => Err(TemporalError::UnsupportedPast("before")),
                TemporalFormulaOp::Historically => {
                    Err(TemporalError::UnsupportedPast("historically"))
                }
                TemporalFormulaOp::Once => Err(TemporalError::UnsupportedPast("once")),
            },
            crate::ast::FormulaNode::TemporalBinary { op, left, right } => match op {
                TemporalBinaryOp::Until => {
                    if pol {
                        self.until(left, right, t)
                    } else {
                        // ¬(a U b) ≡ releases(¬a, ¬b)
                        self.releases(left, right, t)
                    }
                }
                TemporalBinaryOp::Releases => {
                    if pol {
                        self.releases(left, right, t)
                    } else {
                        // ¬(a R b) ≡ until(¬a, ¬b)
                        self.until(left, right, t)
                    }
                }
                TemporalBinaryOp::Since => Err(TemporalError::UnsupportedPast("since")),
                TemporalBinaryOp::Triggered => Err(TemporalError::UnsupportedPast("triggered")),
            },
        }
    }

    /// a U b @ t = some r: t.*TRACE | b[r] && all l: upTo(t, r): a[l]
    fn until(
        &mut self,
        left: FormulaId,
        right: FormulaId,
        t: &T,
    ) -> Result<FormulaId, TemporalError> {
        let v = self.fresh_var("u");
        let domain = self.reach_expr(t);
        let d = self.arena.decl(v, Multiplicity::One, domain)?;
        let ds = self.arena.add_decls(vec![d]);

        let rb = self.formula(right, true, &T::At(v))?;

        let lvar = self.fresh_var("w");
        let range = self.upto_expr(t, v, false);
        let dl = self.arena.decl(lvar, Multiplicity::One, range)?;
        let dsl = self.arena.add_decls(vec![dl]);
        let la = self.formula(left, true, &T::At(lvar))?;
        let forall_a = self.arena.quantified(Quantifier::All, dsl, la);

        let body = self.arena.and(&[rb, forall_a]);
        Ok(self.arena.quantified(Quantifier::Some, ds, body))
    }

    /// a R b @ t = all r: t.*TRACE | b[r] || (a[r] && all l: upTo(t, r): b[l])
    fn releases(
        &mut self,
        left: FormulaId,
        right: FormulaId,
        t: &T,
    ) -> Result<FormulaId, TemporalError> {
        let v = self.fresh_var("r");
        let domain = self.reach_expr(t);
        let d = self.arena.decl(v, Multiplicity::One, domain)?;
        let ds = self.arena.add_decls(vec![d]);

        let ra = self.formula(left, true, &T::At(v))?;
        let rb = self.formula(right, true, &T::At(v))?;

        let lvar = self.fresh_var("s");
        let range = self.upto_expr(t, v, false);
        let dl = self.arena.decl(lvar, Multiplicity::One, range)?;
        let dsl = self.arena.add_decls(vec![dl]);
        let lb = self.formula(right, true, &T::At(lvar))?;
        let forall_b = self.arena.quantified(Quantifier::All, dsl, lb);

        let conj = self.arena.and(&[ra, forall_b]);
        let disj = self.arena.or(&[rb, conj]);
        Ok(self.arena.quantified(Quantifier::All, ds, disj))
    }

    fn int_expr(&mut self, i: IntId, t: &T) -> Result<IntId, TemporalError> {
        match self.arena.int(i).clone() {
            crate::ast::IntNode::Constant(_) => Ok(i),
            crate::ast::IntNode::OfExpr { op, expr } => {
                let e = self.expr(expr, t)?;
                Ok(self.arena.cast_to_int(op, e)?)
            }
            crate::ast::IntNode::Binary { op, left, right } => {
                let l = self.int_expr(left, t)?;
                let r = self.int_expr(right, t)?;
                Ok(self.arena.binary_int(op, l, r))
            }
            crate::ast::IntNode::If { cond, then, els } => {
                let c = self.formula(cond, true, t)?;
                let th = self.int_expr(then, t)?;
                let el = self.int_expr(els, t)?;
                Ok(self.arena.if_int(c, th, el))
            }
            crate::ast::IntNode::Sum { decls, body } => {
                let decl_list = self.arena.decls(decls).to_vec();
                let mut new_decls = Vec::with_capacity(decl_list.len());
                for d in decl_list {
                    let e = self.expr(d.expr, t)?;
                    new_decls.push(self.arena.decl(d.variable, d.mult, e)?);
                }
                let ds = self.arena.add_decls(new_decls);
                let b = self.int_expr(body, t)?;
                Ok(self.arena.sum_int(ds, b))
            }
        }
    }

    fn expr(&mut self, e: ExprId, t: &T) -> Result<ExprId, TemporalError> {
        match self.arena.expr(e).clone() {
            crate::ast::ExprNode::Relation(r) => {
                if let Some(&exp) = self.mapping.get(&r) {
                    let te = self.time_expr(t);
                    let er = self.arena.expr_relation(exp);
                    Ok(self.arena.binary_expr(BinaryOp::Join, er, te).unwrap())
                } else {
                    Ok(e)
                }
            }
            crate::ast::ExprNode::Variable(v) => {
                if let Some(&rel) = self.skolems.get(&v) {
                    // witness at the current time: join($sk, τ)
                    let re = self.arena.expr_relation(rel);
                    let te = self.time_expr(t);
                    Ok(self.arena.binary_expr(BinaryOp::Join, re, te).unwrap())
                } else {
                    Ok(e)
                }
            }
            crate::ast::ExprNode::FromInt(_) => Ok(e),
            crate::ast::ExprNode::Constant(c) => match c {
                ConstantExpr::Univ => {
                    // UNIV − State
                    let u = self.arena.univ();
                    let st = self.arena.expr_relation(self.ids.state);
                    Ok(self.arena.binary_expr(BinaryOp::Difference, u, st).unwrap())
                }
                ConstantExpr::Iden => {
                    // IDEN − (State × State)
                    let id = self.arena.iden();
                    let st = self.arena.expr_relation(self.ids.state);
                    let sp = self.arena.binary_expr(BinaryOp::Product, st, st).unwrap();
                    Ok(self
                        .arena
                        .binary_expr(BinaryOp::Difference, id, sp)
                        .unwrap())
                }
                ConstantExpr::Empty | ConstantExpr::Ints => Ok(e),
            },
            crate::ast::ExprNode::Temporal { op, child } => match op {
                TemporalExprOp::Prime => {
                    let inner = self.expr(child, &T::Next(Box::new(t.clone())))?;
                    Ok(inner)
                }
            },
            crate::ast::ExprNode::Unary { op, child } => {
                let c = self.expr(child, t)?;
                self.arena.unary_expr(op, c).map_err(TemporalError::from)
            }
            crate::ast::ExprNode::Binary { op, left, right } => {
                let l = self.expr(left, t)?;
                let r = self.expr(right, t)?;
                self.arena
                    .binary_expr(op, l, r)
                    .map_err(TemporalError::from)
            }
            crate::ast::ExprNode::Nary { op, children } => {
                let mut out = Vec::with_capacity(children.len());
                for &c in &children {
                    out.push(self.expr(c, t)?);
                }
                self.arena
                    .compose_expr(op, &out)
                    .map_err(TemporalError::from)
            }
            crate::ast::ExprNode::If { cond, then, els } => {
                let c = self.formula(cond, true, t)?;
                let th = self.expr(then, t)?;
                let el = self.expr(els, t)?;
                self.arena.if_expr(c, th, el).map_err(TemporalError::from)
            }
            crate::ast::ExprNode::Project { .. } => Ok(e),
            crate::ast::ExprNode::Comprehension { decls, body } => {
                let decl_list = self.arena.decls(decls).to_vec();
                let mut new_decls = Vec::with_capacity(decl_list.len());
                for d in decl_list {
                    let de = self.expr(d.expr, t)?;
                    new_decls.push(self.arena.decl(d.variable, d.mult, de)?);
                }
                let ds = self.arena.add_decls(new_decls);
                let b = self.formula(body, true, t)?;
                self.arena.comprehension(ds, b).map_err(TemporalError::from)
            }
        }
    }
}

/// Rewrites the temporal formula into pure FOL over the expanded bounds and
/// conjoins the trace axioms (port of `LTL2FOLTranslator.translate`).
pub fn translate_temporal_formula(
    arena: &mut AstArena,
    formula: FormulaId,
    exp: &TemporalExpansion,
    witnesses: &HashMap<VarId, RelationId>,
    witness_domains: &[(RelationId, ExprId)],
) -> Result<FormulaId, TemporalError> {
    let mut tr = Ltl2Fol {
        arena,
        ids: exp.ids,
        mapping: &exp.mapping,
        skolems: witnesses.clone(),
        witness_specs: witness_domains.to_vec(),
        fresh: 0,
    };

    // --- trace structure axioms ---
    let st = tr.arena.expr_relation(exp.ids.state);
    let fi = tr.arena.expr_relation(exp.ids.first);
    let la = tr.arena.expr_relation(exp.ids.last);
    let px = tr.arena.expr_relation(exp.ids.prefix);
    let lp = tr.arena.expr_relation(exp.ids.loop_);

    let v1 = tr.fresh_var("o");
    let dom1 = {
        let diff = tr.arena.binary_expr(BinaryOp::Difference, st, la).unwrap();
        tr.arena.decl(v1, Multiplicity::One, diff)?
    };
    let next_of_v = {
        let vv = tr.arena.expr_variable(v1);
        tr.arena.binary_expr(BinaryOp::Join, vv, px).unwrap()
    };
    let one_next = tr
        .arena
        .multiplicity_formula(Multiplicity::One, next_of_v)?;
    let ds1 = tr.arena.add_decls(vec![dom1]);
    let ax_next_total = tr.arena.quantified(Quantifier::All, ds1, one_next);

    let v2 = tr.fresh_var("o");
    let dom2 = {
        let diff = tr.arena.binary_expr(BinaryOp::Difference, st, fi).unwrap();
        tr.arena.decl(v2, Multiplicity::One, diff)?
    };
    let prev_of_v = {
        let vv = tr.arena.expr_variable(v2);
        tr.arena.binary_expr(BinaryOp::Join, px, vv).unwrap()
    };
    let one_prev = tr
        .arena
        .multiplicity_formula(Multiplicity::One, prev_of_v)?;
    let ds2 = tr.arena.add_decls(vec![dom2]);
    let ax_prev_total = tr.arena.quantified(Quantifier::All, ds2, one_prev);

    // FIRST .* PREFIX = STATE
    let p_rc = tr
        .arena
        .unary_expr(crate::ast::UnaryExprOp::ReflexiveClosure, px)
        .unwrap();
    let reach_all = tr.arena.binary_expr(BinaryOp::Join, fi, p_rc).unwrap();
    let ax_reach = tr.arena.comparison(ExprCompOp::Equals, reach_all, st)?;

    // PREFIX ⊆ STATE × STATE
    let ss = tr.arena.binary_expr(BinaryOp::Product, st, st).unwrap();
    let ax_in = tr.arena.comparison(ExprCompOp::Subset, px, ss)?;

    // LOOP one
    let ax_loop = tr.arena.multiplicity_formula(Multiplicity::One, lp)?;

    // HASLab witness constraints:
    //   all s: STATE | some join(sk,s) && join(sk,s) ⊆ D@s
    let mut witness_parts: Vec<FormulaId> = Vec::new();
    let specs_snapshot = tr.witness_specs.clone();
    for (rel, domain) in &specs_snapshot {
        let sv = tr.arena.variable("$t_ws");
        let sve = tr.arena.expr_variable(sv);
        let st_e = tr.arena.expr_relation(exp.ids.state);
        let dsw = tr.arena.decl(sv, Multiplicity::One, st_e)?;
        let dsw_id = tr.arena.add_decls(vec![dsw]);
        let re = tr.arena.expr_relation(*rel);
        let sk_s = tr.arena.binary_expr(BinaryOp::Join, re, sve).unwrap();
        let some_sk = tr
            .arena
            .multiplicity_formula(Multiplicity::Some, sk_s)
            .unwrap();
        let dom_s = tr.expr(*domain, &T::At(sv))?;
        let re2 = tr.arena.expr_relation(*rel);
        let s2e = tr.arena.expr_variable(sv);
        let sk_s2 = tr.arena.binary_expr(BinaryOp::Join, re2, s2e).unwrap();
        let subset_c = tr.arena.comparison(ExprCompOp::Subset, sk_s2, dom_s)?;
        let conj = tr.arena.and(&[some_sk, subset_c]);
        witness_parts.push(tr.arena.quantified(Quantifier::All, dsw_id, conj));
    }

    let rewritten = tr.formula(formula, true, &T::Init)?;
    let mut all_parts = vec![
        ax_next_total,
        ax_prev_total,
        ax_reach,
        ax_in,
        ax_loop,
        rewritten,
    ];
    all_parts.extend(witness_parts);
    Ok(tr.arena.and(&all_parts))
}

// ---------------------------------------------------------------------------
// Temporal instance extraction
// ---------------------------------------------------------------------------

/// A finite lasso-shaped trace: `states[0..steps]` with the suffix looping
/// back to `loop_state`. Position access beyond the prefix wraps around the
/// cycle.
#[derive(Debug, Clone)]
pub struct TemporalInstance {
    states: Vec<Instance>,
    loop_state: usize,
    unrolls: usize,
}

impl TemporalInstance {
    pub fn states(&self) -> &[Instance] {
        &self.states
    }

    pub fn len(&self) -> usize {
        self.states.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.states.is_empty()
    }

    pub fn loop_state(&self) -> usize {
        self.loop_state
    }

    pub fn unrolls(&self) -> usize {
        self.unrolls
    }

    /// The instance at infinite-trace position `pos` (lasso semantics).
    pub fn state_at(&self, pos: usize) -> &Instance {
        if pos < self.states.len() {
            return &self.states[pos];
        }
        let cycle = self.states.len() - self.loop_state;
        let offset = self.loop_state + ((pos - self.loop_state) % cycle.max(1));
        &self.states[offset.min(self.states.len() - 1)]
    }
}

/// Projects a materialized model over the expanded bounds back into a
/// [`TemporalInstance`] over the original universe.
pub fn extract_temporal_instance(
    inst: &Instance,
    exp: &TemporalExpansion,
) -> Result<TemporalInstance, TemporalError> {
    let width = inst.universe().size() as i64;
    let mut states: Vec<Instance> = (0..exp.steps)
        .map(|_| Instance::new(&exp.orig_universe, &exp.pool))
        .collect();

    for r in inst.relations() {
        let Some(ts) = inst.tuples(r) else { continue };
        if let Some((&orig, _)) = exp.mapping.iter().find(|(_, &e)| e == r) {
            // time-expanded relation: project each state slice back down
            let mut per_state: Vec<TupleSet> = (0..exp.steps)
                .map(|_| TupleSet::new(&exp.orig_universe, ts.arity() - 1))
                .collect::<Result<_, _>>()?;
            for idx in ts.index_view().iter() {
                let col = idx % width;
                let row = idx / width;
                if !(exp.base as i64..(exp.base + exp.steps) as i64).contains(&col) {
                    continue;
                }
                // decode the value coordinates under the EXPANDED base and
                // re-encode them under the original universe size
                let arity = ts.arity() - 1;
                let old_flat = reencode(row, width as usize, exp.orig_universe.size(), arity, 0);
                per_state[(col - exp.base as i64) as usize].insert_index(old_flat);
            }
            for (i, pts) in per_state.into_iter().enumerate() {
                states[i].add(orig, &pts)?;
            }
        } else if r == exp.ids.loop_ {
            let mut chosen: Option<usize> = None;
            for idx in ts.index_view().iter() {
                let k = (idx as usize - exp.base) % exp.steps;
                if chosen.replace(k).is_some_and(|prev| prev != k) {
                    return Err(TemporalError::BadTraceLength);
                }
            }
            let _ = chosen;
        } else if r == exp.ids.prefix
            || r == exp.ids.first
            || r == exp.ids.last
            || r == exp.ids.state
        {
            continue;
        } else {
            // static relation: atom coordinates are preserved by appending
            // time atoms, but flat indices must be recomputed under the
            // ORIGINAL (smaller) base
            let mut out = TupleSet::new(&exp.orig_universe, ts.arity())?;
            for idx in ts.index_view().iter() {
                out.insert_index(reencode(
                    idx,
                    width as usize,
                    exp.orig_universe.size(),
                    ts.arity(),
                    0,
                ));
            }
            for s in &mut states {
                s.add(r, &out)?;
            }
        }
    }

    let loop_ts = inst
        .tuples(exp.ids.loop_)
        .ok_or(TemporalError::UnboundRelation(exp.ids.loop_.0))?;
    let mut loop_state = 0usize;
    for idx in loop_ts.index_view().iter() {
        loop_state = (idx as usize - exp.base) % exp.steps;
    }

    Ok(TemporalInstance {
        states,
        loop_state,
        unrolls: exp.unrolls,
    })
}

// ---------------------------------------------------------------------------
// Bounded lasso evaluation of temporal formulas
// ---------------------------------------------------------------------------

type Env = Vec<(VarId, Vec<u32>)>;

/// Evaluates temporal formulas over a [`TemporalInstance`] using standard
/// lasso semantics: future operators scan at most one full traversal of the
/// trace plus a full cycle (`horizon` positions).
pub struct TemporalEval<'a> {
    pub ti: &'a TemporalInstance,
}

impl<'a> TemporalEval<'a> {
    pub fn new(ti: &'a TemporalInstance) -> TemporalEval<'a> {
        TemporalEval { ti }
    }

    fn horizon(&self) -> usize {
        let steps = self.ti.len();
        let cycle = steps.saturating_sub(self.ti.loop_state()).max(1);
        steps + cycle
    }

    pub fn holds(&self, arena: &AstArena, f: FormulaId) -> Result<bool, EvalError> {
        self.formula_at(arena, f, &Vec::new(), 0)
    }

    pub fn formula_at(
        &self,
        arena: &AstArena,
        f: FormulaId,
        env: &Env,
        pos: usize,
    ) -> Result<bool, EvalError> {
        match arena.formula(f).clone() {
            crate::ast::FormulaNode::TemporalUnary { op, child } => match op {
                TemporalFormulaOp::Always => {
                    for d in 0..self.horizon() {
                        if !self.formula_at(arena, child, env, pos + d)? {
                            return Ok(false);
                        }
                    }
                    Ok(true)
                }
                TemporalFormulaOp::Eventually => {
                    for d in 0..self.horizon() {
                        if self.formula_at(arena, child, env, pos + d)? {
                            return Ok(true);
                        }
                    }
                    Ok(false)
                }
                _ => Err(EvalError::UnboundInteger(-1)),
            },
            crate::ast::FormulaNode::TemporalBinary { op, left, right } => match op {
                TemporalBinaryOp::Until => {
                    // right must be checked before left fails AT the same
                    // position (the witness position itself needs no left)
                    for d in 0..self.horizon() {
                        if self.formula_at(arena, right, env, pos + d)? {
                            return Ok(true);
                        }
                        if !self.formula_at(arena, left, env, pos + d)? {
                            return Ok(false);
                        }
                    }
                    Ok(false)
                }
                TemporalBinaryOp::Releases => {
                    for d in 0..self.horizon() {
                        if self.formula_at(arena, left, env, pos + d)? {
                            return Ok(true);
                        }
                        if !self.formula_at(arena, right, env, pos + d)? {
                            return Ok(false);
                        }
                    }
                    Ok(true)
                }
                _ => Err(EvalError::UnboundInteger(-1)),
            },
            other_node => {
                // non-temporal spine: delegate, threading prime shifts via
                // position-aware expression evaluation
                match other_node {
                    crate::ast::FormulaNode::Constant(v) => Ok(v),
                    crate::ast::FormulaNode::Not(child) => {
                        Ok(!self.formula_at(arena, child, env, pos)?)
                    }
                    crate::ast::FormulaNode::Nary { op, children } => {
                        let vals: Result<Vec<bool>, _> = children
                            .iter()
                            .map(|&c| self.formula_at(arena, c, env, pos))
                            .collect();
                        let vals = vals?;
                        Ok(match op {
                            FormulaBinOp::And => vals.iter().all(|&v| v),
                            FormulaBinOp::Or => vals.iter().any(|&v| v),
                        })
                    }
                    crate::ast::FormulaNode::Comparison { op, left, right } => {
                        let a = self.expr_at(arena, left, env, pos)?;
                        let b = self.expr_at(arena, right, env, pos)?;
                        Ok(match op {
                            ExprCompOp::Equals => a == b,
                            crate::ast::ExprCompOp::Subset => b.covers(&a),
                        })
                    }
                    crate::ast::FormulaNode::IntComparison { op, left, right } => {
                        let l = self.int_at(arena, left, env, pos)?;
                        let r = self.int_at(arena, right, env, pos)?;
                        Ok(match op {
                            IntCompOp::Eq => l == r,
                            IntCompOp::Neq => l != r,
                            IntCompOp::Lt => l < r,
                            IntCompOp::Lte => l <= r,
                            IntCompOp::Gt => l > r,
                            IntCompOp::Gte => l >= r,
                        })
                    }
                    crate::ast::FormulaNode::Quantified { quant, decls, body } => {
                        let decl_list = arena.decls(decls).to_vec();
                        let mut domains = Vec::with_capacity(decl_list.len());
                        let mut vars = Vec::with_capacity(decl_list.len());
                        for d in &decl_list {
                            let m = self.expr_at(arena, d.expr, env, pos)?;
                            domains.push(m);
                            vars.push(d.variable);
                        }
                        let mut results = Vec::new();
                        for b in self.bindings(&domains, &vars, env) {
                            results.push(self.formula_at(arena, body, &b, pos)?);
                        }
                        Ok(match quant {
                            Quantifier::All => results.iter().all(|&v| v),
                            Quantifier::Some => results.iter().any(|&v| v),
                        })
                    }
                    crate::ast::FormulaNode::Multiplicity { mult, expr } => {
                        let m = self.expr_at(arena, expr, env, pos)?;
                        Ok(match mult {
                            Multiplicity::Some => !m.is_empty(),
                            Multiplicity::One => m.len() == 1,
                            Multiplicity::Lone => m.len() <= 1,
                            Multiplicity::Set => true,
                        })
                    }
                    _ => unreachable!("temporal nodes handled above"),
                }
            }
        }
    }

    /// Enumerates all variable bindings over `domains` (product order).
    fn bindings(&self, domains: &[TupleSet], vars: &[VarId], env: &Env) -> Vec<Env> {
        fn rec(
            domains: &[TupleSet],
            vars: &[VarId],
            env: &mut Env,
            out: &mut Vec<Env>,
            depth: usize,
        ) {
            if depth == domains.len() {
                out.push(env.clone());
                return;
            }
            for idx in domains[depth].index_view().iter() {
                let Some(vec) = domains[depth].dims_vector(idx as usize) else {
                    continue;
                };
                env.push((vars[depth], vec));
                rec(domains, vars, env, out, depth + 1);
                env.pop();
            }
        }
        let mut env2 = env.to_vec();
        let mut out = Vec::new();
        rec(domains, vars, &mut env2, &mut out, 0);
        out
    }

    /// Expression evaluation with prime support: `pos` advances along the
    /// prime spine; leaves are read from the state instance at the current
    /// position, all other combinators mirror [`Evaluator::expr_set`].
    pub fn expr_at(
        &self,
        arena: &AstArena,
        e: ExprId,
        env: &Env,
        pos: usize,
    ) -> Result<TupleSet, EvalError> {
        match arena.expr(e).clone() {
            crate::ast::ExprNode::Temporal {
                op: TemporalExprOp::Prime,
                child,
            } => self.expr_at(arena, child, env, pos + 1),
            crate::ast::ExprNode::Relation(_)
            | crate::ast::ExprNode::Variable(_)
            | crate::ast::ExprNode::Constant(_)
            | crate::ast::ExprNode::FromInt(_) => {
                let ev = Evaluator::new(self.ti.state_at(pos));
                ev.expr_set(arena, e, env)
            }
            crate::ast::ExprNode::Unary { op, child } => {
                let m = self.expr_at(arena, child, env, pos)?;
                match op {
                    crate::ast::UnaryExprOp::Transpose => transpose(&m),
                    crate::ast::UnaryExprOp::Closure => closure(&m, false),
                    crate::ast::UnaryExprOp::ReflexiveClosure => closure(&m, true),
                }
            }
            crate::ast::ExprNode::Binary { op, left, right } => {
                let a = self.expr_at(arena, left, env, pos)?;
                let b = self.expr_at(arena, right, env, pos)?;
                match op {
                    BinaryOp::Union => union(&a, &b),
                    BinaryOp::Intersection => intersection(&a, &b),
                    BinaryOp::Difference => difference(&a, &b),
                    BinaryOp::Override => override_sets(&a, &b),
                    BinaryOp::Product => cross(&a, &b),
                    BinaryOp::Join => join(&a, &b),
                }
            }
            crate::ast::ExprNode::Nary { op, children } => {
                let mut acc = self.expr_at(arena, children[0], env, pos)?;
                for &c in &children[1..] {
                    let m = self.expr_at(arena, c, env, pos)?;
                    acc = match op {
                        BinaryOp::Union => union(&acc, &m)?,
                        BinaryOp::Intersection => intersection(&acc, &m)?,
                        BinaryOp::Difference => difference(&acc, &m)?,
                        BinaryOp::Override => override_sets(&acc, &m)?,
                        BinaryOp::Product => cross(&acc, &m)?,
                        BinaryOp::Join => join(&acc, &m)?,
                    };
                }
                Ok(acc)
            }
            crate::ast::ExprNode::If { cond, then, els } => {
                let c = self.formula_at(arena, cond, env, pos)?;
                if c {
                    self.expr_at(arena, then, env, pos)
                } else {
                    self.expr_at(arena, els, env, pos)
                }
            }
            crate::ast::ExprNode::Comprehension { decls, body } => {
                let decl_list = arena.decls(decls).to_vec();
                let mut domains = Vec::with_capacity(decl_list.len());
                let mut vars = Vec::with_capacity(decl_list.len());
                for d in &decl_list {
                    let m = self.expr_at(arena, d.expr, env, pos)?;
                    domains.push(m);
                    vars.push(d.variable);
                }
                let mut collected: BTreeSet<Vec<u32>> = BTreeSet::new();
                for binding in self.bindings(&domains, &vars, env) {
                    if self.formula_at(arena, body, &binding, pos)? {
                        let vec: Vec<u32> = binding
                            .iter()
                            .flat_map(|(_, v)| v.iter().copied())
                            .collect();
                        collected.insert(vec);
                    }
                }
                let arity = collected.iter().next().map(|v| v.len()).unwrap_or_else(|| {
                    decl_list
                        .iter()
                        .map(|d| arena.variable_arity(d.variable) as usize)
                        .sum()
                });
                let n = self.ti.len();
                let _ = n;
                let uni = self.ti.states()[0].universe().clone();
                let mut out =
                    TupleSet::new(&uni, arity as u32).map_err(|_| EvalError::UnboundVariable)?;
                let dims = crate::dimensions::Dimensions::square(uni.size() as u32, arity as u32)
                    .map_err(|_| EvalError::UnboundVariable)?;
                for vec in collected {
                    if let Some(flat) = dims.flat_of(&vec) {
                        out.insert_index(flat as i64);
                    }
                }
                Ok(out)
            }
            crate::ast::ExprNode::Project { .. } => Err(EvalError::UnboundInteger(-2)),
        }
    }

    pub fn int_at(
        &self,
        arena: &AstArena,
        i: IntId,
        env: &Env,
        pos: usize,
    ) -> Result<i64, EvalError> {
        // primes cannot appear under int expressions except via OfExpr; the
        // plain evaluator on the shifted state handles those
        let ev = Evaluator::new(self.ti.state_at(pos));
        ev.int_value(arena, i, env)
    }
}
