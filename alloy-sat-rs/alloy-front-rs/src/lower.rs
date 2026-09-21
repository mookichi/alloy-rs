//! Lowers the frontend AST to kodkod-rs (AstArena + Bounds) and solves.

use crate::ast::*;
use crate::bounds::{self, Resolved};
use crate::types::{SetKind, INT_MISMATCH_MSG};
use crate::FrontError;
use alloy_kodkod_rs::ast::{
    self as kk, CastToIntOp, ExprCompOp, ExprId, FormulaId, IntId, Multiplicity, Quantifier,
};
use alloy_kodkod_rs::bounds::Bounds;
use alloy_kodkod_rs::mepk::decimal_to_mepk;
use alloy_kodkod_rs::opt::OptSense;
use alloy_kodkod_rs::relation::{RelationId, RelationPool};
use std::collections::HashMap;
use std::sync::Arc;

pub struct LoweredProblem {
    pub arena: kk::AstArena,
    pub bounds: Bounds,
    pub formula: FormulaId,
    pub bitwidth: u32,
    /// Some for `maximize`/`minimize` commands.
    pub objective: Option<LoweredOpt>,
    /// In-body `maximize`/`minimize` markers (`Formula::Maximize` /
    /// `Formula::Minimize`) in lowering order. Empty for the plain
    /// `maximize:` / `minimize:` command forms, which set `objective`.
    pub markers: Vec<OptMarker>,
    /// True when the lowered formula contains AlloyMax soft nodes
    /// (`maxsome` / `minsome` / `soft fact`). Such problems must run
    /// through the optimizer, never the plain SAT path.
    pub has_softs: bool,
    /// `some`/`no Overflow` marker at the top level of the command body
    /// (`None` when absent; the marker is consumed, `formula` is the
    /// inner body). Nested markers are rejected during lowering.
    pub overflow: Option<OverflowMode>,
}

/// Trace state an in-body optimization marker is evaluated at, taken
/// from the innermost enclosing state-pinning temporal operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TimePoint {
    /// `initially` — the first state.
    First,
    /// `goal` — the last state.
    Last,
    /// `restore` — the loop state.
    Loop,
}

/// One in-body `maximize`/`minimize` marker: lowered integer target,
/// sense, and enclosing trace state (`None` outside temporal contexts —
/// rejected for temporal commands, which need a state).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OptMarker {
    pub target: IntId,
    pub sense: OptSense,
    pub time: Option<TimePoint>,
}

/// Lowered optimization target of a `maximize`/`minimize` command.
#[derive(Debug, Clone)]
pub struct LoweredOpt {
    pub sense: OptSense,
    pub target: LoweredTarget,
}

/// Lowered optimization target: an integer expression id or resolved
/// relation weights.
#[derive(Debug, Clone)]
pub enum LoweredTarget {
    Int(IntId),
    Weighted(HashMap<RelationId, i64>),
}

pub struct Lowerer<'m> {
    module: &'m Module,
}

type LResult<T> = Result<T, FrontError>;

/// A resolved name binding: (kodkod expr, arity, abstract flavor).
type BindEntry = (ExprId, u32, SetKind);

/// Variable environment: name -> (kodkod var, arity, abstract flavor).
type Env = Vec<(String, kk::VarId, u32, SetKind)>;

impl<'m> Lowerer<'m> {
    pub fn new(module: &'m Module) -> Lowerer<'m> {
        Lowerer { module }
    }

    fn unsup<T>(&self, what: impl Into<String>) -> LResult<T> {
        Err(FrontError::Unsupported(what.into()))
    }

    pub fn prepare_command(&mut self, index: usize) -> LResult<LoweredProblem> {
        let cmd = self
            .module
            .commands
            .get(index)
            .ok_or_else(|| FrontError::Resolve(format!("no command #{index}")))?;
        // Clone up front: the setup closure below borrows `self` mutably.
        let scope = cmd.scope.clone();
        let kind = cmd.kind.clone();
        let opt_spec = match &kind {
            CommandKind::Maximize { objective, .. } | CommandKind::Minimize { objective, .. } => {
                Some(objective.clone())
            }
            CommandKind::Run(_) | CommandKind::Check(_) => None,
        };
        let opt_sense = match &kind {
            CommandKind::Maximize { .. } => Some(OptSense::Maximize),
            CommandKind::Minimize { .. } => Some(OptSense::Minimize),
            CommandKind::Run(_) | CommandKind::Check(_) => None,
        };
        // Soft-bearing commands must run through the optimizer: a
        // `maximize`/`minimize` command, a `soft fact`, or a `maxsome` /
        // `minsome` node anywhere in the facts or command body.
        let body_soft = match &kind {
            CommandKind::Run(None)
            | CommandKind::Check(None)
            | CommandKind::Maximize { name: None, .. }
            | CommandKind::Minimize { name: None, .. } => false,
            CommandKind::Run(Some(name))
            | CommandKind::Check(Some(name))
            | CommandKind::Maximize {
                name: Some(name), ..
            }
            | CommandKind::Minimize {
                name: Some(name), ..
            } => self
                .module
                .paras
                .iter()
                .find(|p| &p.name == name)
                .map(|p| p.body.has_soft())
                .unwrap_or(false),
        };
        let has_softs = !self.module.soft_facts.is_empty()
            || self.module.facts.iter().any(|(_, f)| f.has_soft())
            || self
                .module
                .sigs
                .iter()
                .filter_map(|sd| sd.fact.as_ref())
                .any(|f| f.has_soft())
            || body_soft;
        let (arena, bounds, bitwidth, markers, (formula, objective, overflow)) =
            self.with_setup(&scope, |ctx, arena, _bounds, mut parts| {
                // global facts
                for (_, f) in &ctx.module.facts {
                    parts.push(ctx.lower_formula(arena, f, &mut Vec::new())?);
                }
                // sig facts: all this: S | fact
                for sd in &ctx.module.sigs {
                    if let Some(f) = &sd.fact {
                        for owner in &sd.names {
                            let fid = ctx.lower_sig_fact(arena, f, owner)?;
                            parts.push(fid);
                        }
                    }
                }
                // sig `in` constraints: sig A in B  =>  A in B (subset).
                // A builtin `Int`/`Signed` parent needs no formula: the child's
                // upper bound is already exactly the int atoms (the solver's
                // integer layer cannot take an Ints constant in a formula).
                for sd in &ctx.module.sigs {
                    if sd.rel == crate::ast::SigRel::In {
                        if let Some(parent_name) = &sd.extends {
                            if parent_name == "Int" || parent_name == "Signed" {
                                continue;
                            }
                            for child_name in &sd.names {
                                let child_rel = ctx.lookup_rel(child_name).ok_or_else(|| {
                                    FrontError::Resolve(format!("unknown sig '{child_name}'"))
                                })?;
                                let parent_rel = ctx.lookup_rel(parent_name).ok_or_else(|| {
                                    FrontError::Resolve(format!("unknown sig '{parent_name}'"))
                                })?;
                                let ce = arena.expr_relation(child_rel);
                                let pe = arena.expr_relation(parent_rel);
                                // A in B  <=>  no (A - B)
                                let diff = arena
                                    .binary_expr(kk::BinaryOp::Difference, ce, pe)
                                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                                let some_diff = arena
                                    .multiplicity_formula(Multiplicity::Some, diff)
                                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                                parts.push(arena.not(some_diff));
                            }
                        }
                    }
                }
                // AlloyMax `soft fact`s: lowered and wrapped as soft
                // formulas (optimized, not asserted).
                for (_, f) in &ctx.module.soft_facts {
                    let bf = ctx.lower_formula(arena, f, &mut Vec::new())?;
                    parts.push(arena.soft_fact(bf));
                }
                // command body
                let (body_name, negate) = match &kind {
                    CommandKind::Run(n) => (n.clone(), false),
                    CommandKind::Check(n) => (n.clone(), true),
                    CommandKind::Maximize { name, .. } | CommandKind::Minimize { name, .. } => {
                        (name.clone(), false)
                    }
                };
                // `some/no Overflow` marker at the top level of the body
                // (`None` when absent).
                let mut overflow: Option<OverflowMode> = None;
                match body_name {
                    None => parts.push(arena.bool_formula(true)),
                    Some(name) => {
                        let para = ctx
                            .module
                            .paras
                            .iter()
                            .find(|p| p.name == name)
                            .ok_or_else(|| {
                                FrontError::Resolve(format!("command references unknown '{name}'"))
                            })?;
                        if !para.params.is_empty() {
                            return Err(FrontError::Unsupported(format!(
                                "parametrized '{name}' in command"
                            )));
                        }
                        // Top-level `some/no Overflow` marker: consume it
                        // here (the inner body is lowered normally);
                        // nested markers are rejected in `lower_formula`.
                        // `some Overflow` seeks an overflowing model, which
                        // `check` (counterexample search) does not support.
                        let (body, mode) = match &para.body {
                            Formula::OverflowCond(mode, inner) => {
                                if negate && *mode == OverflowMode::Some {
                                    return Err(FrontError::Resolve(
                                        "`some Overflow` is only allowed in `run` bodies, not `check`".to_string(),
                                    ));
                                }
                                (inner.as_ref(), Some(*mode))
                            }
                            body => (body, None),
                        };
                        overflow = mode;
                        let bf = ctx.lower_formula(arena, body, &mut Vec::new())?;
                        // `check F` searches for a counterexample to F
                        if negate {
                            parts.push(arena.not(bf));
                        } else {
                            parts.push(bf);
                        }
                    }
                }
                let formula = arena.and(&parts);
                // Java Simplifier port: shrink uppers (grow lowers) from
                // top-level `in`/`=` facts before translation. Applies to
                // run/check/opt alike (and hence REPL Cnfs built from them).
                let mut formula = formula;
                if alloy_kodkod_rs::simplify::simplify_bounds(arena, _bounds, formula)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?
                    == alloy_kodkod_rs::simplify::SimplifyOutcome::Unsat
                {
                    formula = arena.false_formula();
                }
                // Optimization target (maximize/minimize only).
                let objective = match (opt_sense, opt_spec) {
                    (Some(sense), Some(spec)) => {
                        let target = match spec {
                            OptSpec::Int(ie) => {
                                LoweredTarget::Int(ctx.lower_int(arena, &ie, &mut Vec::new())?)
                            }
                            OptSpec::Weights(pairs) => {
                                let mut weights = HashMap::new();
                                for (name, w) in pairs {
                                    let r = ctx.lookup_rel(&name).ok_or_else(|| {
                                        FrontError::Resolve(format!(
                                            "unknown relation '{name}' in weights"
                                        ))
                                    })?;
                                    weights.insert(r, w);
                                }
                                LoweredTarget::Weighted(weights)
                            }
                        };
                        Some(LoweredOpt { sense, target })
                    }
                    (None, None) => None,
                    _ => unreachable!("sense and spec move together"),
                };
                Ok((formula, objective, overflow))
            })?;
        // `check` negates its body while a marker is hard `true`: the
        // negation would be unsatisfiable, so reject loudly.
        if matches!(kind, CommandKind::Check(_)) && !markers.is_empty() {
            return Err(FrontError::Resolve(
                "`check` negates its body, so a `maximize`/`minimize` marker in it would be \
                 unsatisfiable; write the objective on a `run` command instead"
                    .into(),
            ));
        }
        // A command-level objective (`maximize:` / `minimize:`) and
        // in-body markers are two ways to write the same thing; mixing
        // them would silently drop one of the two targets.
        if objective.is_some() && !markers.is_empty() {
            return Err(FrontError::Resolve(
                "command has both a `maximize`/`minimize` command objective and an \
                 in-body `maximize`/`minimize` marker (keep one; markers are \
                 written as `maximize <intexpr>` inside the body)"
                    .into(),
            ));
        }
        Ok(LoweredProblem {
            arena,
            bounds,
            formula,
            bitwidth,
            objective,
            markers,
            has_softs,
            overflow,
        })
    }

    /// Lower a bare expression reusing a caller-provided arena (REPL `:query`).
    ///
    /// Relation names are re-interned into `arena`, so IDs line up with any
    /// instance built from the same pool (e.g. `Cnf.arena`). A fresh scope
    /// resolution supplies only typing info; no bounds are (re)built here.
    /// Pass `cnf.arena` (cloned) together with the instance solved from it.
    pub fn lower_expr_in_scope(
        &mut self,
        scope: &Scope,
        arena: &mut kk::AstArena,
        e: &Expr,
    ) -> LResult<(kk::ExprId, u32)> {
        self.with_query_ctx(scope, arena, |ctx, arena| {
            ctx.lower_expr(arena, e, &mut Vec::new())
        })
    }

    /// Lower a bare integer expression reusing a caller-provided arena
    /// (REPL `:query`, e.g. `#A`). Same setup/contract as
    /// [`Self::lower_expr_in_scope`].
    pub fn lower_int_in_scope(
        &mut self,
        scope: &Scope,
        arena: &mut kk::AstArena,
        ie: &IntExpr,
    ) -> LResult<kk::IntId> {
        self.with_query_ctx(scope, arena, |ctx, arena| {
            ctx.lower_int(arena, ie, &mut Vec::new())
        })
    }

    /// Lower a bare formula reusing a caller-provided arena (REPL `:query`
    /// of closed formulas such as `1 = 1`). Same setup/contract as
    /// [`Self::lower_expr_in_scope`].
    pub fn lower_formula_in_scope(
        &mut self,
        scope: &Scope,
        arena: &mut kk::AstArena,
        f: &Formula,
    ) -> LResult<kk::FormulaId> {
        self.with_query_ctx(scope, arena, |ctx, arena| {
            ctx.lower_formula(arena, f, &mut Vec::new())
        })
    }

    /// Shared query-time setup: resolve the scope, re-intern relation names
    /// into the caller-provided arena, and run `f` with the lowering
    /// context. Typing info only; no bounds are (re)built here.
    fn with_query_ctx<R>(
        &mut self,
        scope: &Scope,
        arena: &mut kk::AstArena,
        f: impl FnOnce(&Ctx<'_>, &mut kk::AstArena) -> LResult<R>,
    ) -> LResult<R> {
        let res = bounds::resolve(self.module, scope).map_err(FrontError::Resolve)?;
        // Re-intern only: names already present keep their IDs.
        let mut rels: HashMap<String, RelationId> = HashMap::new();
        for name in res.sigs.keys() {
            let r = arena.relation(name, 1);
            rels.insert(name.clone(), r);
        }
        let mut field_arity: HashMap<String, u32> = HashMap::new();
        // Builtin `EReal` field lanes (binary `EReal -> lane-atoms`).
        for (fname, _) in crate::bounds::EREAL_LANES {
            let key = format!("EReal.{fname}");
            let fa = arena.relation(&key, 2);
            field_arity.insert(key.clone(), 2);
            rels.insert(key, fa);
        }
        for sd in &self.module.sigs {
            for owner in &sd.names {
                for d in &sd.fields {
                    for fname in &d.names {
                        let key = format!("{owner}.{fname}");
                        let ta = self.type_arity(&d.expr, &res)?;
                        let fa = arena.relation(&key, 1 + ta);
                        field_arity.insert(key.clone(), 1 + ta);
                        rels.insert(key, fa);
                    }
                }
            }
        }
        let mut ordering_info: HashMap<String, (RelationId, RelationId)> = HashMap::new();
        for open in &self.module.opens {
            if open.path != "util/ordering" || open.params.is_empty() {
                continue;
            }
            let first_rel = arena.relation(&format!("${}_first", open.alias), 1);
            let next_rel = arena.relation(&format!("${}_next", open.alias), 2);
            ordering_info.insert(open.alias.clone(), (first_rel, next_rel));
        }
        let mut open_params: HashMap<String, Vec<String>> = HashMap::new();
        for open in &self.module.opens {
            let params: Vec<String> = open
                .params
                .iter()
                .map(|p| match p {
                    OpenParam::Exactly(n) | OpenParam::Set(n) => n.clone(),
                })
                .collect();
            if !params.is_empty() {
                open_params.insert(open.alias.clone(), params);
            }
        }
        let mut field_int: HashMap<String, SetKind> = HashMap::new();
        for sd in &self.module.sigs {
            for owner in &sd.names {
                for d in &sd.fields {
                    for fname in &d.names {
                        field_int.insert(
                            format!("{owner}.{fname}"),
                            SetKind::from_bool(mentions_int_expr(&d.expr)),
                        );
                    }
                }
            }
        }
        // Builtin `EReal` lanes are always Int-flavored (bitmask-readable).
        for (fname, _) in crate::bounds::EREAL_LANES {
            field_int.insert(format!("EReal.{fname}"), SetKind::Int);
        }
        let ctx = Ctx {
            module: self.module,
            res: &res,
            rels: &rels,
            field_arity: &field_arity,
            field_int,
            ordering_info: &ordering_info,
            depth: std::cell::Cell::new(0),
            open_params,
            expr_binds: std::cell::RefCell::new(HashMap::new()),
            let_binds: std::cell::RefCell::new(Vec::new()),
            // Query-only: atom references resolve against the solved Cnf's
            // universe (Java's solve-after `frame.a2k` equivalent).
            allow_atoms: true,
            pin_seq: std::cell::Cell::new(0),
            markers: std::cell::RefCell::new(Vec::new()),
            marker_time: std::cell::Cell::new(None),
        };
        f(&ctx, arena)
    }

    /// Shared bounds/arena setup for one scope; runs `f` with the lowering
    /// context and returns the owned arena/bounds plus `f`'s result.
    fn with_setup<R>(
        &mut self,
        scope: &Scope,
        f: impl FnOnce(&Ctx<'_>, &mut kk::AstArena, &mut Bounds, Vec<FormulaId>) -> LResult<R>,
    ) -> LResult<(kk::AstArena, Bounds, u32, Vec<OptMarker>, R)> {
        let res = bounds::resolve(self.module, scope).map_err(FrontError::Resolve)?;
        let pool = Arc::new(RelationPool::new());
        let mut arena = kk::AstArena::with_pool(Arc::clone(&pool));
        let mut b = Bounds::new(&res.universe, &pool);

        // sig relations + exact bounds
        let mut rels: HashMap<String, RelationId> = HashMap::new();
        for name in res.sigs.keys() {
            let r = arena.relation(name, 1);
            rels.insert(name.clone(), r);
        }
        // mark var sig relations as variable (atoms may change between states)
        for sd in &self.module.sigs {
            if sd.is_var {
                for name in &sd.names {
                    if let Some(&r) = rels.get(name.as_str()) {
                        arena.set_variable(r, true);
                    }
                }
            }
        }
        // field relations (per owning sig name)
        let mut field_arity: HashMap<String, u32> = HashMap::new();
        for sd in &self.module.sigs {
            for owner in &sd.names {
                for d in &sd.fields {
                    for fname in &d.names {
                        let key = format!("{owner}.{fname}");
                        let ta = self.type_arity(&d.expr, &res)?;
                        let fa = arena.relation(&key, 1 + ta);
                        field_arity.insert(key.clone(), 1 + ta);
                        // upper bound: owner atoms x type tuples
                        let owner_atoms = res.atoms_of(owner);
                        let tuples = self.type_tuples(&d.expr, &res)?;
                        let mut ts =
                            alloy_kodkod_rs::tupleset::TupleSet::new(&res.universe, 1 + ta)
                                .map_err(|e| FrontError::Resolve(e.to_string()))?;
                        for o in &owner_atoms {
                            for t in &tuples {
                                let mut atoms = vec![o.clone()];
                                atoms.extend(t.iter().cloned());
                                let tup =
                                    bounds::tuple_of(&res, &atoms).map_err(FrontError::Resolve)?;
                                ts.insert(&tup)
                                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                            }
                        }
                        let lo = alloy_kodkod_rs::tupleset::TupleSet::new(&res.universe, 1 + ta)
                            .map_err(|e| FrontError::Resolve(e.to_string()))?;
                        if d.is_var {
                            arena.set_variable(fa, true);
                        }
                        b.bound(fa, &lo, &ts)
                            .map_err(|e| FrontError::Resolve(e.to_string()))?;
                        rels.insert(key.clone(), fa);
                    }
                }
            }
        }
        // ------------------------------------------------------------------
        // Builtin `EReal` lane relations (`EReal.m` etc., binary over the
        // dedicated lane atoms). Allocated lazily with the lane atoms.
        for (fname, group) in crate::bounds::EREAL_LANES {
            let key = format!("EReal.{fname}");
            let fa = arena.relation(&key, 2);
            field_arity.insert(key.clone(), 2);
            let lane = res.lane_atoms.get(&group).cloned().unwrap_or_default();
            let mut ts =
                alloy_kodkod_rs::tupleset::TupleSet::new(&res.universe, 2)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
            for o in &res.ereal_atoms {
                for t in &lane {
                    let tup = bounds::tuple_of(&res, &[o.clone(), t.clone()])
                        .map_err(FrontError::Resolve)?;
                    ts.insert(&tup)
                        .map_err(|e| FrontError::Resolve(e.to_string()))?;
                }
            }
            let lo = alloy_kodkod_rs::tupleset::TupleSet::new(&res.universe, 2)
                .map_err(|e| FrontError::Resolve(e.to_string()))?;
            b.bound(fa, &lo, &ts)
                .map_err(|e| FrontError::Resolve(e.to_string()))?;
            rels.insert(key, fa);
        }
        // `totalOrder[S, S.next]`: pin the binary field relation
        // (i.e. `S<:next`) to the canonical chain
        // over the sig's atoms (Java `pred/totalOrder` symmetry breaking,
        // aggressive mode). Runs before sig binding so the exact bound
        // below replaces the generic upper bound.
        // ------------------------------------------------------------------
        for (sig_name, field_name) in collect_total_order_pins(self.module) {
            let key = format!("{sig_name}.{field_name}");
            let Some(&fr) = rels.get(&key) else {
                return Err(FrontError::Resolve(format!(
                    "totalOrder: unknown field '{key}'"
                )));
            };
            let atoms = res.atoms_of(&sig_name);
            if !res.sigs.contains_key(&sig_name) {
                return Err(FrontError::Resolve(format!(
                    "totalOrder: unknown sig '{sig_name}'"
                )));
            }
            let fa = field_arity.get(&key).copied().unwrap_or(2);
            if fa != 2 {
                return Err(FrontError::Resolve(format!(
                    "totalOrder: field '{key}' must be binary (got arity {fa})"
                )));
            }
            let mut chain =
                alloy_kodkod_rs::tupleset::TupleSet::new(&res.universe, 2)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
            for w in atoms.windows(2) {
                let t = bounds::tuple_of(&res, &[w[0].clone(), w[1].clone()])
                    .map_err(FrontError::Resolve)?;
                chain
                    .insert(&t)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
            }
            b.bound_exactly(fr, &chain)
                .map_err(|e| FrontError::Resolve(e.to_string()))?;
        }
        // bind sig bounds AFTER field bounds so pool interning is consistent
        bounds::bind_sigs(self.module, &res, &pool, &mut arena, &mut b, scope)
            .map_err(FrontError::Resolve)?;

        // ------------------------------------------------------------------
        // Native ordering expansion: pin fresh relations to a fixed total
        // order for `open util/ordering[T] as ord`.
        // ------------------------------------------------------------------
        let mut ordering_info: HashMap<String, (RelationId, RelationId)> = HashMap::new();
        for open in &self.module.opens {
            if open.path != "util/ordering" || open.params.is_empty() {
                continue;
            }
            let sig_name = match &open.params[0] {
                OpenParam::Exactly(n) | OpenParam::Set(n) => n.clone(),
            };
            let atoms = res.atoms_of(&sig_name);
            let alias = &open.alias;

            // $alias_first: unary relation = {a0} (the first atom)
            let first_rel = arena.relation(&format!("${alias}_first"), 1);
            let mut first_ts = alloy_kodkod_rs::tupleset::TupleSet::new(&res.universe, 1)
                .map_err(|e| FrontError::Resolve(e.to_string()))?;
            if let Some(a0) = atoms.first() {
                let t = bounds::tuple_of(&res, std::slice::from_ref(a0))
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                first_ts
                    .insert(&t)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
            }
            arena.set_variable(first_rel, true);
            b.bound_exactly(first_rel, &first_ts)
                .map_err(|e| FrontError::Resolve(e.to_string()))?;

            // $alias_next: binary relation = {(a0,a1), (a1,a2), ..., (a_{n-2},a_{n-1})}
            let next_rel = arena.relation(&format!("${alias}_next"), 2);
            let mut next_ts = alloy_kodkod_rs::tupleset::TupleSet::new(&res.universe, 2)
                .map_err(|e| FrontError::Resolve(e.to_string()))?;
            for w in atoms.windows(2) {
                let t = bounds::tuple_of(&res, &[w[0].clone(), w[1].clone()])
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                next_ts
                    .insert(&t)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
            }
            arena.set_variable(next_rel, true);
            b.bound_exactly(next_rel, &next_ts)
                .map_err(|e| FrontError::Resolve(e.to_string()))?;

            ordering_info.insert(alias.clone(), (first_rel, next_rel));
        }

        // int atom exact bounds (lazy: skipped entirely when the module
        // never mentions Int as a set, so Int-free models carry no int
        // atoms in either the universe or the bounds). Bit-vector model:
        // W atoms `{0, .., W-1}`.
        if crate::ast::module_needs_int_atoms(self.module, scope) {
            for v in 0..res.int_count {
                let name = v.to_string();
                let idx = res
                    .universe
                    .index(&name)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let mut ts = alloy_kodkod_rs::tupleset::TupleSet::new(&res.universe, 1)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                ts.insert_index(idx as i64);
                b.bound_exactly_int(v.into(), &ts)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
            }
        }

        // EReal bit-lane exact bounds (lazy like Int): value `v` is the
        // bit position, read with signed-MSB weight via `BitsIn(group)`.
        for (fname, group) in crate::bounds::EREAL_LANES {
            let lane = res.lane_atoms.get(&group).cloned().unwrap_or_default();
            for (v, name) in lane.iter().enumerate() {
                let idx = res
                    .universe
                    .index(name)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let mut ts = alloy_kodkod_rs::tupleset::TupleSet::new(&res.universe, 1)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                ts.insert_index(idx as i64);
                b.bound_exactly_int_in(group, v as i64, &ts)
                    .map_err(|e| FrontError::Resolve(format!("EReal.{fname}: {e}")))?;
            }
        }

        // Insert ordering relations into rels so name resolution can find them
        for (alias, &(first_rel, next_rel)) in &ordering_info {
            rels.insert(format!("{alias}/first"), first_rel);
            rels.insert(format!("{alias}/next"), next_rel);
        }

        // Build open_params: alias -> parameter type names
        let mut open_params: HashMap<String, Vec<String>> = HashMap::new();
        for open in &self.module.opens {
            let params: Vec<String> = open
                .params
                .iter()
                .map(|p| match p {
                    OpenParam::Exactly(n) | OpenParam::Set(n) => n.clone(),
                })
                .collect();
            if !params.is_empty() {
                open_params.insert(open.alias.clone(), params);
            }
        }

        let mut field_int: HashMap<String, SetKind> = HashMap::new();
        for sd in &self.module.sigs {
            for owner in &sd.names {
                for d in &sd.fields {
                    for fname in &d.names {
                        field_int.insert(
                            format!("{owner}.{fname}"),
                            SetKind::from_bool(mentions_int_expr(&d.expr)),
                        );
                    }
                }
            }
        }
        // Builtin `EReal` lanes are always Int-flavored (bitmask-readable).
        for (fname, _) in crate::bounds::EREAL_LANES {
            field_int.insert(format!("EReal.{fname}"), SetKind::Int);
        }
        let ctx = Ctx {
            module: self.module,
            res: &res,
            rels: &rels,
            field_arity: &field_arity,
            field_int,
            ordering_info: &ordering_info,
            depth: std::cell::Cell::new(0),
            open_params,
            expr_binds: std::cell::RefCell::new(HashMap::new()),
            let_binds: std::cell::RefCell::new(Vec::new()),
            // Model builds never resolve atom names (Java parity: atoms
            // are solver outputs, not language terms).
            allow_atoms: false,
            pin_seq: std::cell::Cell::new(0),
            markers: std::cell::RefCell::new(Vec::new()),
            marker_time: std::cell::Cell::new(None),
        };

        // Field-level formulas, now that `ctx` exists: per-field typing
        // (`f in Owner -> Type`, no dangling tuples) and multiplicity
        // constraints over dynamic (instance-level) quantifier domains.
        let field_formulas = self.field_constraints(&ctx, &mut arena, &mut b)?;

        let out = f(&ctx, &mut arena, &mut b, field_formulas)?;
        let markers = ctx.markers.take();
        Ok((arena, b, res.bitwidth, markers, out))
    }

    /// Per-field formulas for every declared field: typing (`f` stays inside
    /// the current `Owner -> Type` extent) plus multiplicity constraints.
    /// `field_parts` ordering: typing first, then multiplicity.
    fn field_constraints(
        &self,
        ctx: &Ctx,
        arena: &mut kk::AstArena,
        b: &mut Bounds,
    ) -> LResult<Vec<FormulaId>> {
        let mut out = Vec::new();
        for sd in &self.module.sigs {
            for owner in &sd.names {
                for d in &sd.fields {
                    for fname in &d.names {
                        let key = format!("{owner}.{fname}");
                        if let Some(t) = self.field_typing(ctx, arena, owner, &key, d)? {
                            out.push(t);
                        }
                        let tuples = self.type_tuples(&d.expr, ctx.res)?;
                        let frel = ctx
                            .lookup_rel(&key)
                            .ok_or_else(|| FrontError::Resolve(format!("unknown field '{key}'")))?;
                        if let Some(c) =
                            field_mult_constraint(ctx, arena, b, frel, d, owner, &tuples)?
                        {
                            out.push(c);
                        }
                    }
                }
            }
        }
        Ok(out)
    }

    /// Typing constraint `f in Owner -> Type` over instance-level extents.
    ///
    /// Without it the solver may fill `f` with atoms outside the sig
    /// extents (dangling tuples). Integer-typed fields (which the formula
    /// layer cannot evaluate) keep bounds-only behavior.
    fn field_typing(
        &self,
        ctx: &Ctx,
        arena: &mut kk::AstArena,
        owner: &str,
        key: &str,
        d: &Decl,
    ) -> LResult<Option<FormulaId>> {
        if mentions_int_expr(&d.expr) {
            return Ok(None);
        }
        let frel = match ctx.lookup_rel(key) {
            Some(r) => r,
            None => return Ok(None),
        };
        let owner_rel = match ctx.lookup_rel(owner) {
            Some(r) => r,
            None => return Ok(None),
        };
        let stripped = strip_mult(&d.expr);
        let (type_e, _) = match ctx.lower_expr(arena, &stripped, &mut Vec::new()) {
            Ok(v) => v,
            Err(_) => return Ok(None),
        };
        let owner_e = arena.expr_relation(owner_rel);
        let prod = match arena.binary_expr(kk::BinaryOp::Product, owner_e, type_e) {
            Ok(p) => p,
            Err(_) => return Ok(None),
        };
        let f_e = arena.expr_relation(frel);
        match arena.comparison(ExprCompOp::Subset, f_e, prod) {
            Ok(s) => Ok(Some(s)),
            Err(_) => Ok(None),
        }
    }

    fn type_arity(&self, e: &Expr, res: &Resolved) -> LResult<u32> {
        Ok(match e {
            Expr::ArrowMult(_, inner) | Expr::LeadMult(_, inner) => self.type_arity(inner, res)?,
            Expr::Bin(BinOp::Product, a, b) => {
                self.type_arity(a, res)? + self.type_arity(b, res)?
            }
            Expr::Bin(BinOp::Join, a, b) => {
                let (x, y) = (self.type_arity(a, res)?, self.type_arity(b, res)?);
                x + y - 2
            }
            Expr::Bin(_, a, _) => self.type_arity(a, res)?,
            Expr::Name(n, pos) => {
                if res.sigs.contains_key(n)
                    || n == "univ"
                    || n == "int"
                    || n == "Int"
                    || n == "Signed"
                {
                    1
                } else {
                    return Err(FrontError::Parse {
                        pos: *pos,
                        msg: format!("'{n}' is not a type in field declaration"),
                    });
                }
            }
            Expr::Univ | Expr::None_ | Expr::IntAtom => 1,
            other => {
                let _ = other;
                return self.unsup("complex expression in field declaration");
            }
        })
    }

    /// Atom-tuples denoted by a field TYPE expression (upper bound content).
    fn type_tuples(&self, e: &Expr, res: &Resolved) -> LResult<Vec<Vec<String>>> {
        match e {
            Expr::LeadMult(_, inner) | Expr::ArrowMult(_, inner) => self.type_tuples(inner, res),
            Expr::Name(n, _) => {
                let at = if n == "univ" {
                    let mut all: Vec<String> = res
                        .sigs
                        .values()
                        .flat_map(|s| s.atoms.iter().cloned())
                        .collect();
                    all.sort();
                    all.dedup();
                    all
                } else if n == "int" || n == "Int" || n == "Signed" {
                    // Int/Signed atoms: named by their numeric value
                    // (`{0, .., W-1}` in the bit-vector model).
                    (0..res.int_count).map(|v| v.to_string()).collect()
                } else {
                    res.atoms_of(n)
                };
                Ok(at.into_iter().map(|a| vec![a]).collect())
            }
            Expr::Univ => {
                let mut all: Vec<String> = res
                    .sigs
                    .values()
                    .flat_map(|s| s.atoms.iter().cloned())
                    .collect();
                all.sort();
                all.dedup();
                Ok(all.into_iter().map(|a| vec![a]).collect())
            }
            Expr::None_ | Expr::Iden => Ok(Vec::new()),
            Expr::StepAtom => Ok(res
                .step_atoms
                .iter()
                .map(|a| vec![a.clone()])
                .collect()),
            Expr::IntAtom => {
                // Int atoms: named by their numeric value over the
                // resolved atom count (`{0, .., W-1}`).
                let int_atoms: Vec<Vec<String>> =
                    (0..res.int_count).map(|v| vec![v.to_string()]).collect();
                Ok(int_atoms)
            }
            Expr::Bin(BinOp::Product, a, b) => {
                let ta = self.type_tuples(a, res)?;
                let tb = self.type_tuples(b, res)?;
                let mut out = Vec::new();
                for x in &ta {
                    for y in &tb {
                        let mut t = x.clone();
                        t.extend(y.iter().cloned());
                        out.push(t);
                    }
                }
                Ok(out)
            }
            Expr::Bin(BinOp::Union, a, b) => {
                let mut out = self.type_tuples(a, res)?;
                out.extend(self.type_tuples(b, res)?);
                out.sort();
                out.dedup();
                Ok(out)
            }
            Expr::Bin(BinOp::Difference, a, b) => {
                let sa: std::collections::BTreeSet<_> =
                    self.type_tuples(b, res)?.into_iter().collect();
                Ok(self
                    .type_tuples(a, res)?
                    .into_iter()
                    .filter(|t| !sa.contains(t))
                    .collect())
            }
            _ => self.unsup("complex expression in field declaration"),
        }
    }
}

/// Rightmost field label of a dotted chain (`Bar.f` -> `f`).
fn trailing_field_name(e: &Expr) -> Option<String> {
    match e {
        Expr::Name(n, _) => Some(n.clone()),
        Expr::Bin(_, _, r) => trailing_field_name(r),
        Expr::Bracket(base, _) => trailing_field_name(base),
        _ => None,
    }
}

/// Shared lowering context over resolved names.
struct Ctx<'a> {
    module: &'a Module,
    res: &'a Resolved,
    rels: &'a HashMap<String, RelationId>,
    #[allow(dead_code)]
    field_arity: &'a HashMap<String, u32>,
    ordering_info: &'a HashMap<String, (RelationId, RelationId)>,
    depth: std::cell::Cell<u32>,
    /// alias -> parameter type names (from `open util/graph[Type] as graph`)
    open_params: HashMap<String, Vec<String>>,
    /// expression-level name bindings (used for sig fact field qualification):
    /// name -> (kodkod expr, arity, abstract flavor).
    expr_binds: std::cell::RefCell<HashMap<String, BindEntry>>,
    /// Per-field abstract flavor (key `Owner.field`): `Int` when the
    /// field type mentions `int`/`Int`/`Signed` (bitmask-comparable).
    field_int: HashMap<String, SetKind>,
    /// let-binding scope: name -> `BindEntry`.
    let_binds: std::cell::RefCell<Vec<HashMap<String, BindEntry>>>,
    /// Whether universe atom names (`A$0`) resolve as singleton sets.
    /// True only for the `:query` path (solve-after evaluation, mirroring
    /// Java's `frame.a2k`); model text (run/check/eval builds) rejects
    /// them with Java's `$` error instead.
    allow_atoms: bool,
    /// Gensym sequence for `pin` label variables (`$pin{n}_...`).
    /// A counter (not source positions): one `pin` inside a twice-called
    /// predicate expands twice and must not collide with itself.
    pin_seq: std::cell::Cell<u32>,
    /// Collected in-body `maximize`/`minimize` markers.
    markers: std::cell::RefCell<Vec<OptMarker>>,
    /// Innermost enclosing state-pinning temporal operator for markers
    /// (`initially`/`goal`/`restore`); `None` outside temporal contexts.
    marker_time: std::cell::Cell<Option<TimePoint>>,
}

impl<'a> Ctx<'a> {
    fn unsup<T>(&self, what: impl Into<String>) -> LResult<T> {
        Err(FrontError::Unsupported(what.into()))
    }

    fn lookup_rel(&self, name: &str) -> Option<RelationId> {
        if let Some(r) = self.rels.get(name) {
            return Some(*r);
        }
        // field reference without owner prefix: unique field name?
        let hits: Vec<&RelationId> = self
            .rels
            .iter()
            .filter(|(k, _)| k.ends_with(&format!(".{name}")))
            .map(|(_, v)| v)
            .collect();
        if hits.len() == 1 {
            Some(*hits[0])
        } else {
            None
        }
    }

    /// Look up a field by bare name, returning all matching relations (for ambiguous field names).
    fn lookup_rel_all(&self, name: &str) -> Vec<RelationId> {
        if let Some(r) = self.rels.get(name) {
            return vec![*r];
        }
        self.rels
            .iter()
            .filter(|(k, _)| k.ends_with(&format!(".{name}")))
            .map(|(_, v)| *v)
            .collect()
    }

    /// Try to resolve an ordering builtin call as an expression.
    /// Returns Some((expr, arity)) if the name matches an ordering builtin.
    fn try_ordering_expr(
        &self,
        arena: &mut kk::AstArena,
        name: &str,
        args: &[Expr],
        env: &mut Env,
    ) -> LResult<Option<(ExprId, u32)>> {
        // Parse "alias/builtin" pattern
        let (alias, builtin) = match name.split_once('/') {
            Some((a, b)) => (a, b),
            None => return Ok(None),
        };
        let &(first_rel, next_rel) = match self.ordering_info.get(alias) {
            Some(info) => info,
            None => return Ok(None),
        };
        let next_e = arena.expr_relation(next_rel);
        match builtin {
            "first" => Ok(Some((arena.expr_relation(first_rel), 1))),
            "next" => Ok(Some((next_e, 2))),
            "prev" => {
                let inv = arena
                    .unary_expr(kk::UnaryExprOp::Transpose, next_e)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                Ok(Some((inv, 2)))
            }
            "last" => {
                // sig - (next.sig)
                let sig_name = match &self
                    .module
                    .opens
                    .iter()
                    .find(|o| o.alias == alias)
                    .and_then(|o| o.params.first())
                {
                    Some(OpenParam::Exactly(n) | OpenParam::Set(n)) => n.clone(),
                    _ => return Ok(None),
                };
                let sig_rel = self
                    .rels
                    .get(&sig_name)
                    .copied()
                    .ok_or_else(|| FrontError::Resolve(format!("unknown sig {sig_name}")))?;
                let sig_e = arena.expr_relation(sig_rel);
                let next_of_sig = arena
                    .binary_expr(kk::BinaryOp::Join, next_e, sig_e)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let last = arena
                    .binary_expr(kk::BinaryOp::Difference, sig_e, next_of_sig)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                Ok(Some((last, 1)))
            }
            "nexts" => {
                // e.^next
                if args.len() != 1 {
                    return Err(FrontError::Resolve("nexts expects 1 arg".into()));
                }
                let (ee, _) = self.lower_expr(arena, &args[0], env)?;
                let tc = arena
                    .unary_expr(kk::UnaryExprOp::Closure, next_e)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let r = arena
                    .binary_expr(kk::BinaryOp::Join, ee, tc)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                Ok(Some((r, 1)))
            }
            "prevs" => {
                // e.^(~next)
                if args.len() != 1 {
                    return Err(FrontError::Resolve("prevs expects 1 arg".into()));
                }
                let (ee, _) = self.lower_expr(arena, &args[0], env)?;
                let inv = arena
                    .unary_expr(kk::UnaryExprOp::Transpose, next_e)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let tc = arena
                    .unary_expr(kk::UnaryExprOp::Closure, inv)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let r = arena
                    .binary_expr(kk::BinaryOp::Join, ee, tc)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                Ok(Some((r, 1)))
            }
            "larger" => {
                // lt[e1,e2] => e2 else e1
                // lt is the binary relation ^next (transitive closure of next)
                if args.len() != 2 {
                    return Err(FrontError::Resolve("larger expects 2 args".into()));
                }
                let (e1, a1) = self.lower_expr(arena, &args[0], env)?;
                let (e2, a2) = self.lower_expr(arena, &args[1], env)?;
                let tc = arena
                    .unary_expr(kk::UnaryExprOp::Closure, next_e)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                // For binary args: lt = e1.^(~next), cond = lt.e2 some
                // For unary args: lt = ^(next), cond = (e1->e2) in lt
                if a1 >= 2 && a2 >= 2 {
                    let inv = arena
                        .unary_expr(kk::UnaryExprOp::Transpose, next_e)
                        .map_err(|e| FrontError::Resolve(e.to_string()))?;
                    let lt = arena
                        .binary_expr(kk::BinaryOp::Join, e1, inv)
                        .map_err(|e| FrontError::Resolve(e.to_string()))?;
                    let tc_lt = arena
                        .unary_expr(kk::UnaryExprOp::Closure, lt)
                        .map_err(|e| FrontError::Resolve(e.to_string()))?;
                    let lt_some = arena
                        .binary_expr(kk::BinaryOp::Join, tc_lt, e2)
                        .map_err(|e| FrontError::Resolve(e.to_string()))?;
                    let cond = arena
                        .multiplicity_formula(Multiplicity::Some, lt_some)
                        .map_err(|e| FrontError::Resolve(e.to_string()))?;
                    let r = arena
                        .if_expr(cond, e2, e1)
                        .map_err(|e| FrontError::Resolve(e.to_string()))?;
                    Ok(Some((r, a1.max(a2))))
                } else {
                    // Unary case: check (e1 -> e2) in ^(next)
                    let prod = arena
                        .binary_expr(kk::BinaryOp::Product, e1, e2)
                        .map_err(|e| FrontError::Resolve(e.to_string()))?;
                    let cond = arena
                        .comparison(kk::ExprCompOp::Subset, prod, tc)
                        .map_err(|e| FrontError::Resolve(e.to_string()))?;
                    let r = arena
                        .if_expr(cond, e2, e1)
                        .map_err(|e| FrontError::Resolve(e.to_string()))?;
                    Ok(Some((r, 1)))
                }
            }
            "smaller" => {
                // lt[e1,e2] => e1 else e2
                // lt is the binary relation ^next (transitive closure of next)
                if args.len() != 2 {
                    return Err(FrontError::Resolve("smaller expects 2 args".into()));
                }
                let (e1, a1) = self.lower_expr(arena, &args[0], env)?;
                let (e2, a2) = self.lower_expr(arena, &args[1], env)?;
                let tc = arena
                    .unary_expr(kk::UnaryExprOp::Closure, next_e)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                if a1 >= 2 && a2 >= 2 {
                    let inv = arena
                        .unary_expr(kk::UnaryExprOp::Transpose, next_e)
                        .map_err(|e| FrontError::Resolve(e.to_string()))?;
                    let lt = arena
                        .binary_expr(kk::BinaryOp::Join, e1, inv)
                        .map_err(|e| FrontError::Resolve(e.to_string()))?;
                    let tc_lt = arena
                        .unary_expr(kk::UnaryExprOp::Closure, lt)
                        .map_err(|e| FrontError::Resolve(e.to_string()))?;
                    let lt_some = arena
                        .binary_expr(kk::BinaryOp::Join, tc_lt, e2)
                        .map_err(|e| FrontError::Resolve(e.to_string()))?;
                    let cond = arena
                        .multiplicity_formula(Multiplicity::Some, lt_some)
                        .map_err(|e| FrontError::Resolve(e.to_string()))?;
                    let r = arena
                        .if_expr(cond, e1, e2)
                        .map_err(|e| FrontError::Resolve(e.to_string()))?;
                    Ok(Some((r, a1.max(a2))))
                } else {
                    let prod = arena
                        .binary_expr(kk::BinaryOp::Product, e1, e2)
                        .map_err(|e| FrontError::Resolve(e.to_string()))?;
                    let cond = arena
                        .comparison(kk::ExprCompOp::Subset, prod, tc)
                        .map_err(|e| FrontError::Resolve(e.to_string()))?;
                    let r = arena
                        .if_expr(cond, e1, e2)
                        .map_err(|e| FrontError::Resolve(e.to_string()))?;
                    Ok(Some((r, 1)))
                }
            }
            _ => Ok(None),
        }
    }

    /// Try to resolve an ordering builtin predicate call.
    /// Returns Some(formula) if the name matches an ordering builtin predicate.
    /// Builtin `EReal` predicates (`erealAdd` etc.): desugar to comparator
    /// formulas over lane joins and lower recursively. Lane reads lower
    /// through the lane-scoped `BitsIn` cast; `m`/`e` centres stay free
    /// (mirrors `util/mepk.als`: the error exponents are pinned, exact
    /// centres are delegated to the oracle).
    fn try_ereal_pred(
        &self,
        arena: &mut kk::AstArena,
        name: &str,
        args: &[Expr],
        env: &mut Env,
    ) -> LResult<Option<FormulaId>> {
        let body = match name {
            "erealAdd" | "erealSub" => {
                if args.len() != 3 {
                    return Err(FrontError::Resolve(format!("'{name}' expects 3 args")));
                }
                ereal_add_sub(&args[0], &args[1], &args[2])
            }
            "erealMul" => {
                if args.len() != 3 {
                    return Err(FrontError::Resolve(format!("'{name}' expects 3 args")));
                }
                ereal_mul(&args[0], &args[1], &args[2])
            }
            "erealDiv" => {
                if args.len() != 3 {
                    return Err(FrontError::Resolve(format!("'{name}' expects 3 args")));
                }
                ereal_div(&args[0], &args[1], &args[2])
            }
            "erealWellformed" => {
                if args.len() != 1 {
                    return Err(FrontError::Resolve(format!("'{name}' expects 1 arg")));
                }
                ereal_wellformed(&args[0])
            }
            "erealDivGuard" => {
                if args.len() != 1 {
                    return Err(FrontError::Resolve(format!("'{name}' expects 1 arg")));
                }
                ereal_div_guard(&args[0])
            }
            "erealNeedsRefine" => {
                if args.len() != 2 {
                    return Err(FrontError::Resolve(format!("'{name}' expects 2 args")));
                }
                ereal_needs_refine(&args[0], &args[1])
            }
            "setEReal" => {
                if args.len() != 2 {
                    return Err(FrontError::Resolve(format!("'{name}' expects 2 args")));
                }
                // Precision cap from the active widths (same default as
                // `:mepk lit`: usable mantissa precision).
                let max_p = self.res.mepk_widths.m_width.saturating_sub(1).max(1);
                ereal_set(&args[0], &args[1], max_p)?
            }
            _ => return Ok(None),
        };
        Ok(Some(self.lower_formula(arena, &body, env)?))
    }

    fn try_ordering_pred(
        &self,
        arena: &mut kk::AstArena,
        name: &str,
        args: &[Expr],
        env: &mut Env,
    ) -> LResult<Option<FormulaId>> {
        let (alias, builtin) = match name.split_once('/') {
            Some((a, b)) => (a, b),
            None => return Ok(None),
        };
        let &(_, next_rel) = match self.ordering_info.get(alias) {
            Some(info) => info,
            None => return Ok(None),
        };
        let next_e = arena.expr_relation(next_rel);
        match builtin {
            "lt" => {
                if args.len() != 2 {
                    return Err(FrontError::Resolve("lt expects 2 args".into()));
                }
                let (e1, _) = self.lower_expr(arena, &args[0], env)?;
                let (e2, _) = self.lower_expr(arena, &args[1], env)?;
                // e1 in prevs[e2]  <=>  e1->e2 in ~next  <=>  e2->e1 in next
                let inv = arena
                    .unary_expr(kk::UnaryExprOp::Transpose, next_e)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let tc = arena
                    .unary_expr(kk::UnaryExprOp::Closure, inv)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let joined = arena
                    .binary_expr(kk::BinaryOp::Join, e1, tc)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let f = arena
                    .comparison(ExprCompOp::Subset, joined, e2)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                Ok(Some(f))
            }
            "gt" => {
                if args.len() != 2 {
                    return Err(FrontError::Resolve("gt expects 2 args".into()));
                }
                let (e1, _) = self.lower_expr(arena, &args[0], env)?;
                let (e2, _) = self.lower_expr(arena, &args[1], env)?;
                let tc = arena
                    .unary_expr(kk::UnaryExprOp::Closure, next_e)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let joined = arena
                    .binary_expr(kk::BinaryOp::Join, e1, tc)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let f = arena
                    .comparison(ExprCompOp::Subset, joined, e2)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                Ok(Some(f))
            }
            "lte" => {
                if args.len() != 2 {
                    return Err(FrontError::Resolve("lte expects 2 args".into()));
                }
                let (e1, _) = self.lower_expr(arena, &args[0], env)?;
                let (e2, _) = self.lower_expr(arena, &args[1], env)?;
                // e1 = e2 || lt[e1,e2]
                let eq = arena
                    .comparison(ExprCompOp::Equals, e1, e2)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let inv = arena
                    .unary_expr(kk::UnaryExprOp::Transpose, next_e)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let tc = arena
                    .unary_expr(kk::UnaryExprOp::Closure, inv)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let joined = arena
                    .binary_expr(kk::BinaryOp::Join, e1, tc)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let lt_f = arena
                    .comparison(ExprCompOp::Subset, joined, e2)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let f = arena.or(&[eq, lt_f]);
                Ok(Some(f))
            }
            "gte" => {
                if args.len() != 2 {
                    return Err(FrontError::Resolve("gte expects 2 args".into()));
                }
                let (e1, _) = self.lower_expr(arena, &args[0], env)?;
                let (e2, _) = self.lower_expr(arena, &args[1], env)?;
                let eq = arena
                    .comparison(ExprCompOp::Equals, e1, e2)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let tc = arena
                    .unary_expr(kk::UnaryExprOp::Closure, next_e)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let joined = arena
                    .binary_expr(kk::BinaryOp::Join, e1, tc)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let gt_f = arena
                    .comparison(ExprCompOp::Subset, joined, e2)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let f = arena.or(&[eq, gt_f]);
                Ok(Some(f))
            }
            _ => Ok(None),
        }
    }

    /// Try to resolve a stdlib predicate call (e.g. `graph/dag[r]`, `relation/acyclic[r, s]`).
    fn try_stdlib_pred(
        &self,
        arena: &mut kk::AstArena,
        name: &str,
        args: &[Expr],
        env: &mut Env,
    ) -> LResult<Option<FormulaId>> {
        let (alias, builtin) = match name.split_once('/') {
            Some((a, b)) => (a, b),
            None => return Ok(None),
        };
        let domain_type = match self.open_params.get(alias) {
            Some(params) if !params.is_empty() => params[0].clone(),
            _ => return Ok(None),
        };
        let domain_sig = match self.rels.get(&domain_type) {
            Some(&r) => r,
            _ => return Ok(None),
        };

        match builtin {
            "dag" => {
                if args.len() != 1 {
                    return Err(FrontError::Resolve("dag expects 1 arg".into()));
                }
                let (re, _ra) = self.lower_expr(arena, &args[0], env)?;
                let domain_e = arena.expr_relation(domain_sig);
                let v = arena.variable("_x_dag");
                let d = arena.decl(v, Multiplicity::One, domain_e).unwrap();
                let ds = arena.add_decls(vec![d]);
                let ve = arena.expr_variable(v);
                let tc = arena
                    .unary_expr(kk::UnaryExprOp::Closure, re)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let x_tc = arena
                    .binary_expr(kk::BinaryOp::Join, ve, tc)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let x_in_tc = arena
                    .comparison(ExprCompOp::Subset, ve, x_tc)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let nx_in_tc = arena.not(x_in_tc);
                Ok(Some(arena.quantified(Quantifier::All, ds, nx_in_tc)))
            }
            "forest" => {
                if args.len() != 1 {
                    return Err(FrontError::Resolve("forest expects 1 arg".into()));
                }
                let dag_f = self
                    .try_stdlib_pred(arena, &format!("{alias}/dag"), args, env)?
                    .ok_or_else(|| FrontError::Resolve("dag not found".into()))?;
                let (re, _ra) = self.lower_expr(arena, &args[0], env)?;
                let domain_e = arena.expr_relation(domain_sig);
                let v = arena.variable("_n_for");
                let d = arena.decl(v, Multiplicity::One, domain_e).unwrap();
                let ds = arena.add_decls(vec![d]);
                let ve = arena.expr_variable(v);
                let n_r = arena
                    .binary_expr(kk::BinaryOp::Join, ve, re)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let lone_n_r = arena
                    .multiplicity_formula(Multiplicity::Lone, n_r)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let all_lone = arena.quantified(Quantifier::All, ds, lone_n_r);
                Ok(Some(arena.and(&[dag_f, all_lone])))
            }
            "tree" => {
                if args.len() != 1 {
                    return Err(FrontError::Resolve("tree expects 1 arg".into()));
                }
                let forest_f = self
                    .try_stdlib_pred(arena, &format!("{alias}/forest"), args, env)?
                    .ok_or_else(|| FrontError::Resolve("forest not found".into()))?;
                let (re, _ra) = self.lower_expr(arena, &args[0], env)?;
                let domain_e = arena.expr_relation(domain_sig);
                let domain_all = arena.expr_relation(domain_sig);
                let tr = arena
                    .unary_expr(kk::UnaryExprOp::Transpose, re)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let tc = arena
                    .unary_expr(kk::UnaryExprOp::Closure, tr)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let all_tc = arena
                    .binary_expr(kk::BinaryOp::Join, domain_all, tc)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let roots = arena
                    .binary_expr(kk::BinaryOp::Difference, domain_e, all_tc)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let lone_roots = arena
                    .multiplicity_formula(Multiplicity::Lone, roots)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                Ok(Some(arena.and(&[forest_f, lone_roots])))
            }
            "weaklyConnected" => {
                if args.len() != 1 {
                    return Err(FrontError::Resolve("weaklyConnected expects 1 arg".into()));
                }
                let (re, _ra) = self.lower_expr(arena, &args[0], env)?;
                let domain_e = arena.expr_relation(domain_sig);
                let tr = arena
                    .unary_expr(kk::UnaryExprOp::Transpose, re)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let r_plus_tr = arena
                    .binary_expr(kk::BinaryOp::Union, re, tr)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let star = arena
                    .unary_expr(kk::UnaryExprOp::ReflexiveClosure, r_plus_tr)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let v1 = arena.variable("_n1_wc");
                let v2 = arena.variable("_n2_wc");
                let d1 = arena.decl(v1, Multiplicity::One, domain_e).unwrap();
                let domain_e2 = arena.expr_relation(domain_sig);
                let d2 = arena.decl(v2, Multiplicity::One, domain_e2).unwrap();
                let ds = arena.add_decls(vec![d1, d2]);
                let v1e = arena.expr_variable(v1);
                let v2e = arena.expr_variable(v2);
                let n2_star = arena
                    .binary_expr(kk::BinaryOp::Join, v2e, star)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let f = arena
                    .comparison(ExprCompOp::Subset, v1e, n2_star)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                Ok(Some(arena.quantified(Quantifier::All, ds, f)))
            }
            "stronglyConnected" => {
                if args.len() != 1 {
                    return Err(FrontError::Resolve(
                        "stronglyConnected expects 1 arg".into(),
                    ));
                }
                let (re, _ra) = self.lower_expr(arena, &args[0], env)?;
                let domain_e = arena.expr_relation(domain_sig);
                let star = arena
                    .unary_expr(kk::UnaryExprOp::ReflexiveClosure, re)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let v1 = arena.variable("_n1_sc");
                let v2 = arena.variable("_n2_sc");
                let d1 = arena.decl(v1, Multiplicity::One, domain_e).unwrap();
                let domain_e2 = arena.expr_relation(domain_sig);
                let d2 = arena.decl(v2, Multiplicity::One, domain_e2).unwrap();
                let ds = arena.add_decls(vec![d1, d2]);
                let v1e = arena.expr_variable(v1);
                let v2e = arena.expr_variable(v2);
                let n2_star = arena
                    .binary_expr(kk::BinaryOp::Join, v2e, star)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let f = arena
                    .comparison(ExprCompOp::Subset, v1e, n2_star)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                Ok(Some(arena.quantified(Quantifier::All, ds, f)))
            }
            "acyclic" => {
                if args.len() != 2 {
                    return Err(FrontError::Resolve("acyclic expects 2 args".into()));
                }
                let (re, _ra) = self.lower_expr(arena, &args[0], env)?;
                let (se, _sa) = self.lower_expr(arena, &args[1], env)?;
                let v = arena.variable("_x_acyc");
                let d = arena.decl(v, Multiplicity::One, se).unwrap();
                let ds = arena.add_decls(vec![d]);
                let ve = arena.expr_variable(v);
                let tc = arena
                    .unary_expr(kk::UnaryExprOp::Closure, re)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let x_tc = arena
                    .binary_expr(kk::BinaryOp::Join, ve, tc)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let x_in_tc = arena
                    .comparison(ExprCompOp::Subset, ve, x_tc)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let nx_in_tc = arena.not(x_in_tc);
                Ok(Some(arena.quantified(Quantifier::All, ds, nx_in_tc)))
            }
            "irreflexive" => {
                if args.len() != 1 {
                    return Err(FrontError::Resolve("irreflexive expects 1 arg".into()));
                }
                let (re, _ra) = self.lower_expr(arena, &args[0], env)?;
                let iden = arena.constant(kk::ConstantExpr::Iden);
                let inter = arena
                    .binary_expr(kk::BinaryOp::Intersection, iden, re)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let some_inter = arena
                    .multiplicity_formula(Multiplicity::Some, inter)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                Ok(Some(arena.not(some_inter)))
            }
            "symmetric" => {
                if args.len() != 1 {
                    return Err(FrontError::Resolve("symmetric expects 1 arg".into()));
                }
                let (re, _ra) = self.lower_expr(arena, &args[0], env)?;
                let tr = arena
                    .unary_expr(kk::UnaryExprOp::Transpose, re)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let f = arena
                    .comparison(ExprCompOp::Subset, tr, re)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                Ok(Some(f))
            }
            "transitive" => {
                if args.len() != 1 {
                    return Err(FrontError::Resolve("transitive expects 1 arg".into()));
                }
                let (re, _ra) = self.lower_expr(arena, &args[0], env)?;
                let rr = arena
                    .binary_expr(kk::BinaryOp::Join, re, re)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let f = arena
                    .comparison(ExprCompOp::Subset, rr, re)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                Ok(Some(f))
            }
            "reflexive" => {
                if args.len() != 2 {
                    return Err(FrontError::Resolve("reflexive expects 2 args".into()));
                }
                let (re, _ra) = self.lower_expr(arena, &args[0], env)?;
                let (se, _sa) = self.lower_expr(arena, &args[1], env)?;
                let iden = arena.constant(kk::ConstantExpr::Iden);
                let univ = arena.constant(kk::ConstantExpr::Univ);
                let sxu = arena
                    .binary_expr(kk::BinaryOp::Product, se, univ)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let s_iden = arena
                    .binary_expr(kk::BinaryOp::Intersection, iden, sxu)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let f = arena
                    .comparison(ExprCompOp::Subset, s_iden, re)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                Ok(Some(f))
            }
            _ => Ok(None),
        }
    }

    /// Try to resolve a stdlib function call (e.g. `graph/roots[r]`).
    fn try_stdlib_expr(
        &self,
        arena: &mut kk::AstArena,
        name: &str,
        args: &[Expr],
        env: &mut Env,
    ) -> LResult<Option<(ExprId, u32)>> {
        let (alias, builtin) = match name.split_once('/') {
            Some((a, b)) => (a, b),
            None => return Ok(None),
        };
        let domain_type = match self.open_params.get(alias) {
            Some(params) if !params.is_empty() => params[0].clone(),
            _ => return Ok(None),
        };
        let domain_sig = match self.rels.get(&domain_type) {
            Some(&r) => r,
            _ => return Ok(None),
        };

        match builtin {
            "roots" => {
                if args.len() != 1 {
                    return Err(FrontError::Resolve("roots expects 1 arg".into()));
                }
                let (re, _ra) = self.lower_expr(arena, &args[0], env)?;
                let domain_e = arena.expr_relation(domain_sig);
                let tr = arena
                    .unary_expr(kk::UnaryExprOp::Transpose, re)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let tc = arena
                    .unary_expr(kk::UnaryExprOp::Closure, tr)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let all_tc = arena
                    .binary_expr(kk::BinaryOp::Join, domain_e, tc)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let domain_e2 = arena.expr_relation(domain_sig);
                let roots = arena
                    .binary_expr(kk::BinaryOp::Difference, domain_e2, all_tc)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                Ok(Some((roots, 1)))
            }
            "leaves" => {
                if args.len() != 1 {
                    return Err(FrontError::Resolve("leaves expects 1 arg".into()));
                }
                let (re, _ra) = self.lower_expr(arena, &args[0], env)?;
                let tc = arena
                    .unary_expr(kk::UnaryExprOp::Closure, re)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let domain_e = arena.expr_relation(domain_sig);
                let all_tc = arena
                    .binary_expr(kk::BinaryOp::Join, domain_e, tc)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let domain_e2 = arena.expr_relation(domain_sig);
                let leaves = arena
                    .binary_expr(kk::BinaryOp::Difference, domain_e2, all_tc)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                Ok(Some((leaves, 1)))
            }
            "dom" => {
                if args.len() != 1 {
                    return Err(FrontError::Resolve("dom expects 1 arg".into()));
                }
                let (re, _ra) = self.lower_expr(arena, &args[0], env)?;
                let univ = arena.constant(kk::ConstantExpr::Univ);
                let dom = arena
                    .binary_expr(kk::BinaryOp::Join, re, univ)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                Ok(Some((dom, 1)))
            }
            "ran" => {
                if args.len() != 1 {
                    return Err(FrontError::Resolve("ran expects 1 arg".into()));
                }
                let (re, _ra) = self.lower_expr(arena, &args[0], env)?;
                let univ = arena.constant(kk::ConstantExpr::Univ);
                let ran = arena
                    .binary_expr(kk::BinaryOp::Join, univ, re)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                Ok(Some((ran, 1)))
            }
            _ => Ok(None),
        }
    }

    fn lower_sig_fact(
        &self,
        arena: &mut kk::AstArena,
        f: &Formula,
        owner: &str,
    ) -> LResult<FormulaId> {
        let srel = *self
            .rels
            .get(owner)
            .ok_or_else(|| FrontError::Resolve(format!("unknown sig {owner}")))?;
        let var = arena.variable("this");
        let dom = arena.expr_relation(srel);
        let d = arena.decl(var, Multiplicity::One, dom).unwrap();
        let ds = arena.add_decls(vec![d]);
        let this_e = arena.expr_variable(var);

        // Collect all field names for this sig and ancestors, and build this.field bindings
        let mut binds: HashMap<String, BindEntry> = HashMap::new();
        self.collect_sig_field_binds(arena, owner, this_e, &mut binds);

        *self.expr_binds.borrow_mut() = binds;
        let mut env: Env = vec![("this".into(), var, 1, SetKind::Plain)];
        let body = self.lower_formula(arena, f, &mut env)?;
        self.expr_binds.borrow_mut().clear();
        Ok(arena.quantified(Quantifier::All, ds, body))
    }

    fn collect_sig_field_binds(
        &self,
        arena: &mut kk::AstArena,
        sig_name: &str,
        this_e: ExprId,
        binds: &mut HashMap<String, BindEntry>,
    ) {
        // Find the sig decl
        let sd = match self
            .module
            .sigs
            .iter()
            .find(|s| s.names.iter().any(|n| n == sig_name))
        {
            Some(s) => s.clone(),
            None => return,
        };
        // Process this sig's fields
        for fd in &sd.fields {
            for fname in &fd.names {
                if binds.contains_key(fname) {
                    continue;
                }
                // Try this sig first
                let field_key = format!("{sig_name}.{fname}");
                let fr = self.rels.get(&field_key).copied();
                // If not found, walk up ancestors
                let fr = if fr.is_some() {
                    fr
                } else {
                    let mut found = None;
                    let mut cur = sd.extends.as_deref();
                    while let Some(parent) = cur {
                        let pk = format!("{parent}.{fname}");
                        if let Some(&r) = self.rels.get(&pk) {
                            found = Some(r);
                            break;
                        }
                        if let Some(psd) = self
                            .module
                            .sigs
                            .iter()
                            .find(|s| s.names.iter().any(|n| n == parent))
                        {
                            cur = psd.extends.as_deref();
                        } else {
                            break;
                        }
                    }
                    found
                };
                if let Some(fr) = fr {
                    let fexpr = arena.expr_relation(fr);
                    let fa = arena.relation_arity(fr);
                    let flavor = self
                        .field_int
                        .get(&format!("{sig_name}.{fname}"))
                        .copied()
                        .unwrap_or(SetKind::Plain);
                    if let Ok(this_field) = arena.binary_expr(kk::BinaryOp::Join, this_e, fexpr) {
                        binds.insert(fname.clone(), (this_field, fa - 1, flavor));
                    }
                }
            }
        }
        // Recurse to parent
        if let Some(ref parent) = sd.extends {
            self.collect_sig_field_binds(arena, parent, this_e, binds);
        }
    }

    /// Exact singleton set of the int atom `v` (bit-vector model: int
    /// atoms are named by value, `{0, .., W-1}`). Errors when the atom was
    /// not materialized (lazy Int allocation).
    fn int_atom_singleton(&self, arena: &mut kk::AstArena, v: i64) -> LResult<ExprId> {
        let name = v.to_string();
        match self.res.universe.index(&name) {
            Ok(idx) => Ok(arena.expr_atoms(vec![idx])),
            Err(e) => Err(FrontError::Resolve(format!(
                "int atom '{name}' is not in scope (W = {} int atoms; mention Int in the model or add `for N Int`): {e}",
                self.res.int_count
            ))),
        }
    }

    /// Abstract flavor of a sig: `Int` when its ancestor chain roots at
    /// the builtin `Int` or `Signed` (atoms are `{0..W-1}` int atoms).
    fn sig_int_flavored(&self, name: &str) -> SetKind {
        let mut cur = name.to_string();
        loop {
            match self.res.sigs.get(&cur) {
                Some(si) => match &si.parent {
                    Some(p) if p == "Int" || p == "Signed" => return SetKind::Int,
                    Some(p) => cur = p.clone(),
                    None => return SetKind::Plain,
                },
                None => return SetKind::Plain,
            }
        }
    }

    /// Abstract flavor of the LAST field of a dotted chain (`a.x` -> `x`):
    /// Some(kind) when the label resolves to declared fields.
    /// Bit-lane group of the LAST field of a dotted chain (`a.m` -> `m`):
    /// Some(group) when the label uniquely resolves to a builtin `EReal`
    /// lane (`EReal.m` etc.). Labels shared with user fields decline to
    /// None unless `EReal` is allocated (then the use is genuinely
    /// ambiguous and the caller must error loudly, never read 0).
    fn lane_group_of(&self, e: &Expr) -> Option<u32> {
        let field = trailing_field_name(e)?;
        let mut found: Option<u32> = None;
        let mut count = 0;
        for key in self.field_int.keys() {
            if key.rsplit('.').next() == Some(field.as_str()) {
                count += 1;
                if let Some((_, group)) = crate::bounds::EREAL_LANES
                    .iter()
                    .find(|(fname, _)| key == &format!("EReal.{fname}"))
                {
                    // Ignore the builtin lane while `EReal` is unallocated:
                    // a lone user field keeps its legacy reading.
                    let allocated = self
                        .res
                        .lane_atoms
                        .get(group)
                        .is_some_and(|v| !v.is_empty());
                    if !allocated {
                        count -= 1;
                        continue;
                    }
                    found = Some(*group);
                }
            }
        }
        if count == 1 { found } else { None }
    }

    /// True when `e`'s trailing label names both an allocated `EReal`
    /// lane and a user (non-`EReal`) field: genuinely ambiguous.
    fn lane_label_ambiguous(&self, e: &Expr) -> bool {
        let Some(field) = trailing_field_name(e) else {
            return false;
        };
        let lane_allocated = crate::bounds::EREAL_LANES.iter().any(|(fname, g)| {
            *fname == field && self.res.lane_atoms.get(g).is_some_and(|v| !v.is_empty())
        });
        lane_allocated
            && self.field_int.keys().any(|key| {
                key.rsplit('.').next() == Some(field.as_str()) && !key.starts_with("EReal.")
            })
    }

    /// True when the trailing field label also matches a builtin `EReal`
    /// lane (allocated) alongside user fields: the lane reading is
    /// genuinely ambiguous and must error, never silently read 0.
    fn lane_group_ambiguous(&self, e: &Expr) -> bool {
        self.lane_label_ambiguous(e)
    }

    /// Lane equality rewritten as integer comparisons: `x.m = 3` means
    /// the lane's bitmask value is 3, and `x.m = y.m` compares values
    /// (relational set equality could never hold across disjoint lane
    /// namespaces). Returns None for non-lane shapes (legacy reading).
    /// A label shared with a user field while `EReal` is allocated is a
    /// hard error (never a silent empty read).
    fn rewrite_lane_lit_cmp(
        &self,
        kind: &CmpKind,
        l: &Expr,
        r: &Expr,
    ) -> LResult<Option<Formula>> {
        let op = match kind {
            CmpKind::Eq => IntCmpOp::Eq,
            CmpKind::Neq => IntCmpOp::Neq,
            _ => return Ok(None),
        };
        for side in [l, r] {
            if self.lane_label_ambiguous(side) {
                return Err(FrontError::Resolve(
                    "ambiguous EReal lane: a user field shares this label; qualify explicitly"
                        .to_string(),
                ));
            }
        }
        let lane_int = |e: &Expr| -> Option<IntExpr> {
            self.lane_group_of(e)?;
            Some(IntExpr::BitsVal(Box::new(e.clone()), 0))
        };
        // Lane-vs-lane first (values may differ per lane namespace).
        if let (Some(li), Some(ri)) = (lane_int(l), lane_int(r)) {
            return Ok(Some(Formula::IntCmp(op, li, ri, 0)));
        }
        // Lane-vs-literal in either order. Literals arrive as `Bits(v)`
        // bitsets or bare numeric names, depending on position.
        let lit_val = |e: &Expr| -> Option<i64> {
            match e {
                Expr::Bits(v, _) => Some(*v),
                Expr::Name(n, _) => n.parse::<i64>().ok(),
                _ => None,
            }
        };
        if let (Some(li), Some(v)) = (lane_int(l), lit_val(r)) {
            return Ok(Some(Formula::IntCmp(op, li, IntExpr::Lit(v, 0), 0)));
        }
        if let (Some(v), Some(ri)) = (lit_val(l), lane_int(r)) {
            return Ok(Some(Formula::IntCmp(op, IntExpr::Lit(v, 0), ri, 0)));
        }
        Ok(None)
    }

    fn field_int_flavored(&self, e: &Expr) -> Option<SetKind> {
        let field = trailing_field_name(e)?;
        if field == "int" || field == "Int" || field == "Signed" || field == "MSB" {
            return Some(SetKind::Int);
        }
        if field.contains('$') || field.contains('/') || field.parse::<i64>().is_ok() {
            return None;
        }
        let mut found: Option<SetKind> = None;
        for (key, &flavor) in self.field_int.iter() {
            if key.rsplit('.').next() == Some(field.as_str()) {
                found = Some(match found {
                    None => flavor,
                    Some(acc) => acc.and(flavor),
                });
            }
        }
        found
    }

    /// Abstract flavor of an expression (bit-vector model): `Int` when the
    /// set denotes int atoms, so integer comparisons are bitmask
    /// meaningful. `Unknown` (comprehension, unresolved calls) behaves as
    /// non-int today; reserved for gradual strictness.
    fn set_int_flavored(&self, e: &Expr, env: &Env) -> SetKind {
        // Fast path for leaves that need no environment.
        if let Some(kind) = crate::types::leaf_kind(e) {
            match kind {
                SetKind::Int | SetKind::Plain => return kind,
                SetKind::Unknown => return kind,
            }
        }
        match e {
            Expr::Name(n, _) => {
                // name resolution order mirroring lower_expr
                {
                    let binds = self.let_binds.borrow();
                    for scope in binds.iter().rev() {
                        if let Some(&(_, _, kind)) = scope.get(n) {
                            return kind;
                        }
                    }
                }
                if let Some((_, _, _, kind)) = env.iter().rev().find(|(nm, ..)| nm == n) {
                    return *kind;
                }
                if let Some(&(_, _, kind)) = self.expr_binds.borrow().get(n) {
                    return kind;
                }
                if self.rels.contains_key(n) {
                    return self.sig_int_flavored(n);
                }
                // unresolved name: universe atom fallback treats numeric
                // atoms as int; otherwise not int-flavored.
                SetKind::from_bool(
                    self.res
                        .universe
                        .index(n)
                        .ok()
                        .and_then(|idx| self.res.universe.atom(idx as usize).ok())
                        .and_then(|s| s.parse::<i64>().ok())
                        .is_some_and(|v| v >= 0),
                )
            }
            Expr::Bin(op, l, r) => match op {
                BinOp::Join => match self.field_int_flavored(r) {
                    Some(kind) => kind,
                    None => self.set_int_flavored(r, env).and(self.set_int_flavored(l, env)),
                },
                _ => self.set_int_flavored(l, env).and(self.set_int_flavored(r, env)),
            },
            Expr::Transpose(x)
            | Expr::TClosure(x)
            | Expr::RClosure(x)
            | Expr::Prime(x)
            | Expr::AtExpr(x)
            | Expr::ArrowMult(_, x)
            | Expr::LeadMult(_, x) => self.set_int_flavored(x, env),
            Expr::Bracket(base, args) => {
                let mut kind = self.set_int_flavored(base, env);
                for a in args {
                    kind = kind.and(self.set_int_flavored(a, env));
                }
                kind
            }
            Expr::Call(name, _, _) => self
                .module
                .paras
                .iter()
                .find(|p| p.is_fun && p.name == *name && p.ret.is_some())
                .map(|p| self.set_int_flavored(p.ret.as_ref().unwrap(), env))
                .unwrap_or(SetKind::Unknown),
            Expr::If(_c, t, el) => self.set_int_flavored(t, env).and(self.set_int_flavored(el, env)),
            Expr::LetBind(binds, body) => {
                let mut kind = self.set_int_flavored(body, env);
                for (_, ex) in binds {
                    kind = kind.and(self.set_int_flavored(ex, env));
                }
                kind
            }
            // Conservative: other shapes error on int use.
            _ => SetKind::Plain,
        }
    }

    /// Single gate for set-typed operands in integer position: checks the
    /// abstract flavor, then lowers and applies the BITS bitmask cast
    /// (lane-scoped `BitsIn` for builtin `EReal` lanes).
    /// `SumOf` (explicit `sum e`) intentionally bypasses this and uses SUM.
    fn lower_int_cast(
        &self,
        arena: &mut kk::AstArena,
        e: &Expr,
        env: &mut Env,
    ) -> LResult<IntId> {
        if !self.set_int_flavored(e, env).is_int() {
            return Err(FrontError::Resolve(INT_MISMATCH_MSG.to_string()));
        }
        if self.lane_group_ambiguous(e) {
            return Err(FrontError::Resolve(
                "ambiguous EReal lane: a user field shares this label; qualify explicitly".to_string(),
            ));
        }
        let (ee, _) = self.lower_expr(arena, e, env)?;
        let op = match self.lane_group_of(e) {
            Some(group) => CastToIntOp::BitsIn(group),
            None => CastToIntOp::Bits,
        };
        arena
            .cast_to_int(op, ee)
            .map_err(|e| FrontError::Resolve(e.to_string()))
    }

    fn lower_expr(
        &self,
        arena: &mut kk::AstArena,
        e: &Expr,
        env: &mut Env,
    ) -> LResult<(ExprId, u32)> {
        let lowered = match e {
            Expr::Univ => (arena.constant(kk::ConstantExpr::Univ), 1),
            Expr::None_ => (arena.constant(kk::ConstantExpr::Empty), 1),
            Expr::Iden => (arena.constant(kk::ConstantExpr::Iden), 2),
            Expr::IntAtom => {
                // Bare `Int` as a set value: the union of materialized int
                // atoms (same reading as `:query Int`). Int-as-a-set
                // implies lazy allocation, so the atoms always exist here.
                let w = self.res.int_count;
                let mut acc: Option<ExprId> = None;
                for v in 0..w {
                    let s = self.int_atom_singleton(arena, v as i64)?;
                    acc = Some(match acc {
                        Some(a) => arena
                            .binary_expr(kk::BinaryOp::Union, a, s)
                            .map_err(|e| FrontError::Resolve(e.to_string()))?,
                        None => s,
                    });
                }
                match acc {
                    Some(a) => (a, 1),
                    None => (arena.constant(kk::ConstantExpr::Empty), 1),
                }
            }
            Expr::StepAtom => {
                // Builtin `Step`: the interned unary relation (exact over
                // `Step$*`; empty in static commands).
                if let Some(r) = self.lookup_rel("Step") {
                    let ar = arena.relation_arity(r);
                    return Ok((arena.expr_relation(r), ar));
                }
                // Fallback: union of singletons (query ctx without rels).
                let mut acc: Option<ExprId> = None;
                for a in &self.res.step_atoms {
                    let idx = self.res.universe.index(a).map_err(|e| {
                        FrontError::Resolve(format!("Step atom '{a}' missing: {e}"))
                    })?;
                    let s = arena.expr_atoms(vec![idx]);
                    acc = Some(match acc {
                        Some(x) => arena
                            .binary_expr(kk::BinaryOp::Union, x, s)
                            .map_err(|e| FrontError::Resolve(e.to_string()))?,
                        None => s,
                    });
                }
                match acc {
                    Some(a) => (a, 1),
                    None => (arena.constant(kk::ConstantExpr::Empty), 1),
                }
            }
            Expr::Bits(n, _) => {
                // Bitset of an integer literal: `{i < W : bit i of the
                // E-bit wrap of n is set}` (mirrors
                // `IntCircuit::constant` truncation).
                let w = self.res.int_count as usize;
                let e = self.res.bitwidth;
                let mask: i64 = if e >= 63 { -1 } else { (1i64 << e) - 1 };
                let mut rest = (*n & mask) as u64;
                let mut acc: Option<ExprId> = None;
                while rest != 0 {
                    let i = rest.trailing_zeros() as usize;
                    rest &= rest - 1;
                    if i >= w {
                        continue;
                    }
                    let s = self.int_atom_singleton(arena, i as i64)?;
                    acc = Some(match acc {
                        Some(a) => arena
                            .binary_expr(kk::BinaryOp::Union, a, s)
                            .map_err(|e| FrontError::Resolve(e.to_string()))?,
                        None => s,
                    });
                }
                match acc {
                    Some(a) => (a, 1),
                    None => (arena.constant(kk::ConstantExpr::Empty), 1),
                }
            }
            Expr::RealLit(..) => {
                return Err(FrontError::Resolve(
                    "decimal literals are only valid inside `setEReal`".to_string(),
                ));
            }
            Expr::Name(n, pos) => {
                // Check let-binding scopes (innermost first)
                {
                    let binds = self.let_binds.borrow();
                    for scope in binds.iter().rev() {
                        if let Some(&(eid, a, _)) = scope.get(n) {
                            return Ok((eid, a));
                        }
                    }
                }
                if let Some((_, v, a, _fl)) = env.iter().rev().find(|(nm, ..)| nm == n) {
                    let (v, a) = (*v, *a);
                    return Ok((arena.expr_variable(v), a));
                }
                // Check expression-level bindings (sig fact field qualification)
                if let Some(&(eid, a, _)) = self.expr_binds.borrow().get(n) {
                    return Ok((eid, a));
                }
                if let Some(r) = self.lookup_rel(n) {
                    let ar = arena.relation_arity(r);
                    return Ok((arena.expr_relation(r), ar));
                }
                // Ambiguous field name: union of all matching relations
                let all_hits = self.lookup_rel_all(n);
                if all_hits.len() > 1 {
                    let mut cur = arena.expr_relation(all_hits[0]);
                    let mut car = arena.relation_arity(all_hits[0]);
                    for &r in &all_hits[1..] {
                        let ar = arena.relation_arity(r);
                        let other = arena.expr_relation(r);
                        if ar > car {
                            let univ = arena.constant(kk::ConstantExpr::Univ);
                            for _ in car..ar {
                                cur = arena
                                    .binary_expr(kk::BinaryOp::Product, cur, univ)
                                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                            }
                            car = ar;
                        } else if ar < car {
                            let univ = arena.constant(kk::ConstantExpr::Univ);
                            let mut promoted = other;
                            for _ in ar..car {
                                promoted = arena
                                    .binary_expr(kk::BinaryOp::Product, promoted, univ)
                                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                            }
                            cur = arena
                                .binary_expr(kk::BinaryOp::Union, cur, promoted)
                                .map_err(|e| FrontError::Resolve(e.to_string()))?;
                            continue;
                        }
                        cur = arena
                            .binary_expr(kk::BinaryOp::Union, cur, other)
                            .map_err(|e| FrontError::Resolve(e.to_string()))?;
                    }
                    return Ok((cur, car));
                }
                // ordering builtins without args (e.g., ord/first, ord/last, ord/prev)
                if let Some(result) = self.try_ordering_expr(arena, n, &[], env)? {
                    return Ok(result);
                }
                // zero-arg function reference: inline its body
                if let Some(p) = self
                    .module
                    .paras
                    .iter()
                    .find(|p| p.is_fun && p.name == *n && p.params.is_empty())
                {
                    let body = p
                        .body_expr
                        .clone()
                        .ok_or_else(|| FrontError::Resolve(format!("'{n}' has no body")))?;
                    let d = self.depth.get();
                    if d > 64 {
                        return Err(FrontError::Resolve("call recursion too deep".into()));
                    }
                    self.depth.set(d + 1);
                    let out = self.lower_expr(arena, &body, env)?;
                    self.depth.set(d);
                    return Ok(out);
                }
                // Bit-vector builtins (fallback: declared names win since
                // sigs/fields/lets were checked above).
                if n == "Signed" {
                    return Ok((arena.constant(kk::ConstantExpr::Ints), 1));
                }
                if n == "MSB" {
                    // Sign-bit alias: the top atom index `W - 1`.
                    let w = self.res.int_count;
                    let s = self.int_atom_singleton(arena, (w as i64) - 1)?;
                    return Ok((s, 1));
                }
                // Atom literal (`A$0` in `:query`): a universe atom name
                // denotes its singleton set. Declared names win (checked
                // above), so this is strictly a fallback. Positions are
                // scope-local: re-lowering under another scope re-resolves
                // by name. Model builds reject `$` names (Java parity).
                if self.allow_atoms {
                    if let Ok(idx) = self.res.universe.index(n) {
                        return Ok((arena.expr_atoms(vec![idx]), 1));
                    }
                } else if n.contains('$') {
                    return Err(FrontError::Parse {
                        pos: *pos,
                        msg: "The name cannot contain the '$' symbol.".to_string(),
                    });
                } else if let Ok(idx) = self.res.universe.index(n) {
                    // Numeric int atoms (`5`, `-5`) stay resolvable in
                    // models: they carry no `$`.
                    return Ok((arena.expr_atoms(vec![idx]), 1));
                }
                // A-plan lazy allocation: integer literals in set position need
                // materialized int atoms. On Int-free models the universe
                // has none, so explain instead of a bare "unresolved".
                if n.parse::<i64>().is_ok() {
                    return Err(FrontError::Parse {
                        pos: *pos,
                        msg: format!("integer '{n}' is not in scope (this model materializes no Int atoms; mention Int in the model or add `for N Int` to the scope)"),
                    });
                }
                return Err(FrontError::Parse {
                    pos: *pos,
                    msg: format!(
                        "unresolved name '{}' (env has: {:?})",
                        n,
                        env.iter().map(|(n, ..)| n.as_str()).collect::<Vec<_>>()
                    ),
                });
            }
            Expr::Bin(op, a, b) => {
                let (ea, aa) = self.lower_expr(arena, a, env)?;
                let (eb, ab) = self.lower_expr(arena, b, env)?;
                let id = (match op {
                    BinOp::Join => {
                        if aa + ab < 2 {
                            return Err(FrontError::Resolve(format!(
                                "join arity too small ({aa}.{ab})"
                            )));
                        }
                        arena.binary_expr(kk::BinaryOp::Join, ea, eb)
                    }
                    BinOp::DomainRestrict => {
                        // A <: B = (A × univ^(b-1)) & B
                        // This restricts B to tuples whose first column is in A
                        let bx_ar = ab;
                        let mut ax = ea;
                        let univ = arena.constant(kk::ConstantExpr::Univ);
                        for _ in 1..bx_ar {
                            ax = arena
                                .binary_expr(kk::BinaryOp::Product, ax, univ)
                                .map_err(|e| FrontError::Resolve(e.to_string()))?;
                        }
                        arena.binary_expr(kk::BinaryOp::Intersection, ax, eb)
                    }
                    BinOp::RangeRestrict => {
                        // A :> B = (univ^(a-1) × B) & A
                        // This restricts A to tuples whose last column is in B
                        let ax_ar = aa;
                        let mut bx = eb;
                        let univ = arena.constant(kk::ConstantExpr::Univ);
                        for _ in 1..ax_ar {
                            bx = arena
                                .binary_expr(kk::BinaryOp::Product, univ, bx)
                                .map_err(|e| FrontError::Resolve(e.to_string()))?;
                        }
                        arena.binary_expr(kk::BinaryOp::Intersection, bx, ea)
                    }
                    _ => {
                        // For Union, Intersect, Difference, Override, Product:
                        // Auto-promote lower-arity side with univ padding
                        let kk_op = match op {
                            BinOp::Union => kk::BinaryOp::Union,
                            BinOp::Intersect => kk::BinaryOp::Intersection,
                            BinOp::Difference => kk::BinaryOp::Difference,
                            BinOp::Override => kk::BinaryOp::Override,
                            BinOp::Product => kk::BinaryOp::Product,
                            _ => unreachable!(),
                        };
                        if aa == ab || matches!(op, BinOp::Product) {
                            arena.binary_expr(kk_op, ea, eb)
                        } else if aa < ab {
                            // Promote ea to match eb's arity
                            let mut promoted = ea;
                            let univ = arena.constant(kk::ConstantExpr::Univ);
                            for _ in aa..ab {
                                promoted = arena
                                    .binary_expr(kk::BinaryOp::Product, promoted, univ)
                                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                            }
                            arena.binary_expr(kk_op, promoted, eb)
                        } else {
                            // Promote eb to match ea's arity
                            let mut promoted = eb;
                            let univ = arena.constant(kk::ConstantExpr::Univ);
                            for _ in ab..aa {
                                promoted = arena
                                    .binary_expr(kk::BinaryOp::Product, univ, promoted)
                                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                            }
                            arena.binary_expr(kk_op, ea, promoted)
                        }
                    }
                })
                .map_err(|e| FrontError::Resolve(e.to_string()))?;
                let ar = arena.arity(id);
                let _ = (aa, ab);
                (id, ar)
            }
            Expr::Transpose(x) => {
                let (ex, ax) = self.lower_expr(arena, x, env)?;
                if ax < 2 {
                    return Err(FrontError::Resolve("~ needs arity >= 2".into()));
                }
                let id = arena.unary_expr(kk::UnaryExprOp::Transpose, ex).unwrap();
                (id, ax)
            }
            Expr::TClosure(x) => {
                let (ex, ax) = self.lower_expr(arena, x, env)?;
                if ax < 2 {
                    return Err(FrontError::Resolve("^ needs arity >= 2".into()));
                }
                let id = arena.unary_expr(kk::UnaryExprOp::Closure, ex).unwrap();
                (id, ax)
            }
            Expr::RClosure(x) => {
                let (ex, ax) = self.lower_expr(arena, x, env)?;
                if ax < 2 {
                    return Err(FrontError::Resolve("* needs arity >= 2".into()));
                }
                let id = arena
                    .unary_expr(kk::UnaryExprOp::ReflexiveClosure, ex)
                    .unwrap();
                (id, ax)
            }
            Expr::Comprehension(decls, body) => {
                let disj_pairs = collect_disj_pairs(decls, arena);
                let (ds, pushed) = self.lower_decls(arena, decls, env)?;
                let mut bf = self.lower_formula(arena, body, env)?;
                for &(a, b) in &disj_pairs {
                    let neq = var_neq(arena, a, b);
                    bf = arena.and(&[bf, neq]);
                }
                for _ in 0..pushed {
                    env.pop();
                }
                let id = arena
                    .comprehension(ds, bf)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                (id, arena.arity(id))
            }
            Expr::If(c, t, e2) => {
                let cf = self.lower_formula(arena, c, env)?;
                let (te, ta) = self.lower_expr(arena, t, env)?;
                let (ee, ea) = self.lower_expr(arena, e2, env)?;
                if ta != ea {
                    return Err(FrontError::Resolve(format!(
                        "ite branch arity mismatch {ta} vs {ea}"
                    )));
                }
                let id = arena
                    .if_expr(cf, te, ee)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
                (id, ta)
            }
            Expr::Bracket(base, args) => {
                // Box join slices the FIRST column: `r[a]` == `a.r`.
                let (mut cur, mut car) = self.lower_expr(arena, base, env)?;
                for a in args {
                    let (ai, aa) = self.lower_expr(arena, a, env)?;
                    if car + aa < 2 {
                        return Err(FrontError::Resolve("bracket join arity".into()));
                    }
                    cur = arena
                        .binary_expr(kk::BinaryOp::Join, ai, cur)
                        .map_err(|e| FrontError::Resolve(e.to_string()))?;
                    car = arena.arity(cur);
                }
                (cur, car)
            }
            Expr::ArrowMult(..) | Expr::LeadMult(..) => {
                return self.unsup("multiplicity outside field declaration")
            }
            Expr::Call(name, args, _) => {
                // Check ordering builtins first
                if let Some(result) = self.try_ordering_expr(arena, name, args, env)? {
                    return Ok(result);
                }
                // Check stdlib builtins (graph, relation)
                if let Some(result) = self.try_stdlib_expr(arena, name, args, env)? {
                    return Ok(result);
                }
                if args.is_empty() {
                    if let Some(r) = self.lookup_rel(name) {
                        let ar = arena.relation_arity(r);
                        return Ok((arena.expr_relation(r), ar));
                    }
                }
                // name(args) where name is a relation: treat as bracket indexing
                // Check expr_binds first (sig fact context), then lookup_rel
                if !args.is_empty() {
                    let base = if let Some(&(eid, ea, _fl)) = self.expr_binds.borrow().get(name) {
                        Some((eid, ea))
                    } else {
                        self.lookup_rel(name).map(|r| {
                            let ar = arena.relation_arity(r);
                            (arena.expr_relation(r), ar)
                        })
                    };
                    if let Some((base_e, mut car)) = base {
                        // Box join slices the FIRST column: `r[a]` == `a.r`.
                        let mut cur = base_e;
                        for a in args {
                            let (ai, aa) = self.lower_expr(arena, a, env)?;
                            if car + aa < 2 {
                                return Err(FrontError::Resolve("bracket join arity".into()));
                            }
                            cur = arena
                                .binary_expr(kk::BinaryOp::Join, ai, cur)
                                .map_err(|e| FrontError::Resolve(e.to_string()))?;
                            car = arena.arity(cur);
                        }
                        return Ok((cur, car));
                    }
                }
                let para = self
                    .module
                    .paras
                    .iter()
                    .find(|p| p.name == *name && p.is_fun)
                    .ok_or_else(|| FrontError::Resolve(format!("unknown function '{name}'")))?;
                let total_param_names: usize = para.params.iter().map(|d| d.names.len()).sum();
                if total_param_names != args.len() {
                    return Err(FrontError::Resolve(format!(
                        "'{name}' expects {} args, got {}",
                        total_param_names,
                        args.len()
                    )));
                }
                let d = self.depth.get();
                if d > 64 {
                    return Err(FrontError::Resolve("call recursion too deep".into()));
                }
                self.depth.set(d + 1);
                let mut body = para
                    .body_expr
                    .clone()
                    .ok_or_else(|| FrontError::Resolve(format!("'{name}' has no body")))?;
                let mut arg_idx = 0;
                for pd in &para.params {
                    for pn in &pd.names {
                        body = replace_var_expr(&body, pn, &args[arg_idx]);
                        arg_idx += 1;
                    }
                }
                let out = self.lower_expr(arena, &body, env)?;
                self.depth.set(d);
                out
            }
            Expr::Prime(inner) => {
                let (ex, ax) = self.lower_expr(arena, inner, env)?;
                let id = arena.prime(ex);
                (id, ax)
            }
            Expr::AtExpr(inner) => {
                // @ is static field access - no-op for non-overriding semantics
                self.lower_expr(arena, inner, env)?
            }
            Expr::LetBind(binds, body) => {
                // For each binding, substitute the name with the expression
                // in the body. This avoids creating kodkod variables that
                // won't have FOL env bindings.
                let mut current = (**body).clone();
                for (name, e) in binds.iter().rev() {
                    current = replace_var_expr(&current, name, e);
                }
                self.lower_expr(arena, &current, env)?
            }
        };
        Ok(lowered)
    }

    /// Lowers decl list, pushing new env entries; returns count pushed.
    fn lower_decls(
        &self,
        arena: &mut kk::AstArena,
        decls: &[Decl],
        env: &mut Env,
    ) -> LResult<(kk::DeclsId, usize)> {
        if decls.len() > 1 && decls.iter().any(|d| d.disj) {
            // disj across groups unsupported for now
        }
        let mut list = Vec::new();
        let mut pushed = 0usize;
        for d in decls {
            let domain_int = self.set_int_flavored(&d.expr, env);
            let (dom, _da) = self.lower_expr(arena, &d.expr, env)?;
            for n in &d.names {
                let v = arena.variable(n);
                let da = arena.decl(v, Multiplicity::One, dom).map_err(|e| {
                    FrontError::Resolve(format!(
                        "quantifier '{n}': {e} (higher-order quantification over \
                         non-unary domains is not supported)"
                    ))
                })?;
                list.push(da);
                env.push((n.clone(), v, arena.variable_arity(v), domain_int));
                pushed += 1;
            }
        }
        Ok((arena.add_decls(list), pushed))
    }

    fn lower_int(&self, arena: &mut kk::AstArena, ie: &IntExpr, env: &mut Env) -> LResult<IntId> {
        Ok(match ie {
            IntExpr::Lit(v, _) => arena.int_constant(*v),
            IntExpr::Card(e, _) => {
                let (ee, _) = self.lower_expr(arena, e, env)?;
                arena.cast_to_int(CastToIntOp::Cardinality, ee).unwrap()
            }
            IntExpr::SumOf(e, _) => {
                // Explicit `sum e`: Σ of the int-atom VALUES via the SUM
                // cast (`sum {0, 1}` is 1 — distinct from the bitmask 3).
                // Lane sets (`x.m`) have no meaningful atom-value sum
                // (positions, not values); reject loudly instead of
                // silently reading 0.
                if self.lane_group_of(e).is_some() {
                    return Err(FrontError::Resolve(
                        "sum over EReal lanes is unsupported (positions are not values)".to_string(),
                    ));
                }
                let (ee, _) = self.lower_expr(arena, e, env)?;
                arena
                    .cast_to_int(CastToIntOp::Sum, ee)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?
            }
            IntExpr::Val(e, _) | IntExpr::BitsVal(e, _) => {
                self.lower_int_cast(arena, e, env)?
            }
            IntExpr::Sum(decls, body, _) => {
                if decls.iter().any(|d| d.disj && d.names.len() > 1) {
                    return self.unsup("`disj` in sum declarations");
                }
                let (ds, pushed) = self.lower_decls(arena, decls, env)?;
                let b = self.lower_int(arena, body, env)?;
                for _ in 0..pushed {
                    env.pop();
                }
                arena.sum_int(ds, b)
            }
            IntExpr::Bin(op, a, b) => {
                let ia = self.lower_int(arena, a, env)?;
                let ib = self.lower_int(arena, b, env)?;
                let kop = match op {
                    IntBinOp::Add => kk::IntBinOp::Plus,
                    IntBinOp::Sub => kk::IntBinOp::Minus,
                    IntBinOp::Mul => kk::IntBinOp::Times,
                    IntBinOp::Div => kk::IntBinOp::Divide,
                    IntBinOp::Rem => kk::IntBinOp::Modulo,
                };
                arena.binary_int(kop, ia, ib)
            }
        })
    }

    /// Desugar `pin P` to `some x1: D1, ... | <entry comparisons>`.
    ///
    /// Each distinct label `Sig$tag` becomes a fresh variable over the
    /// sig's atoms (`$pin{n}_Sig_tag`, un-collidable since `$` is banned
    /// in user bindings); same-prefix labels get pairwise `!=`. Entries
    /// normalize by label presence and comparison orientation:
    /// `R = S` (exact), `L in R` (lower), `R in S` (upper), plus the
    /// `R = none` exact-empty special case.
    fn lower_pin(
        &self,
        arena: &mut kk::AstArena,
        name: &str,
        pos: usize,
        env: &mut Env,
    ) -> LResult<FormulaId> {
        let pd = self
            .module
            .partials
            .iter()
            .find(|p| p.name == name)
            .ok_or_else(|| FrontError::Resolve(format!("unknown partial '{name}'")))?;
        let _ = pos;
        // Distinct labels in first-seen order: (prefix, tag, full).
        let mut labels: Vec<(String, String, String)> = Vec::new();
        for e in &pd.entries {
            collect_pin_labels(&e.left, &mut labels)?;
            collect_pin_labels(&e.right, &mut labels)?;
        }
        // Mint gensym variables and bind label names in `env` so the
        // entry expressions lower with variables in label positions.
        let base = self.pin_seq.get();
        self.pin_seq.set(base + labels.len() as u32);
        let mut decl_list = Vec::new();
        let mut pushed = 0usize;
        let mut var_of: HashMap<String, kk::VarId> = HashMap::new();
        for (i, (prefix, tag, full)) in labels.iter().enumerate() {
            if !self
                .module
                .sigs
                .iter()
                .flat_map(|s| s.names.iter())
                .any(|n| n == prefix)
            {
                return Err(FrontError::Resolve(format!(
                    "unknown sig prefix '{prefix}' in partial label '{full}'"
                )));
            }
            let vname = format!("$pin{}_{}_{}", base + i as u32, prefix, tag);
            let (dom, _) = self
                .lower_expr(arena, &Expr::Name(prefix.clone(), pd.pos), env)
                .map_err(|_| {
                    FrontError::Resolve(format!(
                        "unknown sig prefix '{prefix}' in partial label '{full}'"
                    ))
                })?;
            let v = arena.variable(&vname);
            let da = arena
                .decl(v, Multiplicity::One, dom)
                .map_err(|e| FrontError::Resolve(e.to_string()))?;
            decl_list.push(da);
            let int_flavor = self.set_int_flavored(&Expr::Name(prefix.clone(), pd.pos), env);
            env.push((full.clone(), v, 1, int_flavor));
            pushed += 1;
            var_of.insert(full.clone(), v);
        }
        // Normalize + lower every entry, then conjoin.
        let mut parts: Vec<FormulaId> = Vec::new();
        for e in &pd.entries {
            let norm = self.normalize_pin_entry(&e.left, &e.right, e.op, &pd.name, e.pos)?;
            let (le, _) = self.lower_expr(arena, norm.left, env)?;
            let (re, _) = self.lower_expr(arena, norm.right, env)?;
            // Normalization only ever yields `Eq`/`In`.
            let kop = match norm.cmp {
                CmpKind::Eq => ExprCompOp::Equals,
                CmpKind::In => ExprCompOp::Subset,
                CmpKind::Neq | CmpKind::NotIn => {
                    return self.unsup("partial entry comparison");
                }
            };
            parts.push(
                arena
                    .comparison(kop, le, re)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?,
            );
        }
        // Same-prefix labels denote distinct atoms.
        let mut by_prefix: HashMap<&str, Vec<kk::VarId>> = HashMap::new();
        for (prefix, _, full) in &labels {
            by_prefix
                .entry(prefix.as_str())
                .or_default()
                .push(var_of[full.as_str()]);
        }
        for vars in by_prefix.values() {
            for i in 0..vars.len() {
                for j in i + 1..vars.len() {
                    parts.push(var_neq(arena, vars[i], vars[j]));
                }
            }
        }
        for _ in 0..pushed {
            env.pop();
        }
        let body = arena.and(&parts);
        let ds = arena.add_decls(decl_list);
        Ok(arena.quantified(Quantifier::Some, ds, body))
    }

    /// Decide which side of a `partial` entry is the relation and which
    /// is the label set, by label presence and comparison orientation.
    /// Returns the comparison to build with operands already in order:
    /// `=` (exact, either orientation), `L in R` (lower), `R in S`
    /// (upper), plus the `R = none` exact-empty special case.
    fn normalize_pin_entry<'e>(
        &self,
        left: &'e Expr,
        right: &'e Expr,
        op: PartialOp,
        pname: &str,
        pos: usize,
    ) -> LResult<PinNorm<'e>> {
        let _ = pos;
        let lh = expr_has_label(left);
        let rh = expr_has_label(right);
        // Exact-empty: `R = none` (either orientation).
        if op == PartialOp::Eq && (matches!(left, Expr::None_) ^ matches!(right, Expr::None_)) {
            let (rel, none) = if matches!(left, Expr::None_) {
                (right, left)
            } else {
                (left, right)
            };
            if expr_has_label(rel) {
                return Err(FrontError::Resolve(format!(
                    "partial '{pname}': label cannot equal `none`"
                )));
            }
            return Ok(PinNorm {
                cmp: CmpKind::Eq,
                left: rel,
                right: none,
            });
        }
        match (op, lh, rh) {
            (PartialOp::Eq, false, true) | (PartialOp::Eq, true, false) => {
                let (rel, set) = if lh { (right, left) } else { (left, right) };
                Ok(PinNorm {
                    cmp: CmpKind::Eq,
                    left: rel,
                    right: set,
                })
            }
            // Lower: label set on the left.
            (PartialOp::In, true, false) => Ok(PinNorm {
                cmp: CmpKind::In,
                left,
                right,
            }),
            // Upper: label set on the right.
            (PartialOp::In, false, true) => Ok(PinNorm {
                cmp: CmpKind::In,
                left,
                right,
            }),
            (PartialOp::Eq, _, _) => Err(FrontError::Resolve(format!(
                "partial '{pname}': `=` needs labels on exactly one side"
            ))),
            (PartialOp::In, _, _) => Err(FrontError::Resolve(format!(
                "partial '{pname}': `in` needs labels on exactly one side"
            ))),
        }
    }

    fn lower_formula(
        &self,
        arena: &mut kk::AstArena,
        f: &Formula,
        env: &mut Env,
    ) -> LResult<FormulaId> {
        Ok(match f {
            Formula::Const(v) => arena.bool_formula(*v),
            // `n in set` with an integer left side: type mismatch (`in`
            // requires set operands on both sides). Reported at lowering.
            Formula::BadIn(..) => {
                return Err(FrontError::Parse {
                    pos: 0,
                    msg: "type mismatch: integer expression cannot appear left of `in` (both sides must be sets, e.g. `{0, 2} in X`)".to_string(),
                });
            }
            Formula::Not(x) => {
                let inner = self.lower_formula(arena, x, env)?;
                arena.not(inner)
            }
            Formula::And(a, b) => {
                let (fa, fb) = (
                    self.lower_formula(arena, a, env)?,
                    self.lower_formula(arena, b, env)?,
                );
                arena.and(&[fa, fb])
            }
            Formula::Or(a, b) => {
                let (fa, fb) = (
                    self.lower_formula(arena, a, env)?,
                    self.lower_formula(arena, b, env)?,
                );
                arena.or(&[fa, fb])
            }
            Formula::Implies(a, b) => {
                let fa = self.lower_formula(arena, a, env)?;
                let na = arena.not(fa);
                let fb = self.lower_formula(arena, b, env)?;
                arena.or(&[na, fb])
            }
            Formula::Iff(a, b) => {
                let fa = self.lower_formula(arena, a, env)?;
                let fb = self.lower_formula(arena, b, env)?;
                let both = arena.and(&[fa, fb]);
                let na = arena.not(fa);
                let nb = arena.not(fb);
                let neither = arena.and(&[na, nb]);
                arena.or(&[both, neither])
            }
            Formula::Call(name, args, pos) => {
                // `totalOrder[S, S.next]`: order fixing is applied via
                // exact bounds on the binary links (i.e. `S<:next`);
                // the formula itself is true.
                if name == "totalOrder" {
                    if args.len() != 2 {
                        return Err(FrontError::Resolve(format!(
                            "'totalOrder' expects 2 args, got {}",
                            args.len()
                        )));
                    }
                    if total_order_target(&args[0], &args[1]).is_none() {
                        return Err(FrontError::Resolve(
                            "'totalOrder' expects (S, S<:f) or (S, S.f) or (S, f)".into(),
                        ));
                    }
                    return Ok(arena.bool_formula(true));
                }
                // Check ordering builtins first
                if let Some(f) = self.try_ordering_pred(arena, name, args, env)? {
                    return Ok(f);
                }
                // Builtin `EReal` predicates (desugared to lane constraints).
                if let Some(f) = self.try_ereal_pred(arena, name, args, env)? {
                    return Ok(f);
                }
                // Check stdlib builtins (graph, relation)
                if let Some(f) = self.try_stdlib_pred(arena, name, args, env)? {
                    return Ok(f);
                }
                // Field fallback: `a.f[b]` as a formula means `some a.f[b]`.
                let is_pred = self
                    .module
                    .paras
                    .iter()
                    .any(|p| p.name == *name && !p.is_fun);
                if !is_pred && self.lookup_rel(name).is_some() {
                    let base = Expr::Call(name.clone(), Vec::new(), *pos);
                    let e = Expr::Bracket(
                        Box::new(base),
                        args.iter().map(|a| Box::new(a.clone())).collect(),
                    );
                    let (ee, _) = self.lower_expr(arena, &e, env)?;
                    let mf = arena.multiplicity_formula(Multiplicity::Some, ee).unwrap();
                    return Ok(mf);
                }
                let para = self
                    .module
                    .paras
                    .iter()
                    .find(|p| p.name == *name && !p.is_fun)
                    .ok_or_else(|| FrontError::Resolve(format!("unknown predicate '{name}'")))?;
                // Flatten multi-name declarations: "t, t\": Type" counts as 2 params
                let total_param_names: usize = para.params.iter().map(|d| d.names.len()).sum();
                if total_param_names != args.len() {
                    return Err(FrontError::Resolve(format!(
                        "'{name}' expects {} args, got {}",
                        total_param_names,
                        args.len()
                    )));
                }
                let d = self.depth.get();
                if d > 64 {
                    return Err(FrontError::Resolve("call recursion too deep".into()));
                }
                self.depth.set(d + 1);
                let mut body = para.body.clone();
                let mut arg_idx = 0;
                for pd in &para.params {
                    for pn in &pd.names {
                        body = replace_var_formula(&body, pn, &args[arg_idx]);
                        arg_idx += 1;
                    }
                }
                let out = self.lower_formula(arena, &body, env)?;
                self.depth.set(d);
                out
            }
            Formula::LetBind(binds, body) => {
                let mut scope = HashMap::new();
                for (name, e) in binds {
                    let (ee, ea) = self.lower_expr(arena, e, env)?;
                    // Formula-level `let` keeps the legacy lenient flavor
                    // (historically `true`); revisit when gradual
                    // strictness assigns real flavors here.
                    scope.insert(name.clone(), (ee, ea, SetKind::Int));
                }
                self.let_binds.borrow_mut().push(scope);
                let bf = self.lower_formula(arena, body, env)?;
                self.let_binds.borrow_mut().pop();
                bf
            }
            // `pin P`: embed the named partial instance by desugaring to
            // an existential over gensym label variables (`avoid P` is
            // already wrapped in `Not` by the parser).
            Formula::Pin(name, pos) => self.lower_pin(arena, name, *pos, env)?,
            // AlloyMax soft set optimization: lower the set expression
            // in the current environment; the kodkod layer records unit
            // softs per cell during FOL translation. Hard meaning: true.
            Formula::MaxSome(e) => {
                let (ee, _) = self.lower_expr(arena, e, env)?;
                arena.maxsome(ee)
            }
            Formula::MaxSomeDecl(..) => {
                return self.unsup(
                    "'maxsome x: T | F' declaration form needs free set-valued \
                     witnesses, which are not supported (use 'maxsome <expr>')",
                );
            }
            Formula::MinSome(e) => {
                let (ee, _) = self.lower_expr(arena, e, env)?;
                arena.minsome(ee)
            }
            // `some/no Overflow` markers only live at the top level of a
            // `run`/`check` body (consumed by `prepare_command`); anywhere
            // else they are rejected here.
            Formula::OverflowCond(..) => {
                return Err(FrontError::Resolve(
                    "`some/no Overflow` is only allowed at the top level of a `run`/`check` body (nested uses are not yet supported)".to_string(),
                ));
            }
            // In-body `maximize`/`minimize` markers: the target becomes
            // the command's objective (collected here with the enclosing
            // trace state, if any); hard meaning is true.
            Formula::Maximize(ie) => {
                let target = self.lower_int(arena, ie, env)?;
                self.markers.borrow_mut().push(OptMarker {
                    target,
                    sense: OptSense::Maximize,
                    time: self.marker_time.get(),
                });
                arena.bool_formula(true)
            }
            Formula::Minimize(ie) => {
                let target = self.lower_int(arena, ie, env)?;
                self.markers.borrow_mut().push(OptMarker {
                    target,
                    sense: OptSense::Minimize,
                    time: self.marker_time.get(),
                });
                arena.bool_formula(true)
            }
            Formula::Cmp(kind, l, r, _) => {
                // Lane-vs-literal equality (`x.m = 3`): the parser reads
                // this relationally (literal as an Int-atom bitset, whose
                // domain never meets the lane atoms), so rewrite to the
                // integer reading (`BitsIn` vs literal). Other shapes keep
                // the legacy relational reading.
                if matches!(kind, CmpKind::Eq | CmpKind::Neq) {
                    if let Some(rw) = self.rewrite_lane_lit_cmp(kind, l, r)? {
                        return self.lower_formula(arena, &rw, env);
                    }
                }
                let (el, al) = self.lower_expr(arena, l, env)?;
                let (er, ar) = self.lower_expr(arena, r, env)?;
                // Auto-promote lower arity side for comparisons
                let (el, er) = if al < ar {
                    let mut promoted = el;
                    let univ = arena.constant(kk::ConstantExpr::Univ);
                    for _ in al..ar {
                        promoted = arena
                            .binary_expr(kk::BinaryOp::Product, promoted, univ)
                            .map_err(|e| FrontError::Resolve(e.to_string()))?;
                    }
                    (promoted, er)
                } else if ar < al {
                    let mut promoted = er;
                    let univ = arena.constant(kk::ConstantExpr::Univ);
                    for _ in ar..al {
                        promoted = arena
                            .binary_expr(kk::BinaryOp::Product, univ, promoted)
                            .map_err(|e| FrontError::Resolve(e.to_string()))?;
                    }
                    (el, promoted)
                } else {
                    (el, er)
                };
                let final_ar = arena.arity(el);
                let final_ar2 = arena.arity(er);
                let base = match kind {
                    CmpKind::Eq | CmpKind::Neq => {
                        arena.comparison(ExprCompOp::Equals, el, er)
                            .map_err(|e| FrontError::Resolve(format!("{e} (final arities: {final_ar} vs {final_ar2}, original: {al} vs {ar})")))?
                    }
                    CmpKind::In | CmpKind::NotIn => {
                        arena.comparison(ExprCompOp::Subset, el, er)
                            .map_err(|e| FrontError::Resolve(e.to_string()))?
                    }
                };
                match kind {
                    CmpKind::Neq | CmpKind::NotIn => arena.not(base),
                    _ => base,
                }
            }
            Formula::IntCmp(op, l, r, _) => {
                let il = self.lower_int(arena, l, env)?;
                let ir = self.lower_int(arena, r, env)?;
                let kop = match op {
                    IntCmpOp::Eq => kk::IntCompOp::Eq,
                    IntCmpOp::Neq => kk::IntCompOp::Neq,
                    IntCmpOp::Lt => kk::IntCompOp::Lt,
                    IntCmpOp::Gt => kk::IntCompOp::Gt,
                    IntCmpOp::Lte => kk::IntCompOp::Lte,
                    IntCmpOp::Gte => kk::IntCompOp::Gte,
                };
                arena.int_comparison(kop, il, ir)
            }
            Formula::Multi(kind, e, _) => {
                let (ee, _) = self.lower_expr(arena, e, env)?;
                let m = match kind {
                    QuantKind::Some => Multiplicity::Some,
                    QuantKind::Lone => Multiplicity::Lone,
                    QuantKind::One => Multiplicity::One,
                    QuantKind::All => return self.unsup("'all' without body"),
                    QuantKind::No => {
                        let sf = arena.multiplicity_formula(Multiplicity::Some, ee).unwrap();
                        return Ok(arena.not(sf));
                    }
                };
                arena.multiplicity_formula(m, ee).unwrap()
            }
            Formula::Quant(kind, decls, body) => {
                match kind {
                    QuantKind::All | QuantKind::Some => {
                        let q = if *kind == QuantKind::All {
                            Quantifier::All
                        } else {
                            Quantifier::Some
                        };
                        // `disj` groups contribute x != y conjuncts/guards
                        let disj_pairs = collect_disj_pairs(decls, arena);
                        let (ds, pushed) = self.lower_decls(arena, decls, env)?;
                        let mut bf = self.lower_formula(arena, body, env)?;
                        for _ in 0..pushed {
                            env.pop();
                        }
                        for &(a, b) in &disj_pairs {
                            let neq = var_neq(arena, a, b);
                            if *kind == QuantKind::All {
                                // all disj x,y | F  ==  all x,y | x!=y => F
                                let nb = arena.not(neq);
                                bf = arena.or(&[nb, bf]);
                            } else {
                                // some disj x,y | F  ==  some x,y | F && x!=y
                                bf = arena.and(&[bf, neq]);
                            }
                        }
                        arena.quantified(q, ds, bf)
                    }
                    QuantKind::No => {
                        let inner = Formula::Quant(QuantKind::Some, decls.clone(), body.clone());
                        let sf = self.lower_formula(arena, &inner, env)?;
                        arena.not(sf)
                    }
                    QuantKind::Lone | QuantKind::One => {
                        // lone x: D | F  ==  not some disj pairs both satisfying F
                        // one x: D | F  ==  some x: D | F  and  lone x: D | F
                        if decls.len() != 1 || decls[0].names.len() != 1 || decls[0].disj {
                            return self.unsup("lone/one quantifier shape");
                        }
                        let name = decls[0].names[0].clone();
                        let alt = format!("{}'", name);
                        let second = subst_formula(body, &name, &alt);
                        // decls for x' reuse same domain
                        let mut ds2 = decls.clone();
                        ds2[0].names = vec![alt.clone()];
                        let neq = Formula::Cmp(
                            CmpKind::Neq,
                            Expr::Name(name.clone(), 0),
                            Expr::Name(alt.clone(), 0),
                            0,
                        );
                        let pair_body = Formula::And(
                            Box::new((**body).clone()),
                            Box::new(Formula::And(Box::new(second), Box::new(neq))),
                        );
                        let two = Formula::Quant(
                            QuantKind::Some,
                            vec![
                                decls[0].clone(),
                                Decl {
                                    disj: false,
                                    names: vec![alt],
                                    expr: decls[0].expr.clone(),
                                    pos: decls[0].pos,
                                    is_var: false,
                                },
                            ],
                            Box::new(pair_body),
                        );
                        let _ = ds2;
                        let two_f = self.lower_formula(arena, &two, env)?;
                        let not_two = arena.not(two_f);
                        if *kind == QuantKind::Lone {
                            return Ok(not_two);
                        }
                        let some1 = self.lower_formula(
                            arena,
                            &Formula::Quant(
                                QuantKind::Some,
                                decls.clone(),
                                Box::new((**body).clone()),
                            ),
                            env,
                        )?;
                        arena.and(&[some1, not_two])
                    }
                }
            }
            Formula::Always(inner) => {
                let f = self.lower_formula(arena, inner, env)?;
                arena.temporal_unary(kk::TemporalFormulaOp::Always, f)
            }
            Formula::Eventually(inner) => {
                let f = self.lower_formula(arena, inner, env)?;
                arena.temporal_unary(kk::TemporalFormulaOp::Eventually, f)
            }
            Formula::Until(left, right) => {
                let fl = self.lower_formula(arena, left, env)?;
                let fr = self.lower_formula(arena, right, env)?;
                arena.temporal_binary(kk::TemporalBinaryOp::Until, fl, fr)
            }
            Formula::Releases(left, right) => {
                let fl = self.lower_formula(arena, left, env)?;
                let fr = self.lower_formula(arena, right, env)?;
                arena.temporal_binary(kk::TemporalBinaryOp::Releases, fl, fr)
            }
            Formula::Before(inner) => {
                let f = self.lower_formula(arena, inner, env)?;
                arena.temporal_unary(kk::TemporalFormulaOp::Before, f)
            }
            Formula::Historically(inner) => {
                let f = self.lower_formula(arena, inner, env)?;
                arena.temporal_unary(kk::TemporalFormulaOp::Historically, f)
            }
            Formula::Once(inner) => {
                let f = self.lower_formula(arena, inner, env)?;
                arena.temporal_unary(kk::TemporalFormulaOp::Once, f)
            }
            Formula::Since(left, right) => {
                let fl = self.lower_formula(arena, left, env)?;
                let fr = self.lower_formula(arena, right, env)?;
                arena.temporal_binary(kk::TemporalBinaryOp::Since, fl, fr)
            }
            Formula::Triggered(left, right) => {
                let fl = self.lower_formula(arena, left, env)?;
                let fr = self.lower_formula(arena, right, env)?;
                arena.temporal_binary(kk::TemporalBinaryOp::Triggered, fl, fr)
            }
            Formula::Keeping(inner) => {
                let f = self.lower_formula(arena, inner, env)?;
                arena.temporal_unary(kk::TemporalFormulaOp::Keeping, f)
            }
            Formula::Goal(inner) => {
                // Markers inside take the goal (last) state; restore the
                // outer context afterwards (innermost operator wins).
                let prev = self.marker_time.replace(Some(TimePoint::Last));
                let f = self.lower_formula(arena, inner, env)?;
                self.marker_time.set(prev);
                arena.temporal_unary(kk::TemporalFormulaOp::Goal, f)
            }
            Formula::Restore(inner) => {
                let prev = self.marker_time.replace(Some(TimePoint::Loop));
                let f = self.lower_formula(arena, inner, env)?;
                self.marker_time.set(prev);
                arena.temporal_unary(kk::TemporalFormulaOp::Restore, f)
            }
            Formula::Initially(inner) => {
                let prev = self.marker_time.replace(Some(TimePoint::First));
                let f = self.lower_formula(arena, inner, env)?;
                self.marker_time.set(prev);
                arena.temporal_unary(kk::TemporalFormulaOp::Initially, f)
            }
            Formula::Regularly(inner) => {
                let f = self.lower_formula(arena, inner, env)?;
                arena.temporal_unary(kk::TemporalFormulaOp::Regularly, f)
            }
            Formula::Consistently(inner) => {
                let f = self.lower_formula(arena, inner, env)?;
                arena.temporal_unary(kk::TemporalFormulaOp::Consistently, f)
            }
        })
    }
}

/// A normalized `partial` entry: comparison operands already in order.
struct PinNorm<'e> {
    cmp: CmpKind,
    left: &'e Expr,
    right: &'e Expr,
}

/// True when `e` mentions any `Sig$tag` label. Entries use the
/// restricted shape (names, `none`, `+`, `->`), so anything else is
/// label-free here (it was rejected at parse time).
fn expr_has_label(e: &Expr) -> bool {
    match e {
        Expr::Name(n, _) => n.contains('$'),
        Expr::Bin(_, a, b) => expr_has_label(a) || expr_has_label(b),
        _ => false,
    }
}

/// A label tag follows plain identifier rules (`$` excluded): leading
/// letter/`_`, then alphanumerics/`_`/`'`.
fn valid_pin_tag(tag: &str) -> bool {
    let mut cs = tag.chars();
    match cs.next() {
        Some(c) if c.is_ascii_alphabetic() || c == '_' => {}
        _ => return false,
    }
    cs.all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '\'')
}

/// Collect distinct `(prefix, tag, full)` labels in first-seen order.
/// Anything that is not a well-formed `Sig$tag` label is an error here
/// (the `$` declaration ban keeps user bindings out of this path).
fn collect_pin_labels(e: &Expr, out: &mut Vec<(String, String, String)>) -> LResult<()> {
    match e {
        Expr::Name(n, pos) => {
            if let Some((prefix, tag)) = n.split_once('$') {
                if prefix.is_empty() || !valid_pin_tag(tag) {
                    return Err(FrontError::Parse {
                        pos: *pos,
                        msg: format!("malformed partial label '{n}' (want `Sig$tag`)"),
                    });
                }
                if !out.iter().any(|(p, t, _)| p == prefix && t == tag) {
                    out.push((prefix.to_string(), tag.to_string(), n.clone()));
                }
            }
            Ok(())
        }
        Expr::Bin(_, a, b) => {
            collect_pin_labels(a, out)?;
            collect_pin_labels(b, out)
        }
        // Restricted entry grammar guarantees nothing else carries
        // labels; other shapes were rejected at parse time.
        _ => Ok(()),
    }
}

/// Textual variable renaming used by lone/one desugaring; stops at
/// shadowing redeclarations of `from`.
fn subst_formula(f: &Formula, from: &str, to: &str) -> Formula {
    match f {
        Formula::Const(v) => Formula::Const(*v),
        // `pin` names a partial block, not a variable: untouched.
        Formula::Pin(name, pos) => Formula::Pin(name.clone(), *pos),
        Formula::MaxSome(e) => Formula::MaxSome(Box::new(subst_expr(e, from, to))),
        Formula::MinSome(e) => Formula::MinSome(Box::new(subst_expr(e, from, to))),
        Formula::OverflowCond(m, body) => {
            Formula::OverflowCond(*m, Box::new(subst_formula(body, from, to)))
        }
        Formula::Maximize(ie) => Formula::Maximize(subst_int(ie, from, to)),
        Formula::Minimize(ie) => Formula::Minimize(subst_int(ie, from, to)),
        Formula::MaxSomeDecl(ds, body) => {
            let nd = ds
                .iter()
                .map(|d| crate::ast::Decl {
                    disj: d.disj,
                    names: d.names.clone(),
                    expr: subst_expr(&d.expr, from, to),
                    pos: d.pos,
                    is_var: d.is_var,
                })
                .collect();
            Formula::MaxSomeDecl(nd, Box::new(subst_formula(body, from, to)))
        }
        Formula::Not(x) => Formula::Not(Box::new(subst_formula(x, from, to))),
        Formula::And(a, b) => Formula::And(
            Box::new(subst_formula(a, from, to)),
            Box::new(subst_formula(b, from, to)),
        ),
        Formula::Or(a, b) => Formula::Or(
            Box::new(subst_formula(a, from, to)),
            Box::new(subst_formula(b, from, to)),
        ),
        Formula::Implies(a, b) => Formula::Implies(
            Box::new(subst_formula(a, from, to)),
            Box::new(subst_formula(b, from, to)),
        ),
        Formula::Iff(a, b) => Formula::Iff(
            Box::new(subst_formula(a, from, to)),
            Box::new(subst_formula(b, from, to)),
        ),
        Formula::Cmp(k, a, b, p) => {
            Formula::Cmp(*k, subst_expr(a, from, to), subst_expr(b, from, to), *p)
        }
        Formula::BadIn(a, p) => Formula::BadIn(Box::new(subst_expr(a, from, to)), *p),
        Formula::IntCmp(op, a, b, p) => {
            Formula::IntCmp(*op, subst_int(a, from, to), subst_int(b, from, to), *p)
        }
        Formula::Multi(k, e, p) => Formula::Multi(*k, subst_expr(e, from, to), *p),
        Formula::Quant(k, decls, body) => {
            let shadows = decls.iter().any(|d| d.names.iter().any(|n| n == from));
            if shadows {
                f.clone()
            } else {
                let nd = decls
                    .iter()
                    .map(|d| Decl {
                        disj: d.disj,
                        names: d.names.clone(),
                        expr: subst_expr(&d.expr, from, to),
                        pos: d.pos,
                        is_var: d.is_var,
                    })
                    .collect();
                Formula::Quant(*k, nd, Box::new(subst_formula(body, from, to)))
            }
        }
        Formula::LetBind(binds, body) => {
            if binds.iter().any(|(n, _)| n == from) {
                f.clone()
            } else {
                Formula::LetBind(
                    binds
                        .iter()
                        .map(|(n, e)| (n.clone(), subst_expr(e, from, to)))
                        .collect(),
                    Box::new(subst_formula(body, from, to)),
                )
            }
        }
        Formula::Call(name, args, p) => Formula::Call(
            name.clone(),
            args.iter().map(|a| subst_expr(a, from, to)).collect(),
            *p,
        ),
        Formula::Always(inner) => Formula::Always(Box::new(subst_formula(inner, from, to))),
        Formula::Eventually(inner) => Formula::Eventually(Box::new(subst_formula(inner, from, to))),
        Formula::Until(a, b) => Formula::Until(
            Box::new(subst_formula(a, from, to)),
            Box::new(subst_formula(b, from, to)),
        ),
        Formula::Releases(a, b) => Formula::Releases(
            Box::new(subst_formula(a, from, to)),
            Box::new(subst_formula(b, from, to)),
        ),
        Formula::Before(inner) => Formula::Before(Box::new(subst_formula(inner, from, to))),
        Formula::Historically(inner) => {
            Formula::Historically(Box::new(subst_formula(inner, from, to)))
        }
        Formula::Once(inner) => Formula::Once(Box::new(subst_formula(inner, from, to))),
        Formula::Since(a, b) => Formula::Since(
            Box::new(subst_formula(a, from, to)),
            Box::new(subst_formula(b, from, to)),
        ),
        Formula::Triggered(a, b) => Formula::Triggered(
            Box::new(subst_formula(a, from, to)),
            Box::new(subst_formula(b, from, to)),
        ),
        Formula::Keeping(inner) => Formula::Keeping(Box::new(subst_formula(inner, from, to))),
        Formula::Goal(inner) => Formula::Goal(Box::new(subst_formula(inner, from, to))),
        Formula::Restore(inner) => Formula::Restore(Box::new(subst_formula(inner, from, to))),
        Formula::Initially(inner) => Formula::Initially(Box::new(subst_formula(inner, from, to))),
        Formula::Regularly(inner) => Formula::Regularly(Box::new(subst_formula(inner, from, to))),
        Formula::Consistently(inner) => {
            Formula::Consistently(Box::new(subst_formula(inner, from, to)))
        }
    }
}

fn subst_expr(e: &Expr, from: &str, to: &str) -> Expr {
    match e {
        Expr::Name(n, p) if n == from => Expr::Name(to.to_string(), *p),
        Expr::Name(..) | Expr::Univ | Expr::None_ | Expr::Iden | Expr::IntAtom | Expr::StepAtom | Expr::Bits(..) | Expr::RealLit(..) => {
            e.clone()
        }
        Expr::Bin(op, a, b) => Expr::Bin(
            *op,
            Box::new(subst_expr(a, from, to)),
            Box::new(subst_expr(b, from, to)),
        ),
        Expr::Transpose(x) => Expr::Transpose(Box::new(subst_expr(x, from, to))),
        Expr::TClosure(x) => Expr::TClosure(Box::new(subst_expr(x, from, to))),
        Expr::RClosure(x) => Expr::RClosure(Box::new(subst_expr(x, from, to))),
        Expr::Comprehension(decls, body) => {
            let shadows = decls.iter().any(|d| d.names.iter().any(|n| n == from));
            if shadows {
                e.clone()
            } else {
                Expr::Comprehension(
                    decls
                        .iter()
                        .map(|d| Decl {
                            disj: d.disj,
                            names: d.names.clone(),
                            expr: subst_expr(&d.expr, from, to),
                            pos: d.pos,
                            is_var: d.is_var,
                        })
                        .collect(),
                    Box::new(subst_formula(body, from, to)),
                )
            }
        }
        Expr::If(c, t, e2) => Expr::If(
            Box::new(subst_formula(c, from, to)),
            Box::new(subst_expr(t, from, to)),
            Box::new(subst_expr(e2, from, to)),
        ),
        Expr::Bracket(b, args) => Expr::Bracket(
            Box::new(subst_expr(b, from, to)),
            args.iter()
                .map(|a| Box::new(subst_expr(a, from, to)))
                .collect(),
        ),
        Expr::ArrowMult(m, x) => Expr::ArrowMult(*m, Box::new(subst_expr(x, from, to))),
        Expr::LeadMult(m, x) => Expr::LeadMult(*m, Box::new(subst_expr(x, from, to))),
        Expr::Call(name, args, p) => Expr::Call(
            name.clone(),
            args.iter().map(|a| subst_expr(a, from, to)).collect(),
            *p,
        ),
        Expr::Prime(inner) => Expr::Prime(Box::new(subst_expr(inner, from, to))),
        Expr::AtExpr(inner) => Expr::AtExpr(Box::new(subst_expr(inner, from, to))),
        Expr::LetBind(binds, body) => Expr::LetBind(
            binds
                .iter()
                .map(|(n, e)| (n.clone(), subst_expr(e, from, to)))
                .collect(),
            Box::new(subst_expr(body, from, to)),
        ),
    }
}

fn subst_int(i: &IntExpr, from: &str, to: &str) -> IntExpr {
    match i {
        IntExpr::Lit(..) => i.clone(),
        IntExpr::Card(e, p) => IntExpr::Card(Box::new(subst_expr(e, from, to)), *p),
        IntExpr::Sum(decls, body, p) => IntExpr::Sum(
            decls
                .iter()
                .map(|d| Decl {
                    disj: d.disj,
                    names: d.names.clone(),
                    expr: subst_expr(&d.expr, from, to),
                    pos: d.pos,
                    is_var: d.is_var,
                })
                .collect(),
            Box::new(subst_int(body, from, to)),
            *p,
        ),
        IntExpr::Bin(op, a, b) => IntExpr::Bin(
            *op,
            Box::new(subst_int(a, from, to)),
            Box::new(subst_int(b, from, to)),
        ),
        IntExpr::Val(e, p) => IntExpr::Val(Box::new(subst_expr(e, from, to)), *p),
        IntExpr::SumOf(e, p) => IntExpr::SumOf(Box::new(subst_expr(e, from, to)), *p),
        IntExpr::BitsVal(e, p) => IntExpr::BitsVal(Box::new(subst_expr(e, from, to)), *p),
    }
}

/// Generates the multiplicity constraint formula for one field declaration,
/// or None when it carries no markers. Exact helper relations give every
/// quantified variable its true domain.
#[allow(clippy::too_many_arguments)]
/// Strip multiplicity markers (`lone`/`one`/`some` on either side of `->`)
/// from a field type expression.
fn strip_mult(e: &Expr) -> Expr {
    match e {
        Expr::ArrowMult(_, inner) | Expr::LeadMult(_, inner) => strip_mult(inner),
        Expr::Bin(op, a, b) => Expr::Bin(*op, Box::new(strip_mult(a)), Box::new(strip_mult(b))),
        Expr::Transpose(x) => Expr::Transpose(Box::new(strip_mult(x))),
        Expr::TClosure(x) => Expr::TClosure(Box::new(strip_mult(x))),
        Expr::RClosure(x) => Expr::RClosure(Box::new(strip_mult(x))),
        Expr::Comprehension(ds, body) => Expr::Comprehension(ds.clone(), body.clone()),
        Expr::If(c, t, el) => {
            Expr::If(c.clone(), Box::new(strip_mult(t)), Box::new(strip_mult(el)))
        }
        Expr::Bracket(base, args) => Expr::Bracket(
            Box::new(strip_mult(base)),
            args.iter().map(|a| Box::new(strip_mult(a))).collect(),
        ),
        Expr::Call(n, args, p) => {
            Expr::Call(n.clone(), args.iter().map(strip_mult).collect(), *p)
        }
        Expr::Prime(x) => Expr::Prime(Box::new(strip_mult(x))),
        Expr::AtExpr(x) => Expr::AtExpr(Box::new(strip_mult(x))),
        Expr::LetBind(binds, body) => Expr::LetBind(binds.clone(), Box::new(strip_mult(body))),
        Expr::Name(..) | Expr::Univ | Expr::None_ | Expr::Iden | Expr::IntAtom | Expr::StepAtom | Expr::Bits(..) | Expr::RealLit(..) => {
            e.clone()
        }
    }
}

/// True if a field type mentions `int`/`Int`: the formula layer cannot
/// evaluate integer atoms, so those fields keep bounds-only behavior.
/// (`none`/`iden` lower and evaluate fine and are kept.)
fn mentions_int_expr(e: &Expr) -> bool {
    match e {
        Expr::IntAtom | Expr::Bits(..) => true,
        Expr::RealLit(..) => false,
        Expr::Name(n, _) => n == "int" || n == "Int" || n == "Signed",
        Expr::ArrowMult(_, inner) | Expr::LeadMult(_, inner) => mentions_int_expr(inner),
        Expr::Bin(_, a, b) => mentions_int_expr(a) || mentions_int_expr(b),
        Expr::Transpose(x) | Expr::TClosure(x) | Expr::RClosure(x) => mentions_int_expr(x),
        Expr::Comprehension(ds, body) => {
            ds.iter().any(|d| mentions_int_expr(&d.expr)) || mentions_int_formula(body)
        }
        Expr::If(c, t, el) => {
            mentions_int_formula(c) || mentions_int_expr(t) || mentions_int_expr(el)
        }
        Expr::Bracket(base, args) => {
            mentions_int_expr(base) || args.iter().any(|a| mentions_int_expr(a))
        }
        Expr::Call(_, args, _) => args.iter().any(mentions_int_expr),
        Expr::Prime(x) | Expr::AtExpr(x) => mentions_int_expr(x),
        Expr::LetBind(binds, body) => {
            binds.iter().any(|(_, ex)| mentions_int_expr(ex)) || mentions_int_expr(body)
        }
        Expr::Univ | Expr::None_ | Expr::Iden | Expr::StepAtom => false,
    }
}

fn mentions_int_formula(f: &Formula) -> bool {
    match f {
        Formula::IntCmp(..) => true,
        Formula::BadIn(..) => true,
        Formula::Const(_) => false,
        // `pin` bodies live in `Module::partials`, walked at module level.
        Formula::Pin(..) => false,
        Formula::MaxSome(e) | Formula::MinSome(e) => mentions_int_expr(e),
        Formula::MaxSomeDecl(ds, body) => {
            ds.iter().any(|d| mentions_int_expr(&d.expr)) || mentions_int_formula(body)
        }
        Formula::OverflowCond(_, body) => mentions_int_formula(body),
        // A marker target is an integer expression by construction.
        Formula::Maximize(_) | Formula::Minimize(_) => true,
        Formula::Cmp(_, a, b, _) => mentions_int_expr(a) || mentions_int_expr(b),
        Formula::Quant(_, ds, body) => {
            ds.iter().any(|d| mentions_int_expr(&d.expr)) || mentions_int_formula(body)
        }
        Formula::Multi(_, e, _) => mentions_int_expr(e),
        Formula::And(a, b)
        | Formula::Or(a, b)
        | Formula::Implies(a, b)
        | Formula::Iff(a, b)
        | Formula::Until(a, b)
        | Formula::Releases(a, b)
        | Formula::Since(a, b)
        | Formula::Triggered(a, b) => mentions_int_formula(a) || mentions_int_formula(b),
        Formula::Not(x)
        | Formula::Always(x)
        | Formula::Eventually(x)
        | Formula::Before(x)
        | Formula::Historically(x)
        | Formula::Once(x)
        | Formula::Keeping(x)
        | Formula::Goal(x)
        | Formula::Restore(x)
        | Formula::Initially(x)
        | Formula::Regularly(x)
        | Formula::Consistently(x) => mentions_int_formula(x),
        Formula::LetBind(binds, body) => {
            binds.iter().any(|(_, ex)| mentions_int_expr(ex)) || mentions_int_formula(body)
        }
        Formula::Call(_, args, _) => args.iter().any(mentions_int_expr),
    }
}

/// Collect `(sig, field)` pairs from `totalOrder[S, S.next]` calls found
/// in facts, sig facts, and predicate bodies. The second argument
/// designates the binary links (i.e. `S<:next`). The actual bound pinning
/// happens in `with_setup`; this only gathers the targets so bounds can
/// be fixed before lowering.
fn collect_total_order_pins(module: &Module) -> Vec<(String, String)> {
    let mut out = Vec::new();
    for (_, f) in &module.facts {
        scan_total_order_formula(f, &mut out);
    }
    for (_, f) in &module.soft_facts {
        scan_total_order_formula(f, &mut out);
    }
    for sd in &module.sigs {
        if let Some(f) = &sd.fact {
            scan_total_order_formula(f, &mut out);
        }
    }
    for p in &module.paras {
        scan_total_order_formula(&p.body, &mut out);
    }
    out
}

fn scan_total_order_formula(f: &Formula, out: &mut Vec<(String, String)>) {
    match f {
        Formula::Call(name, args, _) if name == "totalOrder" && args.len() == 2 => {
            if let Some(pair) = total_order_target(&args[0], &args[1]) {
                if !out.contains(&pair) {
                    out.push(pair);
                }
            }
        }
        Formula::Call(_, args, _) => {
            for a in args {
                scan_total_order_expr(a, out);
            }
        }
        Formula::Cmp(_, a, b, _) => {
            scan_total_order_expr(a, out);
            scan_total_order_expr(b, out);
        }
        Formula::BadIn(a, _) => scan_total_order_expr(a, out),
        Formula::IntCmp(_, a, b, _) => {
            scan_total_order_intexpr(a, out);
            scan_total_order_intexpr(b, out);
        }
        Formula::Quant(_, ds, body) => {
            for d in ds {
                scan_total_order_expr(&d.expr, out);
            }
            scan_total_order_formula(body, out);
        }
        Formula::Multi(_, e, _) => scan_total_order_expr(e, out),
        Formula::OverflowCond(_, body) => scan_total_order_formula(body, out),
        Formula::Maximize(ie) | Formula::Minimize(ie) => scan_total_order_intexpr(ie, out),
        Formula::And(a, b)
        | Formula::Or(a, b)
        | Formula::Implies(a, b)
        | Formula::Iff(a, b)
        | Formula::Until(a, b)
        | Formula::Releases(a, b)
        | Formula::Since(a, b)
        | Formula::Triggered(a, b) => {
            scan_total_order_formula(a, out);
            scan_total_order_formula(b, out);
        }
        Formula::Not(x)
        | Formula::Always(x)
        | Formula::Eventually(x)
        | Formula::Before(x)
        | Formula::Historically(x)
        | Formula::Once(x)
        | Formula::Keeping(x)
        | Formula::Goal(x)
        | Formula::Restore(x)
        | Formula::Initially(x)
        | Formula::Regularly(x)
        | Formula::Consistently(x) => scan_total_order_formula(x, out),
        Formula::LetBind(binds, body) => {
            for (_, e) in binds {
                scan_total_order_expr(e, out);
            }
            scan_total_order_formula(body, out);
        }
        Formula::MaxSome(e) | Formula::MinSome(e) => scan_total_order_expr(e, out),
        Formula::MaxSomeDecl(ds, body) => {
            for d in ds {
                scan_total_order_expr(&d.expr, out);
            }
            scan_total_order_formula(body, out);
        }
        Formula::Const(_) | Formula::Pin(..) => {}
    }
}

fn scan_total_order_expr(e: &Expr, out: &mut Vec<(String, String)>) {
    match e {
        Expr::Call(name, args, _) => {
            if name == "totalOrder" && args.len() == 2 {
                if let Some(pair) = total_order_target(&args[0], &args[1]) {
                    if !out.contains(&pair) {
                        out.push(pair);
                    }
                }
            }
            for a in args {
                scan_total_order_expr(a, out);
            }
        }
        Expr::Bin(_, a, b) => {
            scan_total_order_expr(a, out);
            scan_total_order_expr(b, out);
        }
        Expr::Transpose(x) | Expr::TClosure(x) | Expr::RClosure(x) => {
            scan_total_order_expr(x, out);
        }
        Expr::Comprehension(ds, body) => {
            for d in ds {
                scan_total_order_expr(&d.expr, out);
            }
            scan_total_order_formula(body, out);
        }
        Expr::If(c, t, el) => {
            scan_total_order_formula(c, out);
            scan_total_order_expr(t, out);
            scan_total_order_expr(el, out);
        }
        Expr::Bracket(base, args) => {
            scan_total_order_expr(base, out);
            for a in args {
                scan_total_order_expr(a, out);
            }
        }
        Expr::ArrowMult(_, inner) | Expr::LeadMult(_, inner) => {
            scan_total_order_expr(inner, out);
        }
        Expr::Prime(x) | Expr::AtExpr(x) => scan_total_order_expr(x, out),
        Expr::LetBind(binds, body) => {
            for (_, ex) in binds {
                scan_total_order_expr(ex, out);
            }
            scan_total_order_expr(body, out);
        }
        _ => {}
    }
}

fn scan_total_order_intexpr(e: &IntExpr, out: &mut Vec<(String, String)>) {
    match e {
        IntExpr::Card(inner, _) | IntExpr::Val(inner, _) | IntExpr::BitsVal(inner, _) => {
            scan_total_order_expr(inner, out);
        }
        IntExpr::Bin(_, a, b) => {
            scan_total_order_intexpr(a, out);
            scan_total_order_intexpr(b, out);
        }
        IntExpr::Sum(ds, body, _) => {
            for d in ds {
                scan_total_order_expr(&d.expr, out);
            }
            scan_total_order_intexpr(body, out);
        }
        IntExpr::SumOf(inner, _) => scan_total_order_expr(inner, out),
        IntExpr::Lit(..) => {}
    }
}

/// Extract `(sig, field)` from `totalOrder` arguments.
/// The second argument designates the binary links (i.e. `S<:next`):
/// `S<:f` (domain restriction), `S.f` (a join of the sig and field
/// names), or a bare field name (resolved against the first argument's
/// sig).
// ---- builtin `EReal` desugar (mirrors `util/mepk.als`) --------------------
// Lane reads lower through the lane-scoped `BitsIn` cast; `m`/`e`
// centres stay free (only `p`/`k` error exponents are pinned).
/// Lane read `base.lane` in integer position.
fn ereal_lane(base: &Expr, lane: &str) -> IntExpr {
    IntExpr::BitsVal(
        Box::new(Expr::Bin(
            BinOp::Join,
            Box::new(base.clone()),
            Box::new(Expr::Name(lane.to_string(), 0)),
        )),
        0,
    )
}

fn ereal_lit(v: i64) -> IntExpr {
    IntExpr::Lit(v, 0)
}

fn ereal_add(a: IntExpr, b: IntExpr) -> IntExpr {
    IntExpr::Bin(IntBinOp::Add, Box::new(a), Box::new(b))
}

fn ereal_sub(a: IntExpr, b: IntExpr) -> IntExpr {
    IntExpr::Bin(IntBinOp::Sub, Box::new(a), Box::new(b))
}

fn ereal_icmp(op: IntCmpOp, a: IntExpr, b: IntExpr) -> Formula {
    Formula::IntCmp(op, a, b, 0)
}

fn ereal_and_all(fs: Vec<Formula>) -> Formula {
    fs.into_iter()
        .reduce(|a, b| Formula::And(Box::new(a), Box::new(b)))
        .unwrap_or(Formula::Const(true))
}

fn ereal_or_all(fs: Vec<Formula>) -> Formula {
    fs.into_iter()
        .reduce(|a, b| Formula::Or(Box::new(a), Box::new(b)))
        .unwrap_or(Formula::Const(false))
}

/// `r = min(x, y)` over integer expressions (no Int min operator).
fn ereal_min_eq(r: &IntExpr, x: &IntExpr, y: &IntExpr) -> Formula {
    ereal_and_all(vec![
        ereal_icmp(IntCmpOp::Lte, r.clone(), x.clone()),
        ereal_icmp(IntCmpOp::Lte, r.clone(), y.clone()),
        ereal_or_all(vec![
            ereal_icmp(IntCmpOp::Eq, r.clone(), x.clone()),
            ereal_icmp(IntCmpOp::Eq, r.clone(), y.clone()),
        ]),
    ])
}

/// `k = combine_k(a, b) = max(a-b, 0) + 1` (theory §2).
fn ereal_combine_eq(k: &IntExpr, a: &IntExpr, b: &IntExpr) -> Formula {
    let d = ereal_sub(a.clone(), b.clone());
    ereal_or_all(vec![
        ereal_and_all(vec![
            ereal_icmp(IntCmpOp::Lte, d.clone(), ereal_lit(0)),
            ereal_icmp(IntCmpOp::Eq, k.clone(), ereal_lit(1)),
        ]),
        ereal_and_all(vec![
            ereal_icmp(IntCmpOp::Gt, d.clone(), ereal_lit(0)),
            ereal_icmp(
                IntCmpOp::Eq,
                k.clone(),
                ereal_add(d, ereal_lit(1)),
            ),
        ]),
    ])
}

/// `k = combine_k(ell + max(t1, t2), bExp)`: the shared add/sub tail.
/// Case-splits the max (no Int max operator).
fn ereal_max_combine_eq(
    k: &IntExpr,
    ell: &IntExpr,
    t1: &IntExpr,
    t2: &IntExpr,
    b_exp: &IntExpr,
) -> Formula {
    ereal_or_all(vec![
        ereal_and_all(vec![
            ereal_icmp(IntCmpOp::Gte, t1.clone(), t2.clone()),
            ereal_combine_eq(k, &ereal_add(ell.clone(), t1.clone()), b_exp),
        ]),
        ereal_and_all(vec![
            ereal_icmp(IntCmpOp::Gt, t2.clone(), t1.clone()),
            ereal_combine_eq(k, &ereal_add(ell.clone(), t2.clone()), b_exp),
        ]),
    ])
}

/// `lsb(x) = e - p + 1`.
fn ereal_lsb(x: &Expr) -> IntExpr {
    ereal_add(
        ereal_sub(ereal_lane(x, "e"), ereal_lane(x, "p")),
        ereal_lit(1),
    )
}

fn ereal_wellformed(x: &Expr) -> Formula {
    ereal_and_all(vec![
        ereal_icmp(IntCmpOp::Gt, ereal_lane(x, "p"), ereal_lit(0)),
        ereal_icmp(IntCmpOp::Gte, ereal_lane(x, "k"), ereal_lit(0)),
    ])
}

fn ereal_div_guard(d: &Expr) -> Formula {
    ereal_icmp(IntCmpOp::Lt, ereal_lane(d, "k"), ereal_lane(d, "p"))
}

fn ereal_needs_refine(x: &Expr, g: &Expr) -> Formula {
    // precisionLost (k >= p or tau = p-k-g <= 0) or a violated div guard.
    // The goal `g` must be an integer literal (Call args are `Expr`s;
    // threading a general IntExpr is out of scope for v1).
    let glit = match g {
        Expr::Name(n, _) => n.parse::<i64>().unwrap_or(0),
        _ => 0,
    };
    let tau = ereal_sub(
        ereal_sub(ereal_lane(x, "p"), ereal_lane(x, "k")),
        ereal_lit(glit),
    );
    ereal_or_all(vec![
        ereal_icmp(
            IntCmpOp::Gte,
            ereal_lane(x, "k"),
            ereal_lane(x, "p"),
        ),
        ereal_icmp(IntCmpOp::Lte, tau, ereal_lit(0)),
        Formula::Not(Box::new(ereal_div_guard(x))),
    ])
}

/// Addition / subtraction (§3): same error propagation for ±.
fn ereal_add_sub(a: &Expr, b: &Expr, r: &Expr) -> Formula {
    let (pa, ka) = (ereal_lane(a, "p"), ereal_lane(a, "k"));
    let (pb, kb) = (ereal_lane(b, "p"), ereal_lane(b, "k"));
    let (er, pr, kr) = (ereal_lane(r, "e"), ereal_lane(r, "p"), ereal_lane(r, "k"));
    let la1 = ereal_lsb(a);
    let la2 = ereal_lsb(b);
    let b_exp = ereal_sub(er, pr.clone());
    // ell = min(lsb1, lsb2): case-split (no Int min operator).
    // Case 1 (lsb1 <= lsb2): ell = lsb1, d1 = 0, d2 = lsb2 - lsb1.
    let case1 = ereal_and_all(vec![
        ereal_icmp(IntCmpOp::Lte, la1.clone(), la2.clone()),
        ereal_max_combine_eq(
            &kr,
            &la1,
            &ka,
            &ereal_add(kb.clone(), ereal_sub(la2.clone(), la1.clone())),
            &b_exp,
        ),
    ]);
    // Case 2 (lsb2 < lsb1).
    let case2 = ereal_and_all(vec![
        ereal_icmp(IntCmpOp::Lt, la2.clone(), la1.clone()),
        ereal_max_combine_eq(
            &kr,
            &la2,
            &ereal_add(ka.clone(), ereal_sub(la1.clone(), la2.clone())),
            &kb,
            &b_exp,
        ),
    ]);
    ereal_and_all(vec![
        ereal_wellformed(a),
        ereal_wellformed(b),
        ereal_wellformed(r),
        ereal_min_eq(&pr, &pa, &pb),
        ereal_or_all(vec![case1, case2]),
    ])
}

/// Multiplication (§4): `C = e1+e2 + max(t1,t2,t3) + 2`, 3-way max split.
fn ereal_mul(a: &Expr, b: &Expr, r: &Expr) -> Formula {
    let (ea, pa, ka) = (ereal_lane(a, "e"), ereal_lane(a, "p"), ereal_lane(a, "k"));
    let (eb, pb, kb) = (ereal_lane(b, "e"), ereal_lane(b, "p"), ereal_lane(b, "k"));
    let (er, pr, kr) = (ereal_lane(r, "e"), ereal_lane(r, "p"), ereal_lane(r, "k"));
    let t1 = ereal_add(ereal_sub(ka.clone(), pa.clone()), ereal_lit(1));
    let t2 = ereal_add(ereal_sub(kb.clone(), pb.clone()), ereal_lit(1));
    let t3 = ereal_sub(
        ereal_add(ka.clone(), kb.clone()),
        ereal_add(pa.clone(), pb.clone()),
    );
    let base = ereal_add(ea.clone(), eb.clone());
    let b_exp = ereal_sub(er, pr.clone());
    let case = |dom: &IntExpr, lo1: Formula, lo2: Formula| {
        ereal_and_all(vec![
            lo1,
            lo2,
            ereal_combine_eq(
                &kr,
                &ereal_add(ereal_add(base.clone(), dom.clone()), ereal_lit(2)),
                &b_exp,
            ),
        ])
    };
    ereal_and_all(vec![
        ereal_wellformed(a),
        ereal_wellformed(b),
        ereal_wellformed(r),
        ereal_min_eq(&pr, &pa, &pb),
        ereal_or_all(vec![
            case(
                &t1,
                ereal_icmp(IntCmpOp::Gte, t1.clone(), t2.clone()),
                ereal_icmp(IntCmpOp::Gte, t1.clone(), t3.clone()),
            ),
            case(
                &t2,
                ereal_icmp(IntCmpOp::Gt, t2.clone(), t1.clone()),
                ereal_icmp(IntCmpOp::Gte, t2.clone(), t3.clone()),
            ),
            case(
                &t3,
                ereal_icmp(IntCmpOp::Gt, t3.clone(), t1.clone()),
                ereal_icmp(IntCmpOp::Gt, t3.clone(), t2.clone()),
            ),
        ]),
    ])
}

/// Division (§5): `D = e1-e2 + max(u1,u2) + 3` with the `divGuard`
/// conjunct (violations are UNSAT: no finite bound absorbs a
/// denominator interval spanning zero).
fn ereal_div(a: &Expr, b: &Expr, r: &Expr) -> Formula {
    let (ea, pa, ka) = (ereal_lane(a, "e"), ereal_lane(a, "p"), ereal_lane(a, "k"));
    let (eb, pb, kb) = (ereal_lane(b, "e"), ereal_lane(b, "p"), ereal_lane(b, "k"));
    let (er, pr, kr) = (ereal_lane(r, "e"), ereal_lane(r, "p"), ereal_lane(r, "k"));
    let u1 = ereal_sub(ka.clone(), pa.clone());
    let u2 = ereal_sub(kb.clone(), pb.clone());
    let base = ereal_sub(ea.clone(), eb.clone());
    let b_exp = ereal_sub(er, pr.clone());
    let case = |dom: &IntExpr, lo: Formula| {
        ereal_and_all(vec![
            lo,
            ereal_combine_eq(
                &kr,
                &ereal_add(ereal_add(base.clone(), dom.clone()), ereal_lit(3)),
                &b_exp,
            ),
        ])
    };
    ereal_and_all(vec![
        ereal_wellformed(a),
        ereal_wellformed(b),
        ereal_wellformed(r),
        ereal_div_guard(b),
        ereal_min_eq(&pr, &pa, &pb),
        ereal_or_all(vec![
            case(
                &u1,
                ereal_icmp(IntCmpOp::Gte, u1.clone(), u2.clone()),
            ),
            case(
                &u2,
                ereal_icmp(IntCmpOp::Gt, u2.clone(), u1.clone()),
            ),
        ]),
    ])
}


/// `setEReal[x, lit]`: bind `x`'s lanes to the optimal conversion of
/// the decimal literal (same conversion as `:mepk lit` at `max_p`).
/// Desugars to four lane equalities; the literal text is never rounded
/// through `f64`. Out-of-range literals fail loudly at lowering.
fn ereal_set(x: &Expr, lit: &Expr, max_p: u32) -> LResult<Formula> {
    let s = match lit {
        Expr::RealLit(s, _) => s.clone(),
        _ => {
            return Err(FrontError::Resolve(
                "setEReal expects a decimal literal (e.g. 3.14) as its second argument".to_string(),
            ))
        }
    };
    let conv = decimal_to_mepk(&s, max_p).ok_or_else(|| {
        FrontError::Resolve(format!(
            "setEReal: cannot convert {s:?} (malformed or outside the i128 oracle range)"
        ))
    })?;
    // Lane widths are ≤ 30 bits, so all lanes fit in i64.
    let lanes = [
        ("m", conv.v.m as i64),
        ("e", conv.v.e as i64),
        ("p", conv.v.p as i64),
        ("k", conv.v.k as i64),
    ];
    let mut parts = Vec::with_capacity(4);
    for (lane, v) in lanes {
        parts.push(Formula::IntCmp(
            IntCmpOp::Eq,
            ereal_lane(x, lane),
            IntExpr::Lit(v, 0),
            0,
        ));
    }
    Ok(ereal_and_all(parts))
}


fn total_order_target(sig_arg: &Expr, rel_arg: &Expr) -> Option<(String, String)> {
    let Expr::Name(sig, _) = sig_arg else {
        return None;
    };
    match rel_arg {
        Expr::Bin(
            BinOp::DomainRestrict | BinOp::RangeRestrict | BinOp::Join,
            _,
            right,
        ) => {
            if let Expr::Name(field, _) = right.as_ref() {
                Some((sig.clone(), field.clone()))
            } else {
                None
            }
        }
        Expr::Name(field, _) if field != sig => Some((sig.clone(), field.clone())),
        _ => None,
    }
}

/// Split a (mult-stripped) field type into top-level product leaves.
fn flatten_product<'x>(e: &'x Expr, out: &mut Vec<&'x Expr>) {
    match e {
        Expr::Bin(BinOp::Product, a, b) => {
            flatten_product(a, out);
            flatten_product(b, out);
        }
        _ => out.push(e),
    }
}

/// Arity of one product leaf (mirrors `Lowerer::type_arity` for the
/// shapes that can appear here).
fn seg_arity(e: &Expr) -> u32 {
    match e {
        Expr::ArrowMult(_, inner) | Expr::LeadMult(_, inner) => seg_arity(inner),
        Expr::Bin(BinOp::Product, a, b) => seg_arity(a) + seg_arity(b),
        Expr::Bin(BinOp::Join, a, b) => seg_arity(a).saturating_add(seg_arity(b)).saturating_sub(2),
        Expr::Bin(_, a, _) => seg_arity(a),
        _ => 1,
    }
}

/// A product leaf usable directly as a unary quantifier domain.
fn is_plain_domain(e: &Expr) -> bool {
    matches!(e, Expr::Name(..) | Expr::Univ | Expr::None_ | Expr::Iden)
}

/// Resolve one field-type column to a unary quantifier-domain expression:
/// the lowered product segment for plain sigs, else an exact static helper
/// (`%dom%`, exact so the solver cannot vacate the domain).
#[allow(clippy::too_many_arguments)]
fn col_domain(
    ctx: &Ctx,
    arena: &mut kk::AstArena,
    b: &mut Bounds,
    res: &Resolved,
    segs: &[&Expr],
    seg_cols: &[(usize, u32)],
    col_atoms: &[Vec<String>],
    d: &Decl,
    k: usize,
) -> LResult<ExprId> {
    for (s, (start, a)) in segs.iter().zip(seg_cols.iter()) {
        if *a == 1 && *start == k - 1 && is_plain_domain(s) && !mentions_int_expr(s) {
            if let Ok((eid, 1)) = ctx.lower_expr(arena, s, &mut Vec::new()) {
                return Ok(eid);
            }
            break;
        }
    }
    let name = format!("%dom%{}.{}", std::ptr::from_ref(d) as usize, k);
    let r = arena.relation(&name, 1);
    let up = bounds::ts_of(res, &col_atoms[k]).map_err(FrontError::Resolve)?;
    b.bound_exactly(r, &up)
        .map_err(|e| FrontError::Resolve(e.to_string()))?;
    Ok(arena.expr_relation(r))
}

fn field_mult_constraint(
    ctx: &Ctx,
    arena: &mut kk::AstArena,
    b: &mut Bounds,
    frel: RelationId,
    d: &Decl,
    owner: &str,
    tuples: &[Vec<String>],
) -> LResult<Option<FormulaId>> {
    // markers: (column index, mult, trailing, end). `trailing` is true for
    // `X -> mult Y` (ArrowMult); `end` is the exclusive end column of the
    // marked segment, so `end == total` tells a last-column marking
    // (`N -> some T`) apart from a middle one (`A -> lone B -> C`).
    // LeadMult (`mult X`) records `trailing == false`.
    fn walk(
        e: &Expr,
        offset: usize,
        markers: &mut Vec<(usize, crate::ast::Mult3, bool, usize)>,
        total_cols: &mut usize,
    ) -> LResult<()> {
        match e {
            Expr::LeadMult(m, inner) => {
                let end = offset + arity_of_seg(inner, ()) as usize;
                walk(inner, offset, markers, total_cols)?;
                markers.push((0, *m, false, end));
                Ok(())
            }
            Expr::ArrowMult(m, inner) => {
                let end = offset + arity_of_seg(inner, ()) as usize;
                walk(inner, offset, markers, total_cols)?;
                markers.push((offset, *m, true, end));
                Ok(())
            }
            Expr::Bin(BinOp::Product, a, b) => {
                walk(a, offset, markers, total_cols)?;
                let aa = {
                    res_static();
                    arity_of_seg(a, ())
                };
                walk(b, offset + aa as usize, markers, total_cols)?;
                Ok(())
            }
            Expr::Name(..)
            | Expr::Univ
            | Expr::IntAtom
            | Expr::StepAtom
            | Expr::Bits(..)
            | Expr::None_
            | Expr::Iden => {
                *total_cols += 1;
                Ok(())
            }
            Expr::AtExpr(inner) => walk(inner, offset, markers, total_cols),
            Expr::Bin(BinOp::Union, _, _)
            | Expr::Bin(BinOp::Intersect, _, _)
            | Expr::Bin(BinOp::Difference, _, _) => {
                *total_cols += 1;
                Ok(())
            }
            _ => Err(FrontError::Resolve(
                "unsupported shape in field multiplicity".into(),
            )),
        }
    }
    fn arity_of_seg(e: &Expr, _r: ()) -> u32 {
        match e {
            Expr::ArrowMult(_, i) | Expr::LeadMult(_, i) => arity_of_seg(i, ()),
            Expr::Bin(BinOp::Product, a, b) => arity_of_seg(a, ()) + arity_of_seg(b, ()),
            _ => 1,
        }
    }
    fn res_static() {}

    let mut markers: Vec<(usize, crate::ast::Mult3, bool, usize)> = Vec::new();
    let mut ncols = 0usize;
    walk(&d.expr, 0, &mut markers, &mut ncols)?;
    if markers.is_empty() {
        return Ok(None);
    }
    let n = ncols + 1; // owner column included
    let res = ctx.res;

    // Quantifier domains are instance-level (dynamic) extents, so the
    // solver cannot vacate them:
    // - column 0 is the owner sig relation;
    // - columns 1.. are the lowered product-segment types (plain unary
    //   sigs); anything else falls back to an exact static helper.
    let mut dom_exprs: Vec<ExprId> = Vec::with_capacity(n);
    let owner_rel = ctx
        .lookup_rel(owner)
        .ok_or_else(|| FrontError::Resolve(format!("unknown sig '{owner}'")))?;
    dom_exprs.push(arena.expr_relation(owner_rel));
    // Uniform rule (documented `r: A m -> n B` table, Java-verified): a
    // multiplicity marking constrains, per (owner x prefix) row, the
    // suffix tuple set. Prefix length == the marked segment's end offset:
    // P9 (`N -> some T`, end == total) quantifies owner + middles, middle
    // markings (`A -> lone B -> C`, end < total) quantify owner + earlier
    // middles. Binary fields need only the owner column.
    let max_pre = markers
        .iter()
        .filter(|(c, _, t, _)| *c == 0 && *t)
        .map(|(_, _, _, e)| *e)
        .max()
        .unwrap_or(0);
    // Map each middle column to its product segment. (The last column, for
    // leading constraints, is resolved lazily in the emission loop below.)
    let stripped = strip_mult(&d.expr);
    let mut segs: Vec<&Expr> = Vec::new();
    flatten_product(&stripped, &mut segs);
    // Segment arities and column offsets.
    let mut seg_cols: Vec<(usize, u32)> = Vec::with_capacity(segs.len());
    let mut off = 0usize;
    for s in &segs {
        let a = seg_arity(s);
        seg_cols.push((off, a));
        off += a as usize;
    }
    // Per-column static atoms (fallback helper contents).
    let mut col_atoms: Vec<Vec<String>> = vec![Vec::new(); n];
    col_atoms[0] = res.atoms_of(owner);
    for row in tuples {
        for (k, a) in row.iter().enumerate().take(n) {
            if !col_atoms[k].contains(a) {
                col_atoms[k].push(a.clone());
            }
        }
    }
    if max_pre > 1 {
        for k in 1..max_pre {
            dom_exprs.push(col_domain(
                ctx, arena, b, res, &segs, &seg_cols, &col_atoms, d, k,
            )?);
        }
    }

    let mut out: Vec<FormulaId> = Vec::new();
    for (col, m, trailing, end) in markers {
        let mult = match m {
            crate::ast::Mult3::Some => Multiplicity::Some,
            crate::ast::Mult3::Lone => Multiplicity::Lone,
            crate::ast::Mult3::One => Multiplicity::One,
        };
        let frec = arena.expr_relation(frel);
        // Uniform rule (grammar yields column-0 markers only): a marking
        // constrains, per (owner x prefix) row, the suffix tuple set.
        // `f: lone B` means `all a: Owner | lone(a.f)`; `N -> some T`
        // means `all b,n | some((b.f).n)`; `A -> lone B -> C` means
        // `all o,a | lone((o.f).a)` over (B x C) pairs. Prefix length is
        // the marked segment's end offset.
        if col == 0 && ((n == 2) || (trailing && end >= 1 && end <= ncols)) {
            // all c0: D0, ..., c_{end-1}: D_{end-1} | M(join..(c0.f)..c_{end-1})
            let mut ds: Vec<kk::Decl> = Vec::new();
            let mut vars: Vec<kk::VarId> = Vec::new();
            for (j, dv) in dom_exprs.iter().enumerate().take(end) {
                let v = arena.variable(&format!("%mc{j}%{}", std::ptr::from_ref(d) as usize));
                let dd = arena.decl(v, Multiplicity::One, *dv).unwrap();
                ds.push(dd);
                vars.push(v);
            }
            let v0e = arena.expr_variable(vars[0]);
            let mut g = arena
                .binary_expr(kk::BinaryOp::Join, v0e, frec)
                .map_err(|e| FrontError::Resolve(e.to_string()))?;
            // Box-join order (argument first): each further variable
            // slices the current first column.
            for vj_expr in vars.iter().skip(1) {
                let vj = arena.expr_variable(*vj_expr);
                g = arena
                    .binary_expr(kk::BinaryOp::Join, vj, g)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
            }
            let mf = arena.multiplicity_formula(mult, g).unwrap();
            let dsid = arena.add_decls(ds);
            out.push(arena.quantified(Quantifier::All, dsid, mf));
        } else if col == 0 && !trailing && n == 3 {
            // Leading marking on a ternary field (`A m -> B` in O, per the
            // documented `r: A m -> n B` table): each (owner, last-column)
            // pair sees multiplicity M of the preimage:
            // `all o: O, bl: D_last | M(join(join(o, f), bl))`.
            // (Argument-LAST single join = preimage direction.)
            let dv_last = col_domain(ctx, arena, b, res, &segs, &seg_cols, &col_atoms, d, n - 1)?;
            let v0 = arena.variable(&format!("%ml0%{}", std::ptr::from_ref(d) as usize));
            let d0 = arena.decl(v0, Multiplicity::One, dom_exprs[0]).unwrap();
            let vl = arena.variable(&format!("%ml1%{}", std::ptr::from_ref(d) as usize));
            let dl = arena.decl(vl, Multiplicity::One, dv_last).unwrap();
            let dsid = arena.add_decls(vec![d0, dl]);
            let v0e = arena.expr_variable(v0);
            let vle = arena.expr_variable(vl);
            let g = arena
                .binary_expr(kk::BinaryOp::Join, v0e, frec)
                .map_err(|e| FrontError::Resolve(e.to_string()))?;
            let g = arena
                .binary_expr(kk::BinaryOp::Join, g, vle)
                .map_err(|e| FrontError::Resolve(e.to_string()))?;
            let mf = arena.multiplicity_formula(mult, g).unwrap();
            out.push(arena.quantified(Quantifier::All, dsid, mf));
        } else {
            // Leading markings on wider-than-ternary fields are not yet
            // supported; skip gracefully rather than erroring.
            continue;
        }
    }
    Ok(if out.is_empty() {
        None
    } else {
        Some(arena.and(&out))
    })
}

fn replace_var_expr(e: &Expr, from: &str, to: &Expr) -> Expr {
    match e {
        Expr::Name(n, _) if n == from => to.clone(),
        Expr::Name(..) | Expr::Univ | Expr::None_ | Expr::Iden | Expr::IntAtom | Expr::StepAtom | Expr::Bits(..) | Expr::RealLit(..) => {
            e.clone()
        }
        Expr::Bin(op, a, b) => Expr::Bin(
            *op,
            Box::new(replace_var_expr(a, from, to)),
            Box::new(replace_var_expr(b, from, to)),
        ),
        Expr::Transpose(x) => Expr::Transpose(Box::new(replace_var_expr(x, from, to))),
        Expr::TClosure(x) => Expr::TClosure(Box::new(replace_var_expr(x, from, to))),
        Expr::RClosure(x) => Expr::RClosure(Box::new(replace_var_expr(x, from, to))),
        Expr::Comprehension(decls, body) => {
            let shadows = decls.iter().any(|d| d.names.iter().any(|n| n == from));
            if shadows {
                e.clone()
            } else {
                Expr::Comprehension(
                    decls
                        .iter()
                        .map(|d| Decl {
                            disj: d.disj,
                            names: d.names.clone(),
                            expr: replace_var_expr(&d.expr, from, to),
                            pos: d.pos,
                            is_var: d.is_var,
                        })
                        .collect(),
                    Box::new(replace_var_formula(body, from, to)),
                )
            }
        }
        Expr::If(c, t, x) => Expr::If(
            Box::new(replace_var_formula(c, from, to)),
            Box::new(replace_var_expr(t, from, to)),
            Box::new(replace_var_expr(x, from, to)),
        ),
        Expr::Bracket(b, args) => Expr::Bracket(
            Box::new(replace_var_expr(b, from, to)),
            args.iter()
                .map(|a| Box::new(replace_var_expr(a, from, to)))
                .collect(),
        ),
        Expr::ArrowMult(m, x) => Expr::ArrowMult(*m, Box::new(replace_var_expr(x, from, to))),
        Expr::LeadMult(m, x) => Expr::LeadMult(*m, Box::new(replace_var_expr(x, from, to))),
        Expr::Call(name, args, p) => Expr::Call(
            name.clone(),
            args.iter().map(|a| replace_var_expr(a, from, to)).collect(),
            *p,
        ),
        Expr::Prime(inner) => Expr::Prime(Box::new(replace_var_expr(inner, from, to))),
        Expr::AtExpr(inner) => Expr::AtExpr(Box::new(replace_var_expr(inner, from, to))),
        Expr::LetBind(binds, body) => Expr::LetBind(
            binds
                .iter()
                .map(|(n, e)| (n.clone(), replace_var_expr(e, from, to)))
                .collect(),
            Box::new(replace_var_expr(body, from, to)),
        ),
    }
}

fn replace_var_formula(f: &Formula, from: &str, to: &Expr) -> Formula {
    match f {
        Formula::Const(v) => Formula::Const(*v),
        // `pin` names a partial block, not a variable: untouched.
        Formula::Pin(name, pos) => Formula::Pin(name.clone(), *pos),
        Formula::MaxSome(e) => Formula::MaxSome(Box::new(replace_var_expr(e, from, to))),
        Formula::MinSome(e) => Formula::MinSome(Box::new(replace_var_expr(e, from, to))),
        Formula::MaxSomeDecl(ds, body) => {
            let nd = ds
                .iter()
                .map(|d| crate::ast::Decl {
                    disj: d.disj,
                    names: d.names.clone(),
                    expr: replace_var_expr(&d.expr, from, to),
                    pos: d.pos,
                    is_var: d.is_var,
                })
                .collect();
            Formula::MaxSomeDecl(nd, Box::new(replace_var_formula(body, from, to)))
        }
        Formula::Not(x) => Formula::Not(Box::new(replace_var_formula(x, from, to))),
        Formula::OverflowCond(m, body) => {
            Formula::OverflowCond(*m, Box::new(replace_var_formula(body, from, to)))
        }
        Formula::Maximize(ie) => Formula::Maximize(replace_var_int(ie, from, to)),
        Formula::Minimize(ie) => Formula::Minimize(replace_var_int(ie, from, to)),
        Formula::And(a, b) => Formula::And(
            Box::new(replace_var_formula(a, from, to)),
            Box::new(replace_var_formula(b, from, to)),
        ),
        Formula::Or(a, b) => Formula::Or(
            Box::new(replace_var_formula(a, from, to)),
            Box::new(replace_var_formula(b, from, to)),
        ),
        Formula::Implies(a, b) => Formula::Implies(
            Box::new(replace_var_formula(a, from, to)),
            Box::new(replace_var_formula(b, from, to)),
        ),
        Formula::Iff(a, b) => Formula::Iff(
            Box::new(replace_var_formula(a, from, to)),
            Box::new(replace_var_formula(b, from, to)),
        ),
        Formula::Cmp(k, a, b, p) => Formula::Cmp(
            *k,
            replace_var_expr(a, from, to),
            replace_var_expr(b, from, to),
            *p,
        ),
        Formula::BadIn(a, p) => Formula::BadIn(Box::new(replace_var_expr(a, from, to)), *p),
        Formula::IntCmp(op, a, b, p) => Formula::IntCmp(
            *op,
            replace_var_int(a, from, to),
            replace_var_int(b, from, to),
            *p,
        ),
        Formula::Multi(k, e, p) => Formula::Multi(*k, replace_var_expr(e, from, to), *p),
        Formula::Quant(k, decls, body) => {
            let shadows = decls.iter().any(|d| d.names.iter().any(|n| n == from));
            if shadows {
                f.clone()
            } else {
                let nd = decls
                    .iter()
                    .map(|d| Decl {
                        disj: d.disj,
                        names: d.names.clone(),
                        expr: replace_var_expr(&d.expr, from, to),
                        pos: d.pos,
                        is_var: d.is_var,
                    })
                    .collect();
                Formula::Quant(*k, nd, Box::new(replace_var_formula(body, from, to)))
            }
        }
        Formula::LetBind(binds, body) => {
            if binds.iter().any(|(n, _)| n == from) {
                f.clone()
            } else {
                Formula::LetBind(
                    binds
                        .iter()
                        .map(|(n, e)| (n.clone(), replace_var_expr(e, from, to)))
                        .collect(),
                    Box::new(replace_var_formula(body, from, to)),
                )
            }
        }
        Formula::Call(name, args, p) => Formula::Call(
            name.clone(),
            args.iter().map(|a| replace_var_expr(a, from, to)).collect(),
            *p,
        ),
        Formula::Always(inner) => Formula::Always(Box::new(replace_var_formula(inner, from, to))),
        Formula::Eventually(inner) => {
            Formula::Eventually(Box::new(replace_var_formula(inner, from, to)))
        }
        Formula::Until(a, b) => Formula::Until(
            Box::new(replace_var_formula(a, from, to)),
            Box::new(replace_var_formula(b, from, to)),
        ),
        Formula::Releases(a, b) => Formula::Releases(
            Box::new(replace_var_formula(a, from, to)),
            Box::new(replace_var_formula(b, from, to)),
        ),
        Formula::Before(inner) => Formula::Before(Box::new(replace_var_formula(inner, from, to))),
        Formula::Historically(inner) => {
            Formula::Historically(Box::new(replace_var_formula(inner, from, to)))
        }
        Formula::Once(inner) => Formula::Once(Box::new(replace_var_formula(inner, from, to))),
        Formula::Since(a, b) => Formula::Since(
            Box::new(replace_var_formula(a, from, to)),
            Box::new(replace_var_formula(b, from, to)),
        ),
        Formula::Triggered(a, b) => Formula::Triggered(
            Box::new(replace_var_formula(a, from, to)),
            Box::new(replace_var_formula(b, from, to)),
        ),
        Formula::Keeping(inner) => Formula::Keeping(Box::new(replace_var_formula(inner, from, to))),
        Formula::Goal(inner) => Formula::Goal(Box::new(replace_var_formula(inner, from, to))),
        Formula::Restore(inner) => Formula::Restore(Box::new(replace_var_formula(inner, from, to))),
        Formula::Initially(inner) => {
            Formula::Initially(Box::new(replace_var_formula(inner, from, to)))
        }
        Formula::Regularly(inner) => {
            Formula::Regularly(Box::new(replace_var_formula(inner, from, to)))
        }
        Formula::Consistently(inner) => {
            Formula::Consistently(Box::new(replace_var_formula(inner, from, to)))
        }
    }
}

fn replace_var_int(i: &IntExpr, from: &str, to: &Expr) -> IntExpr {
    match i {
        IntExpr::Lit(..) => i.clone(),
        IntExpr::Card(e, p) => IntExpr::Card(Box::new(replace_var_expr(e, from, to)), *p),
        IntExpr::Sum(decls, body, p) => IntExpr::Sum(
            decls
                .iter()
                .map(|d| Decl {
                    disj: d.disj,
                    names: d.names.clone(),
                    expr: replace_var_expr(&d.expr, from, to),
                    pos: d.pos,
                    is_var: d.is_var,
                })
                .collect(),
            Box::new(replace_var_int(body, from, to)),
            *p,
        ),
        IntExpr::Bin(op, a, b) => IntExpr::Bin(
            *op,
            Box::new(replace_var_int(a, from, to)),
            Box::new(replace_var_int(b, from, to)),
        ),
        IntExpr::Val(e, p) => IntExpr::Val(Box::new(replace_var_expr(e, from, to)), *p),
        IntExpr::SumOf(e, p) => IntExpr::SumOf(Box::new(replace_var_expr(e, from, to)), *p),
        IntExpr::BitsVal(e, p) => IntExpr::BitsVal(Box::new(replace_var_expr(e, from, to)), *p),
    }
}

/// Pairs of same-group variables declared `disj`.
fn collect_disj_pairs(decls: &[Decl], arena: &mut kk::AstArena) -> Vec<(kk::VarId, kk::VarId)> {
    let mut out = Vec::new();
    for d in decls {
        if !d.disj || d.names.len() < 2 {
            continue;
        }
        let vars: Vec<kk::VarId> = d.names.iter().map(|n| arena.variable(n)).collect();
        for i in 0..vars.len() {
            for j in i + 1..vars.len() {
                out.push((vars[i], vars[j]));
            }
        }
    }
    out
}

fn var_neq(arena: &mut kk::AstArena, a: kk::VarId, b: kk::VarId) -> FormulaId {
    let ea = arena.expr_variable(a);
    let eb = arena.expr_variable(b);
    let eq = arena.comparison(ExprCompOp::Equals, ea, eb).unwrap();
    arena.not(eq)
}
