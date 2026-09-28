//! Lowers the frontend AST to kodkod-rs (AstArena + Bounds) and solves.

use crate::ast::*;
use crate::bounds::{self, Resolved};
use crate::types::{SetKind, INT_MISMATCH_MSG};
use crate::FrontError;
use alloy_kodkod_rs::ast::{
    self as kk, CastToIntOp, ExprCompOp, ExprId, FormulaId, IntId, Multiplicity, Quantifier,
};
use alloy_kodkod_rs::bounds::Bounds;
use alloy_kodkod_rs::mepk::{decimal_to_mepk, Mepk};
use alloy_kodkod_rs::real::{
    decimal_down_up, decimal_to_real, decimal_to_real_rounded, RealCenter, RealRound,
};
use alloy_kodkod_rs::mepk::decimal_rational;
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
                // `extends Real`/`extends EReal` partition (Alloy hierarchy
                // semantics over the shared populations): each extender is a
                // subset of its parent, siblings are disjoint, and an
                // *abstract-like* parent is covered by its direct extenders.
                // Roots: builtin `Real` (with the builtin `EReal` as a
                // direct child, `EReal extends Real`) plus the transitive
                // user extenders. Transitive (`A extends B extends EReal`)
                // handled level by level; `in`-children keep the
                // subset-only rule above.
                // `Real` itself is NOT covered (free `Real` values keep
                // working alongside extenders, like the old non-abstract
                // `EReal` value sort); `EReal` and abstract user parents
                // keep coverage (with extenders present they collapse onto
                // the union — sound now that decimal literals are
                // constant tuples needing no witness atoms).
                {
                    use std::collections::HashSet;
                    let mut rooted: HashSet<String> = HashSet::new();
                    rooted.insert("Real".to_string());
                    let mut kids_of: HashMap<String, Vec<String>> = HashMap::new();
                    // Builtin edge: `EReal extends Real` (only when the
                    // `EReal` population is allocated; otherwise `Real`
                    // has no builtin child).
                    if ctx.res.ereal_atoms.is_empty() {
                        // No EReal population: nothing to link.
                    } else {
                        kids_of
                            .entry("Real".to_string())
                            .or_default()
                            .push("EReal".to_string());
                        rooted.insert("EReal".to_string());
                    }
                    loop {
                        let mut grew = false;
                        for sd in &ctx.module.sigs {
                            if sd.rel == crate::ast::SigRel::In {
                                continue;
                            }
                            if let Some(p) = &sd.extends {
                                if rooted.contains(p) {
                                    for n in &sd.names {
                                        let e = kids_of.entry(p.clone()).or_default();
                                        if !e.contains(n) {
                                            e.push(n.clone());
                                        }
                                        if rooted.insert(n.clone()) {
                                            grew = true;
                                        }
                                    }
                                }
                            }
                        }
                        if !grew {
                            break;
                        }
                    }
                    let rel_of = |ctx: &Ctx<'_>, name: &str| {
                        ctx.lookup_rel(name).ok_or_else(|| {
                            FrontError::Resolve(format!("unknown sig '{name}'"))
                        })
                    };
                    // `no (A op B)` helper.
                    let no_some = |arena: &mut kk::AstArena,
                                   op: kk::BinaryOp,
                                   a: RelationId,
                                   b: RelationId| {
                        let ae = arena.expr_relation(a);
                        let be = arena.expr_relation(b);
                        let combined = arena
                            .binary_expr(op, ae, be)
                            .map_err(|e| FrontError::Resolve(e.to_string()))?;
                        let some = arena
                            .multiplicity_formula(Multiplicity::Some, combined)
                            .map_err(|e| FrontError::Resolve(e.to_string()))?;
                        Ok::<_, FrontError>(arena.not(some))
                    };
                    let mut parents: Vec<String> = kids_of.keys().cloned().collect();
                    parents.sort();
                    for p in &parents {
                        let kids = &kids_of[p];
                        let pe = rel_of(ctx, p)?;
                        // subset: kid in parent
                        for k in kids {
                            let ke = rel_of(ctx, k)?;
                            parts.push(no_some(arena, kk::BinaryOp::Difference, ke, pe)?);
                        }
                        // disjoint siblings
                        for (i, a) in kids.iter().enumerate() {
                            for b in &kids[..i] {
                                let ae = rel_of(ctx, a)?;
                                let be = rel_of(ctx, b)?;
                                parts.push(no_some(
                                    arena,
                                    kk::BinaryOp::Intersection,
                                    ae,
                                    be,
                                )?);
                            }
                        }
                        // coverage: parent in union(kids).
                        // The builtin `EReal` is abstract like any other
                        // parent: with extenders present it is covered by
                        // them, so `one sig R extends EReal` collapses
                        // `EReal` onto `R`. This is sound now that decimal
                        // literals are `ERealConstant` tuples needing no
                        // witness atoms (previously the exemption kept room
                        // for hoisted `$elit` witnesses). Parents without
                        // kids never reach this loop, so free `EReal` values
                        // (`some a: EReal`, `for N EReal`) keep working.
                        // Subset/disjoint apply everywhere (Java parity).
                        // Exception: the builtin `Real` root is covered only
                        // when user extenders exist (abstract `Real`).
                        // With the builtin `EReal` as the sole child (or
                        // no children at all), `Real` keeps free values:
                        // covering would force foreign-population atoms
                        // into `EReal` (unsound) or empty `Real` against
                        // a live `EReal` extent (UNSAT everywhere).
                        if p == "Real"
                            && !kids.iter().any(|k| k != "EReal")
                        {
                            continue;
                        }
                        let mut union = {
                            let first = rel_of(ctx, &kids[0])?;
                            arena.expr_relation(first)
                        };
                        for k in &kids[1..] {
                            let ke = arena.expr_relation(rel_of(ctx, k)?);
                            union = arena
                                .binary_expr(kk::BinaryOp::Union, union, ke)
                                .map_err(|e| FrontError::Resolve(e.to_string()))?;
                        }
                        let pe2 = arena.expr_relation(pe);
                        let diff = arena
                            .binary_expr(kk::BinaryOp::Difference, pe2, union)
                            .map_err(|e| FrontError::Resolve(e.to_string()))?;
                        let some_diff = arena
                            .multiplicity_formula(Multiplicity::Some, diff)
                            .map_err(|e| FrontError::Resolve(e.to_string()))?;
                        parts.push(arena.not(some_diff));
                    }
                    // Sig multiplicities on the shared Real/EReal population are
                    // cardinality formulas (Java `BoundsComputer`: `one` /
                    // `some` / `lone` formulas when bounds do not pin);
                    // exact bounds would pin every shared atom.
                    let mut shared = crate::bounds::ereal_shared_sigs(ctx.module);
                    shared.extend(crate::bounds::real_shared_sigs(ctx.module));
                    for sd in &ctx.module.sigs {
                        let op = match sd.mult {
                            crate::ast::SigMult::One => Multiplicity::One,
                            crate::ast::SigMult::Lone => Multiplicity::Lone,
                            crate::ast::SigMult::Some => Multiplicity::Some,
                            _ => continue,
                        };
                        for n in &sd.names {
                            if !shared.contains(n) {
                                continue;
                            }
                            let re = arena.expr_relation(rel_of(ctx, n)?);
                            parts.push(
                                arena
                                    .multiplicity_formula(op, re)
                                    .map_err(|e| FrontError::Resolve(e.to_string()))?,
                            );
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
        // Builtin `Real` centre lanes (`Real.m`, `Real.e`) plus the
        // `EReal`-only lanes (`EReal.p`, `EReal.k`); all binary
        // `owner -> lane-atoms`. `EReal` reads its centre through the
        // shared `Real.m`/`Real.e` (`EReal extends Real`).
        for (owner, fname) in crate::bounds::REAL_LANES
            .iter()
            .map(|(f, _)| ("Real", *f))
            .chain(
                crate::bounds::EREAL_EXTRA_LANES
                    .iter()
                    .map(|(f, _)| ("EReal", *f)),
            )
        {
            let key = format!("{owner}.{fname}");
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
        // Builtin `Real`/`EReal` lanes are always Int-flavored (bitmask-readable).
        for (owner, fname) in crate::bounds::REAL_LANES
            .iter()
            .map(|(f, _)| ("Real", *f))
            .chain(
                crate::bounds::EREAL_EXTRA_LANES
                    .iter()
                    .map(|(f, _)| ("EReal", *f)),
            )
        {
            field_int.insert(format!("{owner}.{fname}"), SetKind::Int);
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
            var_roots: std::cell::RefCell::new(HashMap::new()),
            // Query-only: atom references resolve against the solved Cnf's
            // universe (Java's solve-after `frame.a2k` equivalent).
            allow_atoms: true,
            pin_seq: std::cell::Cell::new(0),
            rup_memo: std::cell::RefCell::new(HashMap::new()),
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
        // Builtin lane relations (binary over the dedicated lane atoms).
        // `Real.m`/`Real.e` range over the full `Real` closure (including
        // `EReal` atoms, which read their centre through them);
        // `EReal.p`/`EReal.k` range over the `EReal` population only.
        // Allocated lazily with the lane atoms.
        for (owner, fname, group) in crate::bounds::REAL_LANES
            .iter()
            .map(|(f, g)| ("Real", *f, *g))
            .chain(
                crate::bounds::EREAL_EXTRA_LANES
                    .iter()
                    .map(|(f, g)| ("EReal", *f, *g)),
            )
        {
            let key = format!("{owner}.{fname}");
            let fa = arena.relation(&key, 2);
            field_arity.insert(key.clone(), 2);
            let lane = res.lane_atoms.get(&group).cloned().unwrap_or_default();
            let mut ts =
                alloy_kodkod_rs::tupleset::TupleSet::new(&res.universe, 2)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
            let owners: Vec<String> = if owner == "Real" {
                res.atoms_of("Real")
            } else {
                res.ereal_atoms.clone()
            };
            for o in &owners {
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

        // Bit-lane exact bounds (lazy like Int): value `v` is the
        // bit position, read with signed-MSB weight via `BitsIn(group)`.
        for (owner, fname, group) in crate::bounds::REAL_LANES
            .iter()
            .map(|(f, g)| ("Real", *f, *g))
            .chain(
                crate::bounds::EREAL_EXTRA_LANES
                    .iter()
                    .map(|(f, g)| ("EReal", *f, *g)),
            )
        {
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
                    .map_err(|e| FrontError::Resolve(format!("{owner}.{fname}: {e}")))?;
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
        // Builtin `Real`/`EReal` lanes are always Int-flavored (bitmask-readable).
        for (owner, fname) in crate::bounds::REAL_LANES
            .iter()
            .map(|(f, _)| ("Real", *f))
            .chain(
                crate::bounds::EREAL_EXTRA_LANES
                    .iter()
                    .map(|(f, _)| ("EReal", *f)),
            )
        {
            field_int.insert(format!("{owner}.{fname}"), SetKind::Int);
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
            var_roots: std::cell::RefCell::new(HashMap::new()),
            // Model builds never resolve atom names (Java parity: atoms
            // are solver outputs, not language terms).
            allow_atoms: false,
            pin_seq: std::cell::Cell::new(0),
            rup_memo: std::cell::RefCell::new(HashMap::new()),
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
    /// FLAT-EXPERIMENT: quantifier/comprehension variable -> declared
    /// root sig (`Real`/`EReal`/other). Lets `x.m` reads pick the bit
    /// partition (Real-rooted) or the legacy join (EReal-rooted).
    var_roots: std::cell::RefCell<HashMap<String, String>>,
    /// Whether universe atom names (`A$0`) resolve as singleton sets.
    /// True only for the `:query` path (solve-after evaluation, mirroring
    /// Java's `frame.a2k`); model text (run/check/eval builds) rejects
    /// them with Java's `$` error instead.
    allow_atoms: bool,
    /// Gensym sequence for `pin` label variables (`$pin{n}_...`).
    /// A counter (not source positions): one `pin` inside a twice-called
    /// predicate expands twice and must not collide with itself.
    pin_seq: std::cell::Cell<u32>,
    /// Memoized `realUp`/`realDown` lowerings: `(name, source pos,
    /// env-var fingerprint, temporal marker)` -> lowered set. The same
    /// call site is lowered once per lane join (plus once per use);
    /// sharing one lowering lets the kodkod matrix memo hit instead of
    /// re-expanding the successor core per lane. Arena-stable: `Ctx`
    /// (and this map) is fresh per lowering run.
    rup_memo: std::cell::RefCell<
        HashMap<(String, usize, Vec<kk::VarId>, Option<TimePoint>), (kk::ExprId, u32)>,
    >,
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

    /// Hoist `realUp`/`realDown` calls out of transparent expression
    /// positions: rewrites the occurrence to a fresh `$rhN` variable and
    /// records `(var, pred, arg)` triples (innermost first) for the
    /// caller to wrap in `some $vars: Real | succs & rest`. Returns
    /// `None` when no hoisting applies (no clone). Does NOT descend
    /// into nested Formula contexts (quantifier/comprehension bodies,
    /// `if` conditions): those lower per predicate call site anyway,
    /// and remaining value positions use the comprehension desugar.
    /// Fresh `$`-names can never collide with user bindings (the lexer
    /// bans `$`, and `pin_seq` is monotonic process-wide here).
    fn hoist_real_fun(
        &self,
        e: &Expr,
        out: &mut Vec<(String, String, Expr)>,
    ) -> Option<Expr> {
        match e {
            Expr::Name(..)
            | Expr::Univ
            | Expr::None_
            | Expr::Iden
            | Expr::IntAtom
            | Expr::StepAtom
            | Expr::Bits(..)
            | Expr::RealLit(..)
            | Expr::ApproxRealLit(..) => None,
            Expr::Bin(op, a, b) => {
                let na = self.hoist_real_fun(a, out);
                let nb = self.hoist_real_fun(b, out);
                if na.is_none() && nb.is_none() {
                    None
                } else {
                    Some(Expr::Bin(
                        *op,
                        Box::new(na.unwrap_or_else(|| a.as_ref().clone())),
                        Box::new(nb.unwrap_or_else(|| b.as_ref().clone())),
                    ))
                }
            }
            Expr::Transpose(x)
            | Expr::TClosure(x)
            | Expr::RClosure(x)
            | Expr::Prime(x)
            | Expr::AtExpr(x) => {
                let nx = self.hoist_real_fun(x, out)?;
                Some(match e {
                    Expr::Transpose(_) => Expr::Transpose(Box::new(nx)),
                    Expr::TClosure(_) => Expr::TClosure(Box::new(nx)),
                    Expr::RClosure(_) => Expr::RClosure(Box::new(nx)),
                    Expr::Prime(_) => Expr::Prime(Box::new(nx)),
                    _ => Expr::AtExpr(Box::new(nx)),
                })
            }
            Expr::ArrowMult(m, x) | Expr::LeadMult(m, x) => {
                let nx = self.hoist_real_fun(x, out)?;
                Some(match e {
                    Expr::ArrowMult(..) => Expr::ArrowMult(*m, Box::new(nx)),
                    _ => Expr::LeadMult(*m, Box::new(nx)),
                })
            }
            Expr::Comprehension(ds, body) => {
                let mut changed = false;
                let nds: Vec<Decl> = ds
                    .iter()
                    .map(|d| match self.hoist_real_fun(&d.expr, out) {
                        None => d.clone(),
                        Some(ne) => {
                            changed = true;
                            Decl { expr: ne, ..d.clone() }
                        }
                    })
                    .collect();
                if changed {
                    Some(Expr::Comprehension(nds, body.clone()))
                } else {
                    None
                }
            }
            Expr::If(c, t, el) => {
                let nt = self.hoist_real_fun(t, out);
                let ne = self.hoist_real_fun(el, out);
                if nt.is_none() && ne.is_none() {
                    None
                } else {
                    Some(Expr::If(
                        c.clone(),
                        Box::new(nt.unwrap_or_else(|| t.as_ref().clone())),
                        Box::new(ne.unwrap_or_else(|| el.as_ref().clone())),
                    ))
                }
            }
            Expr::Bracket(base, args) => {
                let nb = self.hoist_real_fun(base, out);
                let mut nargs: Vec<Box<Expr>> = Vec::with_capacity(args.len());
                let mut changed = nb.is_some();
                for a in args {
                    match self.hoist_real_fun(a, out) {
                        None => nargs.push(a.clone()),
                        Some(na) => {
                            changed = true;
                            nargs.push(Box::new(na));
                        }
                    }
                }
                if changed {
                    Some(Expr::Bracket(
                        Box::new(nb.unwrap_or_else(|| base.as_ref().clone())),
                        nargs,
                    ))
                } else {
                    None
                }
            }
            Expr::LetBind(binds, body) => {
                let mut changed = false;
                let nbinds: Vec<(String, Expr)> = binds
                    .iter()
                    .map(|(n, ex)| match self.hoist_real_fun(ex, out) {
                        None => (n.clone(), ex.clone()),
                        Some(ne) => {
                            changed = true;
                            (n.clone(), ne)
                        }
                    })
                    .collect();
                match self.hoist_real_fun(body, out) {
                    None if !changed => None,
                    None => Some(Expr::LetBind(nbinds, body.clone())),
                    Some(nb) => Some(Expr::LetBind(nbinds, Box::new(nb))),
                }
            }
            Expr::Call(name, cargs, pos) => {
                let mut nargs = Vec::with_capacity(cargs.len());
                for a in cargs {
                    match self.hoist_real_fun(a, out) {
                        None => nargs.push(a.clone()),
                        Some(na) => nargs.push(na),
                    }
                }
                if (name == "realUp" || name == "realDown") && nargs.len() == 1 {
                    let pred = if name == "realUp" { "realSucc" } else { "realPred" };
                    let n = self.pin_seq.get();
                    self.pin_seq.set(n + 1);
                    let v = format!("$rhh{n}");
                    out.push((v.clone(), pred.to_string(), nargs.pop().unwrap()));
                    Some(Expr::Name(v, *pos))
                } else if nargs
                    .iter()
                    .zip(cargs.iter())
                    .any(|(a, b)| a != b)
                {
                    Some(Expr::Call(name.clone(), nargs, *pos))
                } else {
                    None
                }
            }
        }
    }

    /// Hoist wrapper for builtin predicate calls: rewrites `args`,
    /// lowering `pred[hoisted...]` under `some $vars: Real | succs`.
    /// Returns `None` when no occurrence applies (caller proceeds
    /// normally). Recursion terminates (hoisted args are `realUp`-free).
    fn hoist_real_funs_call(
        &self,
        arena: &mut kk::AstArena,
        name: &str,
        args: &[Expr],
        env: &mut Env,
    ) -> LResult<Option<FormulaId>> {
        let mut hoists: Vec<(String, String, Expr)> = Vec::new();
        let mut hoisted: Vec<Expr> = Vec::with_capacity(args.len());
        for a in args {
            match self.hoist_real_fun(a, &mut hoists) {
                None => hoisted.push(a.clone()),
                Some(na) => hoisted.push(na),
            }
        }
        if hoists.is_empty() {
            return Ok(None);
        }
        let mut decls = Vec::with_capacity(hoists.len());
        let mut conj = Vec::with_capacity(hoists.len() + 1);
        for (v, pred, arg) in hoists {
            decls.push(Decl {
                disj: false,
                names: vec![v.clone()],
                expr: Expr::Name("Real".into(), 0),
                pos: 0,
                is_var: false,
            });
            conj.push(Formula::Call(pred, vec![Expr::Name(v, 0), arg], 0));
        }
        conj.push(Formula::Call(name.to_string(), hoisted, 0));
        let wrapped = Formula::Quant(
            QuantKind::Some,
            decls,
            Box::new(ereal_and_all(conj)),
        );
        Ok(Some(self.lower_formula(arena, &wrapped, env)?))
    }

    /// Try to resolve a builtin `Real` predicate call.
    /// Returns Some(formula) if the name matches (`realAdd` etc.): desugars
    /// to exact-centre constraints over the shared `Real.m`/`Real.e` lanes.
    /// Decimal literals in value positions resolve to `RealConstant`
    /// centres inline (dyadic only, no witness atoms).
    fn try_real_pred(
        &self,
        arena: &mut kk::AstArena,
        name: &str,
        args: &[Expr],
        env: &mut Env,
    ) -> LResult<Option<FormulaId>> {
        // Hoist `realUp`/`realDown` out of value positions (skolem-fast).
        if let Some(hoisted) = self.hoist_real_funs_call(arena, name, args, env)? {
            return Ok(Some(hoisted));
        }
        let body = match name {
            "realAdd" | "realSub" => {
                if args.len() != 3 {
                    return Err(FrontError::Resolve(format!("'{name}' expects 3 args")));
                }
                let wv = self.ereal_shift_width()?;
                let sign = if name == "realAdd" { 1 } else { -1 };
                // Arg order is `[R, A, B]` (`R = A +/- B`), so that
                // `R.realAdd[A, B]` reads naturally.
                let (a, b, r) = match (
                    self.real_op_or_unsat(&args[1])?,
                    self.real_op_or_unsat(&args[2])?,
                    self.real_op_or_unsat(&args[0])?,
                ) {
                    (Some(a), Some(b), Some(r)) => (a, b, r),
                    // Plain non-dyadic operand: no dyadic centre can
                    // occupy the position — the predicate is UNSAT.
                    _ => return Ok(Some(self.lower_formula(arena, &Formula::Const(false), env)?)),
                };
                real_add_sub(&a, &b, &r, sign, wv)
            }
            "realMul" | "realDiv" => {
                if args.len() != 3 {
                    return Err(FrontError::Resolve(format!("'{name}' expects 3 args")));
                }
                let wv = self.ereal_shift_width_mul()?;
                // Arg order is `[R, A, B]` (`R = A * B`, `R = A / B`), so
                // that `X.realDiv[N, D]` reads as `X = N / D`.
                let (a, b, r) = match (
                    self.real_op_or_unsat(&args[1])?,
                    self.real_op_or_unsat(&args[2])?,
                    self.real_op_or_unsat(&args[0])?,
                ) {
                    (Some(a), Some(b), Some(r)) => (a, b, r),
                    _ => return Ok(Some(self.lower_formula(arena, &Formula::Const(false), env)?)),
                };
                if name == "realMul" {
                    real_mul(&a, &b, &r, wv)
                } else {
                    real_div(&a, &b, &r, wv)
                }
            }
            "realWellformed" => {
                if args.len() != 1 {
                    return Err(FrontError::Resolve(format!("'{name}' expects 1 arg")));
                }
                match self.real_op_or_unsat(&args[0])? {
                    Some(a) => real_wellformed(&a),
                    None => Formula::Const(false),
                }
            }
            "realEq" => {
                if args.len() != 2 {
                    return Err(FrontError::Resolve(format!("'{name}' expects 2 args")));
                }
                let wv = self.ereal_shift_width()?;
                let (a, b) = match (self.real_op_or_unsat(&args[0])?, self.real_op_or_unsat(&args[1])?) {
                    (Some(a), Some(b)) => (a, b),
                    _ => return Ok(Some(self.lower_formula(arena, &Formula::Const(false), env)?)),
                };
                ereal_and_all(
                    real_all_wellformed(&[&a, &b])
                        .into_iter()
                        .chain(std::iter::once(real_scaled_eq(&a, &b, wv)))
                        .collect(),
                )
            }
            "realLT" | "realLTE" | "realGT" | "realGTE" => {
                if args.len() != 2 {
                    return Err(FrontError::Resolve(format!("'{name}' expects 2 args")));
                }
                let wv = self.ereal_shift_width()?;
                // `GT`/`GTE` swap the operands through the same exact
                // scaled comparison as `LT`/`LTE`.
                let (l, r) = if name == "realGT" || name == "realGTE" {
                    (&args[1], &args[0])
                } else {
                    (&args[0], &args[1])
                };
                // Strictness follows the original name (the swap above
                // preserves it: `GT`→`Lt`, `GTE`→`Lte`).
                let strict = name == "realLT" || name == "realGT";
                // Bracket semantics for non-dyadic literals (plain or
                // `(d)` alike): `X < L ⟺ X ≤ Down(L)`,
                // `L < X ⟺ Up(L) ≤ X` (verdict-exact: `Down(L) < L`
                // strictly, and every lane value is dyadic).
                // Dyadic literals take the legacy exact path.
                let mw = self.res.mepk_widths.m_width;
                // Plain non-dyadic literal anywhere: the predicate is
                // UNSAT (no approximation without the `(d)` spelling).
                for e in [l, r] {
                    if let Expr::RealLit(s, _) = e {
                        if decimal_to_real(s, Some(mw)).is_none()
                            && decimal_down_up(s, Some(mw)).is_some()
                        {
                            return Ok(Some(
                                self.lower_formula(arena, &Formula::Const(false), env)?,
                            ));
                        }
                    }
                }
                // Bracket endpoint (`upper` selects `Up`/`Down`) for
                // `(d)` non-dyadic literals only; `None` for
                // non-literals and dyadic literals.
                let br = |e: &Expr, upper: bool| -> LResult<Option<RealCenter>> {
                    let s = match e {
                        Expr::ApproxRealLit(s, _) => s,
                        _ => return Ok(None),
                    };
                    if decimal_to_real(s, Some(mw)).is_some() {
                        return Ok(None);
                    }
                    match decimal_down_up(s, Some(mw)) {
                        Some((d, u)) => Ok(Some(if upper { u } else { d })),
                        None => Err(FrontError::Resolve(format!(
                            "cannot convert ({s:?}) (malformed or outside the m lane)"
                        ))),
                    }
                };
                fn lit_str(e: &Expr) -> Option<&String> {
                    match e {
                        Expr::RealLit(s, _) | Expr::ApproxRealLit(s, _) => Some(s),
                        _ => None,
                    }
                }
                // Both sides non-dyadic literals: exact rational compare
                // (no lanes involved; a single bracket endpoint each
                // would be sufficient-only, hence unsound).
                if let (Some(s1), Some(s2)) = (lit_str(l), lit_str(r)) {
                    let dy1 = decimal_to_real(s1, Some(mw)).is_some();
                    let dy2 = decimal_to_real(s2, Some(mw)).is_some();
                    if !dy1 || !dy2 {
                        let (n1, d1) = decimal_rational(s1).ok_or_else(|| {
                            FrontError::Resolve(format!(
                                "cannot convert {s1:?} (malformed or outside the i128 oracle range)"
                            ))
                        })?;
                        let (n2, d2) = decimal_rational(s2).ok_or_else(|| {
                            FrontError::Resolve(format!(
                                "cannot convert {s2:?} (malformed or outside the i128 oracle range)"
                            ))
                        })?;
                        let (lhs, rhs) = (
                            n1.checked_mul(d2).ok_or_else(|| {
                                FrontError::Resolve("rational comparison overflow".to_string())
                            })?,
                            n2.checked_mul(d1).ok_or_else(|| {
                                FrontError::Resolve("rational comparison overflow".to_string())
                            })?,
                        );
                        let holds = if strict { lhs < rhs } else { lhs <= rhs };
                        return Ok(Some(self.lower_formula(arena, &Formula::Const(holds), env)?));
                    }
                }
                // Resolve: bracketed endpoint consts replace non-dyadic
                // literals (strictness absorbed: `LT`→`LTE`); dyadic and
                // variables take the exact path.
                let (bl, bb) = (br(l, true)?, br(r, false)?);
                let op = if bl.is_some() || bb.is_some() {
                    IntCmpOp::Lte
                } else if strict {
                    IntCmpOp::Lt
                } else {
                    IntCmpOp::Lte
                };
                let (a, b) = match (bl, bb) {
                    (Some(v), _) => (RealOp::Const(v), self.real_op(r)?),
                    (None, Some(v)) => (self.real_op(l)?, RealOp::Const(v)),
                    (None, None) => (self.real_op(l)?, self.real_op(r)?),
                };
                ereal_and_all(
                    real_all_wellformed(&[&a, &b])
                        .into_iter()
                        .chain(std::iter::once(real_scaled_cmp(&a, &b, op, wv)))
                        .collect(),
                )
            }
            "setReal" => {
                if args.len() != 2 {
                    return Err(FrontError::Resolve(format!("'{name}' expects 2 args")));
                }
                real_set(&args[0], &args[1], self.res.mepk_widths.m_width)?
            }
            "setRealNearest" | "setRealDown" | "setRealUp" => {
                if args.len() != 2 {
                    return Err(FrontError::Resolve(format!("'{name}' expects 2 args")));
                }
                let mode = match name {
                    "setRealNearest" => RealRound::Nearest,
                    "setRealDown" => RealRound::Down,
                    _ => RealRound::Up,
                };
                real_set_rounded(&args[0], &args[1], self.res.mepk_widths.m_width, mode, name)?
            }
            "composeReal" => {
                // Lane composition `R.composeReal[M, E]` (`R = (M, E)`):
                // user-writable counterpart of `setReal`, taking integer
                // lane values (literals or lane reads like `x.m`) so
                // `fun` derivatives can be built on top of it.
                if args.len() != 3 {
                    return Err(FrontError::Resolve(format!("'{name}' expects 3 args")));
                }
                let r = self.real_op(&args[0])?;
                let w = &self.res.mepk_widths;
                let (mw, ew) = (w.m_width, w.e_width);
                let m = self.compose_lane_or_lit(&args[1], env, mw, "m")?;
                let e = self.compose_lane_or_lit(&args[2], env, ew, "e")?;
                ereal_and_all(vec![
                    ereal_icmp(IntCmpOp::Eq, real_lane_of(&r, "m"), m),
                    ereal_icmp(IntCmpOp::Eq, real_lane_of(&r, "e"), e),
                    real_wellformed(&r),
                ])
            }
            "realSucc" | "realPred" => {
                // Lane successor / predecessor over strictly positive
                // input (mirrored for negatives, pinned for zero):
                // per-scale optima with pairwise extremality, all
                // division on lane-small non-negatives (see
                // `real_next_core`). Backs `realUp`/`realDown`.
                if args.len() != 2 {
                    return Err(FrontError::Resolve(format!("'{name}' expects 2 args")));
                }
                let up = name == "realSucc";
                let w = &self.res.mepk_widths;
                let mw = w.m_width;
                // Window radius: exactly the oracle window
                // (`ilog2(mag_max) + 2`, validated exhaustively against
                // brute force in `real.rs`), so pairwise stays minimal.
                let mag_max = if mw >= 2 { (1i64 << (mw - 1)) - 1 } else { 0 };
                let r = (mag_max.max(1).ilog2() + 2) as i64;
                let emin = -(1i64 << (w.e_width - 1));
                let emax = (1i64 << (w.e_width - 1)) - 1;
                // Arg order is `[B, A]` (`B = succ/pred(A)`), so that
                // `b.realSucc[a]` reads naturally.
                let (a, b) = (self.real_op(&args[1])?, self.real_op(&args[0])?);
                // Both-constant operands constant-fold through the
                // oracle (instant literal checks).
                if let (RealOp::Const(va), RealOp::Const(vb)) = (a, b) {
                    let w = &self.res.mepk_widths;
                    let nv = if up {
                        alloy_kodkod_rs::real::next_up(&va, w.m_width, w.e_width)
                    } else {
                        alloy_kodkod_rs::real::next_down(&va, w.m_width, w.e_width)
                    };
                    return Ok(Some(self.lower_formula(
                        arena,
                        &Formula::Const(nv == Some(vb)),
                        env,
                    )?));
                }
                let ma = real_lane_of(&a, "m");
                let ea = real_lane_of(&a, "e");
                let mb = real_lane_of(&b, "m");
                let eb = real_lane_of(&b, "e");
                // Zero input pins the extreme first step.
                let emin_lit = IntExpr::Lit(emin, 0);
                let (z_m, z_e) = if up {
                    (IntExpr::Lit(1, 0), emin_lit.clone())
                } else {
                    (IntExpr::Lit(-1, 0), emin_lit.clone())
                };
                let zero_in = ereal_and_all(vec![
                    ereal_icmp(IntCmpOp::Eq, ma.clone(), IntExpr::Lit(0, 0)),
                    ereal_icmp(IntCmpOp::Eq, mb.clone(), z_m),
                    ereal_icmp(IntCmpOp::Eq, eb.clone(), z_e),
                ]);
                // Positive input: direct core.
                let pos = ereal_and_all(vec![
                    ereal_icmp(IntCmpOp::Gt, ma.clone(), IntExpr::Lit(0, 0)),
                    real_next_core(
                        up, &ma, &ea, &mb, &eb, self.res.bitwidth, mag_max, emin,
                        emax, r,
                    ),
                ]);
                // Negative input: mirrored core on negated lanes, linked back.
                // Mirroring flips the direction: the successor above a
                // negative `a` is the negated predecessor of `-a`
                // (and dually), so the core runs with `!up`.
                let mx = IntExpr::Widen(
                    WidenOp::Sub,
                    Box::new(IntExpr::Lit(0, 0)),
                    Box::new(ma.clone()),
                );
                let my = IntExpr::Widen(
                    WidenOp::Sub,
                    Box::new(IntExpr::Lit(0, 0)),
                    Box::new(mb.clone()),
                );
                let neg_core = real_next_core(
                    !up, &mx, &ea, &my, &eb, self.res.bitwidth, mag_max, emin, emax,
                    r,
                );
                let neg = ereal_and_all(vec![
                    ereal_icmp(IntCmpOp::Lt, ma.clone(), IntExpr::Lit(0, 0)),
                    neg_core,
                    // `my` mirrors `-m_b` (the `e` lane is shared: the
                    // core pins `ey = e_b` directly).
                    ereal_icmp(
                        IntCmpOp::Eq,
                        IntExpr::Widen(WidenOp::Add, Box::new(mb.clone()), Box::new(my)),
                        real_wide(IntExpr::Lit(0, 0)),
                    ),
                ]);
                let mut parts = real_all_wellformed(&[&a, &b]);
                parts.push(ereal_or_all(vec![zero_in, pos, neg]));
                ereal_and_all(parts)
            }
            _ => return Ok(None),
        };
        Ok(Some(self.lower_formula(arena, &body, env)?))
    }

    /// Try to resolve an ordering builtin predicate call.
    /// Returns Some(formula) if the name matches an ordering builtin predicate.
    /// Builtin `EReal` predicates (`erealAdd` etc.): desugar to comparator
    /// formulas over lane joins and lower recursively. Lane reads lower
    /// through the lane-scoped `BitsIn` cast; result centres are
    /// window-pinned (Phase 1: `|c_r − (c_a ± c_b)| ≤ 2^B` plus result
    /// normalization; exact-centre rounding is a future tightening).
    fn try_ereal_pred(
        &self,
        arena: &mut kk::AstArena,
        name: &str,
        args: &[Expr],
        env: &mut Env,
    ) -> LResult<Option<FormulaId>> {
        // Decimal literals in EReal value positions (`erealAdd[c, a, 2.5]`)
        // resolve to `ERealConstant` tuples inline (no witness atoms).
        // `erealNeedsRefine` takes an integer goal second, so only its
        // first arg is an operand; `setEReal` keeps its literal second arg.
        // Hoist `realUp`/`realDown` out of value positions (skolem-fast).
        if let Some(hoisted) = self.hoist_real_funs_call(arena, name, args, env)? {
            return Ok(Some(hoisted));
        }
        let body = match name {
            "erealAdd" | "erealSub" => {
                if args.len() != 3 {
                    return Err(FrontError::Resolve(format!("'{name}' expects 3 args")));
                }
                let wv = self.ereal_shift_width()?;
                let mw = self.res.mepk_widths.m_width;
                let sign = if name == "erealAdd" { 1 } else { -1 };
                // Arg order is `[R, A, B]` (see `realAdd`).
                ereal_add_sub(&self.ereal_op(&args[1])?, &self.ereal_op(&args[2])?, &self.ereal_op(&args[0])?, sign, wv, mw)
            }
            "erealMul" => {
                if args.len() != 3 {
                    return Err(FrontError::Resolve(format!("'{name}' expects 3 args")));
                }
                let wv = self.ereal_shift_width_mul()?;
                let mw = self.res.mepk_widths.m_width;
                ereal_mul(&self.ereal_op(&args[1])?, &self.ereal_op(&args[2])?, &self.ereal_op(&args[0])?, wv, mw)
            }
            "erealDiv" => {
                if args.len() != 3 {
                    return Err(FrontError::Resolve(format!("'{name}' expects 3 args")));
                }
                let wv = self.ereal_shift_width_mul()?;
                let w = &self.res.mepk_widths;
                ereal_div(&self.ereal_op(&args[1])?, &self.ereal_op(&args[2])?, &self.ereal_op(&args[0])?, wv, w.m_width, w.guard)
            }
            "erealWellformed" => {
                if args.len() != 1 {
                    return Err(FrontError::Resolve(format!("'{name}' expects 1 arg")));
                }
                ereal_wellformed(&self.ereal_op(&args[0])?)
            }
            "erealValid" => {
                if args.len() != 1 {
                    return Err(FrontError::Resolve(format!("'{name}' expects 1 arg")));
                }
                let wv = self.ereal_shift_width()?;
                let mw = self.res.mepk_widths.m_width;
                ereal_valid_strict(&self.ereal_op(&args[0])?, wv, mw)
            }
            "erealDivGuard" => {
                if args.len() != 1 {
                    return Err(FrontError::Resolve(format!("'{name}' expects 1 arg")));
                }
                ereal_div_guard(&self.ereal_op(&args[0])?)
            }
            "erealNeedsRefine" => {
                if args.len() != 2 {
                    return Err(FrontError::Resolve(format!("'{name}' expects 2 args")));
                }
                ereal_needs_refine(&self.ereal_op(&args[0])?, &args[1])
            }
            "erealExactEq" => {
                if args.len() != 2 {
                    return Err(FrontError::Resolve(format!("'{name}' expects 2 args")));
                }
                ereal_exact_eq(&self.ereal_op(&args[0])?, &self.ereal_op(&args[1])?)
            }
            "erealMayEq" | "erealCovers" | "erealLT" | "erealLTE" | "erealMayLTE" | "erealGT" | "erealGTE" => {
                if args.len() != 2 {
                    return Err(FrontError::Resolve(format!("'{name}' expects 2 args")));
                }
                let wv = self.ereal_shift_width()?;
                match name {
                    "erealMayEq" => ereal_may_eq(&self.ereal_op(&args[0])?, &self.ereal_op(&args[1])?, wv),
                    "erealCovers" => ereal_covers(&self.ereal_op(&args[0])?, &self.ereal_op(&args[1])?, wv),
                    "erealLT" => ereal_lt(&self.ereal_op(&args[0])?, &self.ereal_op(&args[1])?, wv),
                    "erealLTE" => ereal_lte(&self.ereal_op(&args[0])?, &self.ereal_op(&args[1])?, wv),
                    // `GT`/`GTE` swap through the same closed-interval
                    // edge comparisons as `LT`/`LTE`.
                    "erealGT" => ereal_lt(&self.ereal_op(&args[1])?, &self.ereal_op(&args[0])?, wv),
                    "erealGTE" => ereal_lte(&self.ereal_op(&args[1])?, &self.ereal_op(&args[0])?, wv),
                    _ => ereal_may_lte(&self.ereal_op(&args[0])?, &self.ereal_op(&args[1])?, wv),
                }
            }
            "setEReal" => {
                if args.len() != 2 {
                    return Err(FrontError::Resolve(format!("'{name}' expects 2 args")));
                }
                // Precision cap from the active widths (same default as
                // `:mepk lit`: usable mantissa precision).
                ereal_set(&args[0], &args[1], self.ereal_max_p())?
            }
            "composeEReal" => {
                // Lane composition `R.composeEReal[M, E, P, K]`: the
                // `EReal` counterpart of `composeReal`.
                if args.len() != 5 {
                    return Err(FrontError::Resolve(format!("'{name}' expects 5 args")));
                }
                let r = self.ereal_op(&args[0])?;
                let w = &self.res.mepk_widths;
                let (mw, ew, pw, kw) = (w.m_width, w.e_width, w.p_width, w.k_width);
                let m = self.compose_lane_or_lit(&args[1], env, mw, "m")?;
                let e = self.compose_lane_or_lit(&args[2], env, ew, "e")?;
                let p = self.compose_lane_or_lit(&args[3], env, pw, "p")?;
                let k = self.compose_lane_or_lit(&args[4], env, kw, "k")?;
                ereal_and_all(vec![
                    ereal_icmp(IntCmpOp::Eq, ereal_lane_of(&r, "m"), m),
                    ereal_icmp(IntCmpOp::Eq, ereal_lane_of(&r, "e"), e),
                    ereal_icmp(IntCmpOp::Eq, ereal_lane_of(&r, "p"), p),
                    ereal_icmp(IntCmpOp::Eq, ereal_lane_of(&r, "k"), k),
                    ereal_wellformed(&r),
                ])
            }
            _ => return Ok(None),
        };
        Ok(Some(self.lower_formula(arena, &body, env)?))
    }

    /// Precision cap for decimal conversions (usable mantissa precision;
    /// same default as `:mepk lit`).
    fn ereal_max_p(&self) -> u32 {
        self.res.mepk_widths.m_width.saturating_sub(1).max(1)
    }

    /// Resolve an `EReal` operand: decimal literals become `ERealConstant`
    /// tuples (Kodkod `IntConstant` analogue: fixed lanes, no witness atom,
    /// no scope consumed); anything else stays an atom reference.
    /// Out-of-range literals fail loudly, as in `setEReal`.
    fn ereal_op<'e>(&self, e: &'e Expr) -> LResult<ERealOp<'e>> {
        match e {
            Expr::RealLit(s, _) | Expr::ApproxRealLit(s, _) => {
                let conv = decimal_to_mepk(s, self.ereal_max_p()).ok_or_else(|| {
                    FrontError::Resolve(format!(
                        "cannot convert {s:?} (malformed or outside the i128 oracle range)"
                    ))
                })?;
                Ok(ERealOp::Const(conv.v))
            }
            _ => Ok(ERealOp::Ref(e)),
        }
    }

    /// Resolve a `Real` operand: dyadic decimal literals become
    /// `RealConstant` centres inline (no witness atoms, no scope consumed);
    /// approximable `(d)` literals become their nearest centre;
    /// anything else stays an atom reference. Malformed/range literals
    /// fail loudly; plain non-dyadic literals fail loudly here too —
    /// callers needing UNSAT-instead-of-error use `real_op_or_unsat`.
    fn real_op<'e>(&self, e: &'e Expr) -> LResult<RealOp<'e>> {
        match e {
            Expr::RealLit(s, _) => {
                let mw = self.res.mepk_widths.m_width;
                let v = decimal_to_real(s, Some(mw)).ok_or_else(|| {
                    FrontError::Resolve(format!(
                        "cannot convert {s:?} to Real exactly (non-dyadic, malformed, or outside the m lane)"
                    ))
                })?;
                Ok(RealOp::Const(v))
            }
            Expr::ApproxRealLit(s, _) => {
                let mw = self.res.mepk_widths.m_width;
                let v = decimal_to_real_rounded(s, Some(mw), RealRound::Nearest).ok_or_else(|| {
                    FrontError::Resolve(format!(
                        "cannot convert ({s:?}) to Real (malformed or outside the m lane)"
                    ))
                })?;
                Ok(RealOp::Const(v))
            }
            _ => Ok(RealOp::Ref(e)),
        }
    }

    /// `real_op` with plain-non-dyadic mapped to whole-predicate-false:
    /// `None` means the enclosing predicate is UNSAT (no dyadic centre
    /// equals the literal — composable, unlike loud errors).
    /// Malformed/range literals still fail loudly.
    fn real_op_or_unsat<'e>(&self, e: &'e Expr) -> LResult<Option<RealOp<'e>>> {
        match e {
            Expr::RealLit(s, _) => {
                let mw = self.res.mepk_widths.m_width;
                if decimal_to_real(s, Some(mw)).is_some() {
                    return self.real_op(e).map(Some);
                }
                // Distinguish approximable (UNSAT) from malformed (loud).
                if decimal_to_real_rounded(s, Some(mw), RealRound::Nearest).is_some() {
                    Ok(None)
                } else {
                    Err(FrontError::Resolve(format!(
                        "cannot convert {s:?} to Real (malformed or outside the m lane)"
                    )))
                }
            }
            _ => self.real_op(e).map(Some),
        }
    }

    /// Integer lane-value argument for `composeReal`/`composeEReal`: an
    /// integer literal (range-checked against the lane width so
    /// wraparound never binds silently) or a lane read (`x.m`,
    /// bitmask-cast). General set expressions are rejected loudly: Int
    /// singletons need the SUM cast while lanes need the bitmask cast,
    /// so accepting them would silently misread one side. Bound names
    /// (quantifier/fun variables, e.g. a fun param named `m`) are never
    /// read as lanes, even when the label coincides.
    fn compose_lane_or_lit(
        &self,
        e: &Expr,
        env: &Env,
        lane_width: u32,
        lane: &str,
    ) -> LResult<IntExpr> {
        let lit = match e {
            Expr::Name(n, _) => n.parse::<i64>().ok(),
            Expr::Bits(v, _) => Some(*v),
            _ => None,
        };
        if let Some(v) = lit {
            let (lo, hi) = lane_range(lane_width);
            if v < lo || v > hi {
                return Err(FrontError::Resolve(format!(
                    "compose argument {v} outside the {lane} lane range [{lo}, {hi}]"
                )));
            }
            return Ok(IntExpr::Lit(v, 0));
        }
        if let Expr::Name(n, _) = e {
            if env.iter().any(|(nm, ..)| nm == n)
                || self.let_binds.borrow().iter().any(|s| s.contains_key(n))
                || self.expr_binds.borrow().contains_key(n)
            {
                return Err(FrontError::Resolve(format!(
                    "compose expects an integer literal or lane read for the {lane} lane (got variable `{n}`; pass a literal or `x.{lane}`)"
                )));
            }
        }
        if self.lane_group_ambiguous(e) {
            return Err(FrontError::Resolve(
                "ambiguous EReal lane: a user field shares this label; qualify explicitly"
                    .to_string(),
            ));
        }
        // FLAT-EXPERIMENT: Real-rooted `x.m` reads the partition.
        if let Some(r) = self.lane_partition_redirect(e) {
            return Ok(IntExpr::BitsVal(Box::new(r), 0));
        }
        if self.lane_group_of(e).is_some() {
            return Ok(IntExpr::BitsVal(Box::new(e.clone()), 0));
        }
        Err(FrontError::Resolve(format!(
            "compose expects an integer literal or lane read for the {lane} lane"
        )))
    }

    /// Static barrel width for scaled interval comparisons:
    /// `wv = m_width + scale_spread + 2`, where `scale_spread` is the
    /// widest representable gap between the `lsb`/`r` scale exponents
    /// (from the lane-width ranges). Shift amounts never exceed the
    /// spread and mantissae never exceed `m` bits, so every scaled edge
    /// fits with sign room to spare. Absurdly wide lane configurations
    /// fail loudly instead of hanging the solver.
    fn ereal_shift_width(&self) -> LResult<u32> {
        let w = &self.res.mepk_widths;
        let spread = Self::ereal_scale_spread(w);
        let wv = (w.m_width as u64).saturating_add(spread).saturating_add(2);
        if wv > 256 {
            return Err(FrontError::Resolve(format!(
                "interval comparison needs {wv}-bit shifts (m={}, scale spread={spread}); narrow MEPK_*_WIDTH so that m_width + spread + 2 <= 256",
                w.m_width,
            )));
        }
        Ok(wv as u32)
    }

    /// Static barrel width for mul/div centre windows (Phase 2): products
    /// of two lane mantissae need `2*m_width` bits and the doubled scales
    /// (`lsb_a+lsb_b`, `B+lsb_b`) span twice the spread, so
    /// `wv2 = 2*m_width + 2*spread + 4`. Guards loudly like `ereal_shift_width`.
    fn ereal_shift_width_mul(&self) -> LResult<u32> {
        let w = &self.res.mepk_widths;
        let spread = Self::ereal_scale_spread(w);
        let wv = (2 * w.m_width as u64)
            .saturating_add(2 * spread)
            .saturating_add(4);
        if wv > 512 {
            return Err(FrontError::Resolve(format!(
                "mul/div centre window needs {wv}-bit shifts (m={}, scale spread={spread}); narrow MEPK_*_WIDTH so that 2*m_width + 2*spread + 4 <= 512",
                w.m_width,
            )));
        }
        Ok(wv as u32)
    }

    /// Widest representable gap between the `lsb`/`r` scale exponents.
    fn ereal_scale_spread(w: &alloy_kodkod_rs::mepk::MepkWidths) -> u64 {
        // Signed lane range for width n: [-2^(n-1), 2^(n-1)-1].
        let range = |n: u32| -> (i128, i128) {
            if n == 0 {
                return (0, 0);
            }
            if n > 120 {
                return (i128::MIN, i128::MAX);
            }
            let h = 1i128 << (n - 1);
            (-h, h - 1)
        };
        let (e_lo, e_hi) = range(w.e_width);
        let (p_lo, p_hi) = range(w.p_width);
        let (k_lo, k_hi) = range(w.k_width);
        // lsb = e-p+1, r = e-p+k.
        let lo = (e_lo - p_hi + 1).min(e_lo - p_hi + k_lo);
        let hi = (e_hi - p_lo + 1).max(e_hi - p_lo + k_hi);
        (hi - lo).max(0) as u64
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
        // Desugared lanes use the qualified `Real.{lane}` / `EReal.{lane}`
        // spelling; match on the trailing segment either way.
        let short = field.rsplit('.').next().unwrap_or(&field);
        let mut found: Option<u32> = None;
        let mut count = 0;
        for key in self.field_int.keys() {
            if key.rsplit('.').next() == Some(short) {
                count += 1;
                // Builtin lanes: `Real.m`/`Real.e` (shared centre) plus
                // `EReal.p`/`EReal.k`.
                let group = [
                    ("Real.m", crate::bounds::LANE_M),
                    ("Real.e", crate::bounds::LANE_E),
                    ("EReal.p", crate::bounds::LANE_P),
                    ("EReal.k", crate::bounds::LANE_K),
                ]
                .iter()
                .find(|(k, _)| key == *k)
                .map(|(_, g)| *g);
                if let Some(group) = group {
                    // Ignore the builtin lane while its group is unallocated:
                    // a lone user field keeps its legacy reading.
                    let allocated = self
                        .res
                        .lane_atoms
                        .get(&group)
                        .is_some_and(|v| !v.is_empty());
                    if !allocated {
                        count -= 1;
                        continue;
                    }
                    found = Some(group);
                }
            }
        }
        if count == 1 { found } else { None }
    }

    /// True when `e`'s trailing label names both an allocated builtin
    /// (`Real`/`EReal`) lane and a user field: genuinely ambiguous.
    fn lane_label_ambiguous(&self, e: &Expr) -> bool {
        let Some(field) = trailing_field_name(e) else {
            return false;
        };
        let short = field.rsplit('.').next().unwrap_or(&field);
        let lane_allocated = [
            ("m", crate::bounds::LANE_M),
            ("e", crate::bounds::LANE_E),
            ("p", crate::bounds::LANE_P),
            ("k", crate::bounds::LANE_K),
        ]
        .iter()
        .any(|(fname, g)| {
            *fname == short && self.res.lane_atoms.get(g).is_some_and(|v| !v.is_empty())
        });
        lane_allocated
            && self.field_int.keys().any(|key| {
                key.rsplit('.').next() == Some(short)
                    && !key.starts_with("Real.")
                    && !key.starts_with("EReal.")
            })
    }

    /// True when the trailing field label also matches a builtin `EReal`
    /// lane (allocated) alongside user fields: the lane reading is
    /// genuinely ambiguous and must error, never silently read 0.
    fn lane_group_ambiguous(&self, e: &Expr) -> bool {
        self.lane_label_ambiguous(e)
    }

    /// FLAT-EXPERIMENT: `x.m` / `x.e` lane reads route to the bit
/// partition (`x & $M` / `x & $E`) when the base is Real-rooted
/// (sig-typed or variable-typed, never `EReal`-rooted). Returns the
/// replacement `Expr`, or `None` for the legacy join reading
/// (`EReal` control group, `p`/`k` lanes, unresolvable shapes).
fn lane_partition_redirect(&self, e: &Expr) -> Option<Expr> {
    let group = self.lane_group_of(e)?;
    let part = match group {
        g if g == crate::bounds::LANE_M => "$M",
        g if g == crate::bounds::LANE_E => "$E",
        _ => return None,
    };
    let Expr::Bin(BinOp::Join, base, _) = e else {
        return None;
    };
    // Root of the base: bound variables consult `var_roots`
    // (EReal-typed vars keep the legacy join); otherwise the sig
    // hierarchy decides (`R.m` for `R in Real` redirects).
    let root: Option<String> = match base.as_ref() {
        Expr::Name(n, _) => self
            .var_roots
            .borrow()
            .get(n)
            .cloned()
            .or_else(|| self.sig_root(n)),
        _ => None,
    };
    match root.as_deref() {
        Some("Real") => Some(flat_partition_read(base, part)),
        _ => None,
    }
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
            // FLAT-EXPERIMENT: Real-rooted `x.m` reads the partition.
            if let Some(r) = self.lane_partition_redirect(e) {
                return Some(IntExpr::BitsVal(Box::new(r), 0));
            }
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

    /// Decimal-literal value equality: `R = 1.2` / `R != 1.2` rewrite to
    /// the lane equalities (`setEReal` for `EReal`-rooted values,
    /// `setReal` otherwise since `extends` siblings are disjoint as sets
    /// and atom identity could never hold). Literal-vs-literal compares
    /// oracle conversions directly. A literal against an integer lane read
    /// (`x.m = 3.14`) stays a loud error: lanes hold integers. Returns
    /// None when neither side is a decimal literal.
    fn rewrite_ereal_lit_cmp(
        &self,
        kind: &CmpKind,
        l: &Expr,
        r: &Expr,
    ) -> LResult<Option<Formula>> {
        let neg = match kind {
            CmpKind::Eq => false,
            CmpKind::Neq => true,
            _ => return Ok(None),
        };
        let max_p = self.ereal_max_p();
        match (l, r) {
            (Expr::RealLit(s1, _), Expr::RealLit(s2, _)) => {
                let c1 = decimal_to_mepk(s1, max_p).ok_or_else(|| {
                    FrontError::Resolve(format!(
                        "cannot convert {s1:?} (malformed or outside the i128 oracle range)"
                    ))
                })?;
                let c2 = decimal_to_mepk(s2, max_p).ok_or_else(|| {
                    FrontError::Resolve(format!(
                        "cannot convert {s2:?} (malformed or outside the i128 oracle range)"
                    ))
                })?;
                let eq = c1.v == c2.v;
                Ok(Some(Formula::Const(if neg { !eq } else { eq })))
            }
            (Expr::ApproxRealLit(..), Expr::ApproxRealLit(..))
            | (Expr::RealLit(..), Expr::ApproxRealLit(..))
            | (Expr::ApproxRealLit(..), Expr::RealLit(..)) => {
                // `=`/`!=` with an approximable side: nearest-centre
                // equality (verdict-exact only when both sides' nearest
                // coincide semantics hold; both-constant so direct).
                fn approx_centre(
                    mw: u32,
                    e: &Expr,
                ) -> Result<RealCenter, FrontError> {
                    let (s, approx) = match e {
                        Expr::RealLit(s, _) => (s.as_str(), false),
                        Expr::ApproxRealLit(s, _) => (s.as_str(), true),
                        _ => unreachable!(),
                    };
                    if approx {
                        decimal_to_real_rounded(s, Some(mw), RealRound::Nearest).ok_or_else(|| {
                            FrontError::Resolve(format!(
                                "cannot convert ({s:?}) (malformed or outside the m lane)"
                            ))
                        })
                    } else {
                        decimal_to_real(s, Some(mw)).ok_or_else(|| {
                            FrontError::Resolve(format!(
                                "cannot convert {s:?} exactly (non-dyadic; wrap it as ({s}) to approximate)"
                            ))
                        })
                    }
                }
                let mw0 = self.res.mepk_widths.m_width;
                let (c1, c2) = (approx_centre(mw0, l)?, approx_centre(mw0, r)?);
                let eq = c1 == c2;
                Ok(Some(Formula::Const(if neg { !eq } else { eq })))
            }
            (Expr::RealLit(..), other)
            | (other, Expr::RealLit(..))
            | (Expr::ApproxRealLit(..), other)
            | (other, Expr::ApproxRealLit(..)) => {
                let lit = if matches!(l, Expr::RealLit(..) | Expr::ApproxRealLit(..)) {
                    l
                } else {
                    r
                };
                if self.lane_group_of(other).is_some() {
                    return Err(FrontError::Resolve(
                        "type mismatch: decimal literals cannot appear in integer lane position (e.g. `x.m = 3.14`); compare EReal values instead"
                            .to_string(),
                    ));
                }
                // `EReal`-rooted values keep the legacy `setEReal`
                // reading (pins `m/e/p/k`); everything else (`Real`
                // values, quantifier variables, unrecognized shapes)
                // uses the exact-centre `setReal` reading (`m`/`e`
                // only — still centre-correct for `EReal` atoms, with
                // `p`/`k` left free). Plain non-dyadic `Real` literals
                // are UNSAT (`=`)/true (`!=`); `(d)` binds nearest.
                let body = if self.expr_is_ereal_rooted(other) {
                    ereal_set(other, lit, max_p)?
                } else {
                    let mw = self.res.mepk_widths.m_width;
                    let lit_text = match lit {
                        Expr::RealLit(s, _) | Expr::ApproxRealLit(s, _) => s.as_str(),
                        _ => unreachable!(),
                    };
                    let is_approx = matches!(lit, Expr::ApproxRealLit(..));
                    if !is_approx
                        && decimal_to_real(lit_text, Some(mw)).is_none()
                        && decimal_to_real_rounded(lit_text, Some(mw), RealRound::Nearest).is_some()
                    {
                        // No dyadic centre equals the literal.
                        return Ok(Some(Formula::Const(neg)));
                    }
                    real_set(other, lit, mw)?
                };
                Ok(Some(if neg {
                    Formula::Not(Box::new(body))
                } else {
                    body
                }))
            }
            _ => Ok(None),
        }
    }

    /// Root builtin of a sig name (`Real`/`EReal`/other) following the
    /// user `extends` chain. `None` for unknown names (quantifier
    /// variables carry no sig type here).
    fn sig_root(&self, name: &str) -> Option<String> {
        if name == "Real" {
            return Some("Real".to_string());
        }
        if name == "EReal" {
            return Some("EReal".to_string());
        }
        let mut cur = name.to_string();
        loop {
            let sd = self
                .module
                .sigs
                .iter()
                .find(|s| s.names.iter().any(|n| n == &cur))?;
            match &sd.extends {
                None => return Some(cur),
                Some(p) if p == "Real" => return Some("Real".to_string()),
                Some(p) if p == "EReal" => return Some("EReal".to_string()),
                Some(p) => cur = p.clone(),
            }
        }
    }

    /// True when an expression is rooted at the builtin `EReal` (the
    /// `EReal` sig itself, an `extends`-descendant, or a join/bracket
    /// built on one). Used to pick the `setEReal` literal reading.
    fn expr_is_ereal_rooted(&self, e: &Expr) -> bool {
        match e {
            Expr::Name(n, _) => self.sig_root(n).as_deref() == Some("EReal"),
            Expr::Bin(_, a, _) => self.expr_is_ereal_rooted(a),
            Expr::Bracket(base, _) => self.expr_is_ereal_rooted(base),
            _ => false,
        }
    }

    fn field_int_flavored(&self, e: &Expr) -> Option<SetKind> {
        let field = trailing_field_name(e)?;
        if field == "int" || field == "Int" || field == "Signed" || field == "MSB" {
            return Some(SetKind::Int);
        }
        if field.contains('$') || field.contains('/') || field.parse::<i64>().is_ok() {
            return None;
        }
        // Qualified desugared lanes (`EReal.m`) still match lane key `m`.
        let short = field.rsplit('.').next().unwrap_or(&field);
        let mut found: Option<SetKind> = None;
        for (key, &flavor) in self.field_int.iter() {
            if key.rsplit('.').next() == Some(short) {
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
        // FLAT-EXPERIMENT: `x & $M` / `x & $E` read through the lane
        // int-bound groups (the intersect itself is plain-flavored, so
        // it bypasses the int-flavor gate like lane joins do).
        if let Some(group) = flat_lane_group(e) {
            let (ee, _) = self.lower_expr(arena, e, env)?;
            return arena
                .cast_to_int(CastToIntOp::BitsIn(group), ee)
                .map_err(|e| FrontError::Resolve(e.to_string()));
        }
        // FLAT-EXPERIMENT: Real-rooted `x.m` joins (which the parser
        // routes here directly via `set_eq_int`, bypassing the `Cmp`
        // rewrites) read the partition instead of the legacy join.
        // `EReal`-rooted bases keep the legacy reading (control).
        if let Some(r) = self.lane_partition_redirect(e) {
            if let Some(group) = flat_lane_group(&r) {
                let (ee, _) = self.lower_expr(arena, &r, env)?;
                return arena
                    .cast_to_int(CastToIntOp::BitsIn(group), ee)
                    .map_err(|e| FrontError::Resolve(e.to_string()));
            }
        }
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
            Expr::RealLit(..) | Expr::ApproxRealLit(..) => {
                return Err(FrontError::Resolve(
                    "decimal literals are only valid in Real/EReal value positions (`=`, `!=`, `setReal`, `setEReal`, `real*`, `ereal*`); approximable literals `(d)` additionally allow `real*` rounding positions".to_string(),
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
            Expr::Call(name, args, pos) => {
                // Builtin `Real` successor functions (desugared to a
                // singleton comprehension over `realSucc`/`realPred`, so
                // no witness relations are needed and nesting works
                // through the standard comprehension path).
                // Decimal literals constant-fold through the oracle
                // (`ERealConstant` philosophy): the result pins exact
                // lanes, keeping literal-heavy models trivial. Only
                // dyadic literals fold (round explicitly first).
                if name == "realUp" || name == "realDown" {
                    if args.len() != 1 {
                        return Err(FrontError::Resolve(format!("'{name}' expects 1 arg")));
                    }
                    if let Expr::RealLit(s, _) | Expr::ApproxRealLit(s, _) = &args[0] {
                        let approx = matches!(&args[0], Expr::ApproxRealLit(..));
                        let w = &self.res.mepk_widths;
                        let v = if approx {
                            decimal_to_real_rounded(s, Some(w.m_width), RealRound::Nearest).ok_or_else(|| {
                                FrontError::Resolve(format!(
                                    "cannot convert ({s:?}) to Real (malformed or outside the m lane)"
                                ))
                            })?
                        } else {
                            decimal_to_real(s, Some(w.m_width)).ok_or_else(|| {
                                FrontError::Resolve(format!(
                                    "cannot convert {s:?} to Real exactly; round it with setRealNearest first"
                                ))
                            })?
                        };
                        let nv = if name == "realUp" {
                            alloy_kodkod_rs::real::next_up(&v, w.m_width, w.e_width)
                        } else {
                            alloy_kodkod_rs::real::next_down(&v, w.m_width, w.e_width)
                        }
                        .ok_or_else(|| {
                            FrontError::Resolve(format!(
                                "'{name}' of {s:?} leaves the lane range"
                            ))
                        })?;
                        let n = self.pin_seq.get();
                        self.pin_seq.set(n + 1);
                        let vnm = format!("$rup{n}");
                        let decl = Decl {
                            disj: false,
                            names: vec![vnm.clone()],
                            expr: Expr::Name("Real".into(), 0),
                            pos: 0,
                            is_var: false,
                        };
                        // Pin the witness lanes to the computed centre.
                        let pin = ereal_and_all(vec![
                            Formula::IntCmp(
                                IntCmpOp::Eq,
                                ereal_lane(&Expr::Name(vnm.clone(), 0), "m"),
                                IntExpr::Lit(nv.m as i64, 0),
                                0,
                            ),
                            Formula::IntCmp(
                                IntCmpOp::Eq,
                                ereal_lane(&Expr::Name(vnm.clone(), 0), "e"),
                                IntExpr::Lit(nv.e as i64, 0),
                                0,
                            ),
                        ]);
                        return self.lower_expr(
                            arena,
                            &Expr::Comprehension(vec![decl], Box::new(pin)),
                            env,
                        );
                    }
                    let pred = if name == "realUp" { "realSucc" } else { "realPred" };
                    let n = self.pin_seq.get();
                    self.pin_seq.set(n + 1);
                    let v = format!("$rup{n}");
                    let decl = Decl {
                        disj: false,
                        names: vec![v.clone()],
                        expr: Expr::Name("Real".into(), 0),
                        pos: 0,
                        is_var: false,
                    };
                    let body = Formula::Call(
                        pred.into(),
                        vec![Expr::Name(v, 0), args[0].clone()],
                        0,
                    );
                    // Memoize per call site: the same occurrence is
                    // lowered once per lane join (plus once per use);
                    // sharing one lowering lets the kodkod matrix memo
                    // hit instead of re-expanding the core per lane.
                    let key = (
                        name.clone(),
                        *pos,
                        env.iter().map(|(_, vid, _, _)| *vid).collect::<Vec<_>>(),
                        self.marker_time.get(),
                    );
                    if let Some(hit) = self.rup_memo.borrow().get(&key) {
                        return Ok(*hit);
                    }
                    let out = self.lower_expr(
                        arena,
                        &Expr::Comprehension(vec![decl], Box::new(body)),
                        env,
                    )?;
                    self.rup_memo.borrow_mut().insert(key, out);
                    return Ok(out);
                }
                // Bit-position singletons (`mbit[0]` = `{M$0}`): the flat
                // spelling for individual lane bits, so lane sets can be
                // written directly (`x.m = mbit[0] + mbit[1]`).
                if matches!(name.as_str(), "mbit" | "ebit" | "pbit" | "kbit") {
                    if args.len() != 1 {
                        return Err(FrontError::Resolve(format!("'{name}' expects 1 arg")));
                    }
                    let prefix = name.chars().next().unwrap().to_ascii_uppercase();
                    let width = match name.as_str() {
                        "mbit" => self.res.mepk_widths.m_width,
                        "ebit" => self.res.mepk_widths.e_width,
                        "pbit" => self.res.mepk_widths.p_width,
                        _ => self.res.mepk_widths.k_width,
                    };
                    let idx_lit = match &args[0] {
                        Expr::Name(n, _) => n.parse::<i64>().ok(),
                        Expr::Bits(v, _) => Some(*v),
                        _ => None,
                    };
                    let i = idx_lit.ok_or_else(|| {
                        FrontError::Resolve(format!("'{name}' expects an integer literal"))
                    })?;
                    if i < 0 || i >= width as i64 {
                        return Err(FrontError::Resolve(format!(
                            "'{name}[{i}]' outside the lane range [0, {width})"
                        )));
                    }
                    let atom = format!("{prefix}${i}");
                    let idx = self
                        .res
                        .universe
                        .index(&atom)
                        .map_err(|e| FrontError::Resolve(e.to_string()))?;
                    return Ok((arena.expr_atoms(vec![idx]), 1));
                }
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
        // FLAT-EXPERIMENT: remember each variable's declared root sig
        // for lane-read routing (`x.m` -> partition iff Real-rooted).
        // Removed on exit: all inserts below happen inside this call
        // (callers pop `env` symmetrically; shadowing restores via
        // re-insertion on the outer scope's own lowering).
        let mut added_roots: Vec<String> = Vec::new();
        for d in decls {
            let domain_int = self.set_int_flavored(&d.expr, env);
            let (dom, _da) = self.lower_expr(arena, &d.expr, env)?;
            // Only plain sig names resolve (joins/arrows keep legacy routing).
            let decl_root = match &d.expr {
                Expr::Name(n, _) => self.sig_root(n),
                _ => None,
            };
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
                if let Some(ref r) = decl_root {
                    self.var_roots.borrow_mut().insert(n.clone(), r.clone());
                    added_roots.push(n.clone());
                }
                pushed += 1;
            }
        }
        let out = arena.add_decls(list);
        for n in added_roots {
            self.var_roots.borrow_mut().remove(&n);
        }
        Ok((out, pushed))
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
                    IntBinOp::Min => kk::IntBinOp::Min,
                    IntBinOp::Max => kk::IntBinOp::Max,
                    IntBinOp::Shl => kk::IntBinOp::Shl,
                };
                arena.binary_int(kop, ia, ib)
            }
            IntExpr::Widen(op, a, b) => {
                let ia = self.lower_int(arena, a, env)?;
                let ib = self.lower_int(arena, b, env)?;
                let kop = match op {
                    WidenOp::Add => kk::WidenOp::Add,
                    WidenOp::Sub => kk::WidenOp::Sub,
                    WidenOp::Shl(w) => kk::WidenOp::Shl(*w),
                    // Constant shift: the second operand is a dummy
                    // (ignored by lowering); the amount rides in the op.
                    WidenOp::ShlConst(k) => kk::WidenOp::ShlConst(*k),
                    WidenOp::Mul => kk::WidenOp::Mul,
                };
                arena.widen_int(kop, ia, ib)
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
                // Builtin `Real` predicates (exact-centre lane constraints).
                if let Some(f) = self.try_real_pred(arena, name, args, env)? {
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
                // Decimal-literal value equality (`R = 1.2`): the literal
                // denotes an EReal *value* (lane equalities, i.e.
                // `setEReal`), since `extends` siblings are disjoint as
                // sets. Lane-vs-literal (`x.m = 3`) keeps the integer
                // reading below; other shapes keep the legacy relational
                // reading.
                if matches!(kind, CmpKind::Eq | CmpKind::Neq) {
                    if let Some(rw) = self.rewrite_ereal_lit_cmp(kind, l, r)? {
                        return self.lower_formula(arena, &rw, env);
                    }
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
        Expr::Name(..) | Expr::Univ | Expr::None_ | Expr::Iden | Expr::IntAtom | Expr::StepAtom | Expr::Bits(..) | Expr::RealLit(..) | Expr::ApproxRealLit(..) => {
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
        IntExpr::Widen(op, a, b) => IntExpr::Widen(
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
        Expr::Name(..) | Expr::Univ | Expr::None_ | Expr::Iden | Expr::IntAtom | Expr::StepAtom | Expr::Bits(..) | Expr::RealLit(..) | Expr::ApproxRealLit(..) => {
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
        Expr::RealLit(..) | Expr::ApproxRealLit(..) => false,
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
        IntExpr::Widen(_, a, b) => {
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
// Lane reads lower through the lane-scoped `BitsIn` cast. Result centres
// are window-pinned (see `ereal_add_window`/`ereal_result_normalized`);
// only an exact-centre rounding encoding is left for the future.
/// FLAT-EXPERIMENT: bit-partition read (`x & $M` / `x & $E`): the lane's
/// bitmask value comes from the `$M`/`$E` int-bound group, not group 0.
fn flat_lane_group(e: &Expr) -> Option<u32> {
    if let Expr::Bin(BinOp::Intersect, a, b) = e {
        for side in [a.as_ref(), b.as_ref()] {
            if let Expr::Name(n, _) = side {
                match n.as_str() {
                    "$M" => return Some(crate::bounds::LANE_M),
                    "$E" => return Some(crate::bounds::LANE_E),
                    _ => {}
                }
            }
        }
    }
    None
}

/// FLAT-EXPERIMENT: `base & $part` as an `Expr`.
fn flat_partition_read(base: &Expr, part: &str) -> Expr {
    Expr::Bin(
        BinOp::Intersect,
        Box::new(base.clone()),
        Box::new(Expr::Name(part.to_string(), 0)),
    )
}

/// Lane read `base.lane` in integer position.
fn ereal_lane(base: &Expr, lane: &str) -> IntExpr {
    // Qualified owner: `m`/`e` live in the shared `Real` lanes
    // (`EReal extends Real`), `p`/`k` in the `EReal`-only lanes.
    // A bare lane name (`e`, `m`, `p`, `k`) would resolve through the
    // quantifier environment first, so a user variable named `e` (etc.)
    // shadows the lane relation and produces a 1+1 join
    // (`join arity too low`). The qualified key always hits the lane
    // relation directly (env names never contain `.`).
    // Lane helpers below normalize the trailing segment, so `EReal.m`
    // is still recognised as lane `m`.
    let owner = match lane {
        "m" | "e" => "Real",
        _ => "EReal",
    };
    IntExpr::BitsVal(
        Box::new(Expr::Bin(
            BinOp::Join,
            Box::new(base.clone()),
            Box::new(Expr::Name(format!("{owner}.{lane}"), 0)),
        )),
        0,
    )
}

fn ereal_lit(v: i64) -> IntExpr {
    IntExpr::Lit(v, 0)
}

/// An `EReal` operand: either an atom-valued expression (lane joins) or a
/// constant tuple (`ERealConstant`, the Kodkod `IntConstant` analogue: fixed
/// `(m, e, p, k)` lanes, no universe atom, no scope consumed).
#[derive(Clone, Copy)]
enum ERealOp<'e> {
    Ref(&'e Expr),
    Const(Mepk),
}

/// Lane read through an operand: joins for atoms, literals for constants.
/// Constant lanes always fit `i64` (converted at `ereal_max_p <= m_width-1`,
/// same bound as `ereal_set` relies on).
fn ereal_lane_of(op: &ERealOp, lane: &str) -> IntExpr {
    match op {
        ERealOp::Ref(e) => ereal_lane(e, lane),
        ERealOp::Const(v) => {
            let n = match lane {
                "m" => v.m as i64,
                "e" => v.e as i64,
                "p" => v.p as i64,
                "k" => v.k as i64,
                _ => unreachable!("unknown EReal lane {lane}"),
            };
            ereal_lit(n)
        }
    }
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

fn ereal_wellformed(x: &ERealOp) -> Formula {
    ereal_and_all(vec![
        ereal_icmp(IntCmpOp::Gt, ereal_lane_of(x, "p"), ereal_lit(0)),
        ereal_icmp(IntCmpOp::Gte, ereal_lane_of(x, "k"), ereal_lit(0)),
    ])
}

fn ereal_div_guard(d: &ERealOp) -> Formula {
    ereal_icmp(IntCmpOp::Lt, ereal_lane_of(d, "k"), ereal_lane_of(d, "p"))
}

/// Value identity: all four lanes agree (plus wellformedness, like the
/// arithmetic predicates). `extends` siblings are disjoint as *sets*,
/// so this is the usable equality for EReal values.
fn ereal_exact_eq(a: &ERealOp, b: &ERealOp) -> Formula {
    let mut parts = vec![ereal_wellformed(a), ereal_wellformed(b)];
    for lane in ["m", "e", "p", "k"] {
        parts.push(ereal_icmp(
            IntCmpOp::Eq,
            ereal_lane_of(a, lane),
            ereal_lane_of(b, lane),
        ));
    }
    ereal_and_all(parts)
}

// ---- scaled interval comparisons ----------------------------------------
// An EReal value denotes the closed interval `[lo, hi]` with centre
// `c = m*2^lsb` (`lsb = e-p+1`) and radius `R = 2^r` (`r = e-p+k`).
// Comparing edges (`hiA <= loB`, ...) needs a common binary point: both
// sides are scaled by `2^s0` (`s0` = min of the four scale exponents) so
// every shift amount is non-negative. Shifts run in a statically-sized
// barrel (`wv = m_width + scale_spread + 2`, guarded below); sums grow
// exactly. Fixed-width circuits could never hold this (a mantissa
// already spans the problem bitwidth), hence the widening layer.

/// `lsb(x) = e - p + 1`, exact widening arithmetic.
fn ereal_lsb_wide(x: &ERealOp) -> IntExpr {
    IntExpr::Widen(
        WidenOp::Add,
        Box::new(IntExpr::Widen(
            WidenOp::Sub,
            Box::new(ereal_lane_of(x, "e")),
            Box::new(ereal_lane_of(x, "p")),
        )),
        Box::new(IntExpr::Lit(1, 0)),
    )
}

/// `r(x) = e - p + k`: exponent of the error radius (`R = 2^r`).
fn ereal_r_exp(x: &ERealOp) -> IntExpr {
    IntExpr::Widen(
        WidenOp::Add,
        Box::new(IntExpr::Widen(
            WidenOp::Sub,
            Box::new(ereal_lane_of(x, "e")),
            Box::new(ereal_lane_of(x, "p")),
        )),
        Box::new(ereal_lane_of(x, "k")),
    )
}

fn ereal_wadd(a: IntExpr, b: IntExpr) -> IntExpr {
    IntExpr::Widen(WidenOp::Add, Box::new(a), Box::new(b))
}

fn ereal_wsub(a: IntExpr, b: IntExpr) -> IntExpr {
    IntExpr::Widen(WidenOp::Sub, Box::new(a), Box::new(b))
}

fn ereal_wshl(v: IntExpr, d: IntExpr, wv: u32) -> IntExpr {
    IntExpr::Widen(WidenOp::Shl(wv), Box::new(v), Box::new(d))
}

/// Exact widening product (see `WidenOp::Mul`).
fn ereal_wmul(a: IntExpr, b: IntExpr) -> IntExpr {
    IntExpr::Widen(WidenOp::Mul, Box::new(a), Box::new(b))
}

fn ereal_min(a: IntExpr, b: IntExpr) -> IntExpr {
    IntExpr::Bin(IntBinOp::Min, Box::new(a), Box::new(b))
}

/// One scaled interval-edge comparison:
/// `mA*2^lsbA + s1*2^rA  OP  mB*2^lsbB + s2*2^rB`
/// with `s1, s2 ∈ {+1 (hi edge), -1 (lo edge)}` and `OP ∈ {Lt, Lte}`.
fn ereal_scaled_cmp(a: &ERealOp, b: &ERealOp, s1: i64, s2: i64, op: IntCmpOp, wv: u32) -> Formula {
    let lsb_a = ereal_lsb_wide(a);
    let r_a = ereal_r_exp(a);
    let lsb_b = ereal_lsb_wide(b);
    let r_b = ereal_r_exp(b);
    let s0 = ereal_min(
        ereal_min(lsb_a.clone(), r_a.clone()),
        ereal_min(lsb_b.clone(), r_b.clone()),
    );
    let edge = |m: IntExpr, lsb: IntExpr, r: IntExpr, s: i64| {
        let c = ereal_wshl(m, ereal_wsub(lsb, s0.clone()), wv);
        let rad = ereal_wshl(IntExpr::Lit(1, 0), ereal_wsub(r, s0.clone()), wv);
        if s > 0 {
            ereal_wadd(c, rad)
        } else {
            ereal_wsub(c, rad)
        }
    };
    let lhs = edge(ereal_lane_of(a, "m"), lsb_a, r_a, s1);
    let rhs = edge(ereal_lane_of(b, "m"), lsb_b, r_b, s2);
    Formula::IntCmp(op, lhs, rhs, 0)
}

/// Closed-interval overlap: `loA<=hiB and loB<=hiA` (endpoint contact
/// counts).
fn ereal_may_eq(a: &ERealOp, b: &ERealOp, wv: u32) -> Formula {
    ereal_and_all(vec![
        ereal_wellformed(a),
        ereal_wellformed(b),
        ereal_scaled_cmp(a, b, -1, 1, IntCmpOp::Lte, wv),
        ereal_scaled_cmp(b, a, -1, 1, IntCmpOp::Lte, wv),
    ])
}

/// Containment (A covers B, equal intervals count): `loA<=loB and hiB<=hiA`.
fn ereal_covers(a: &ERealOp, b: &ERealOp, wv: u32) -> Formula {
    ereal_and_all(vec![
        ereal_wellformed(a),
        ereal_wellformed(b),
        ereal_scaled_cmp(a, b, -1, -1, IntCmpOp::Lte, wv),
        ereal_scaled_cmp(b, a, 1, 1, IntCmpOp::Lte, wv),
    ])
}

/// Strictly below: `hiA < loB`.
fn ereal_lt(a: &ERealOp, b: &ERealOp, wv: u32) -> Formula {
    ereal_and_all(vec![
        ereal_wellformed(a),
        ereal_wellformed(b),
        ereal_scaled_cmp(a, b, 1, -1, IntCmpOp::Lt, wv),
    ])
}

/// Below or touching: `hiA <= loB`.
fn ereal_lte(a: &ERealOp, b: &ERealOp, wv: u32) -> Formula {
    ereal_and_all(vec![
        ereal_wellformed(a),
        ereal_wellformed(b),
        ereal_scaled_cmp(a, b, 1, -1, IntCmpOp::Lte, wv),
    ])
}

/// A's upper end lies in B's range: `loB<=hiA<=hiB`.
fn ereal_may_lte(a: &ERealOp, b: &ERealOp, wv: u32) -> Formula {
    ereal_and_all(vec![
        ereal_wellformed(a),
        ereal_wellformed(b),
        ereal_scaled_cmp(b, a, -1, 1, IntCmpOp::Lte, wv),
        ereal_scaled_cmp(a, b, 1, 1, IntCmpOp::Lte, wv),
    ])
}

fn ereal_needs_refine(x: &ERealOp, g: &Expr) -> Formula {
    // precisionLost (k >= p or tau = p-k-g <= 0) or a violated div guard.
    // The goal `g` must be an integer literal (Call args are `Expr`s;
    // threading a general IntExpr is out of scope for v1).
    let glit = match g {
        Expr::Name(n, _) => n.parse::<i64>().unwrap_or(0),
        _ => 0,
    };
    let tau = ereal_sub(
        ereal_sub(ereal_lane_of(x, "p"), ereal_lane_of(x, "k")),
        ereal_lit(glit),
    );
    ereal_or_all(vec![
        ereal_icmp(
            IntCmpOp::Gte,
            ereal_lane_of(x, "k"),
            ereal_lane_of(x, "p"),
        ),
        ereal_icmp(IntCmpOp::Lte, tau, ereal_lit(0)),
        Formula::Not(Box::new(ereal_div_guard(x))),
    ])
}

/// Addition / subtraction (§3): same error propagation for ±, plus a
/// centre window pin and result normalization (Phase 1). `sign` is +1
/// (add) or -1 (sub); `wv` is the static barrel width
/// (`ereal_shift_width`), `m_width` the mantissa lane width.
///
/// The `k'` path is end-to-end widening-exact (P2-2): `lsb`, `A`, and `B`
/// never wrap at the problem bitwidth (a wrapped `ell` would pick the
/// wrong alignment case and silently shrink `k'`).
fn ereal_add_sub(a: &ERealOp, b: &ERealOp, r: &ERealOp, sign: i8, wv: u32, m_width: u32) -> Formula {
    let (pa, ka) = (ereal_lane_of(a, "p"), ereal_lane_of(a, "k"));
    let (pb, kb) = (ereal_lane_of(b, "p"), ereal_lane_of(b, "k"));
    let (er, pr, kr) = (ereal_lane_of(r, "e"), ereal_lane_of(r, "p"), ereal_lane_of(r, "k"));
    let la1 = ereal_lsb_wide(a);
    let la2 = ereal_lsb_wide(b);
    let b_exp = ereal_wsub(er, pr.clone());
    // ell = min(lsb1, lsb2): case-split (no Int min operator).
    // Case 1 (lsb1 <= lsb2): ell = lsb1, d1 = 0, d2 = lsb2 - lsb1.
    let case1 = ereal_and_all(vec![
        ereal_icmp(IntCmpOp::Lte, la1.clone(), la2.clone()),
        ereal_max_combine_eq_wide(
            &kr,
            &la1,
            &ka,
            &ereal_wadd(kb.clone(), ereal_wsub(la2.clone(), la1.clone())),
            &b_exp,
        ),
    ]);
    // Case 2 (lsb2 < lsb1).
    let case2 = ereal_and_all(vec![
        ereal_icmp(IntCmpOp::Lt, la2.clone(), la1.clone()),
        ereal_max_combine_eq_wide(
            &kr,
            &la2,
            &ereal_wadd(ka.clone(), ereal_wsub(la1.clone(), la2.clone())),
            &kb,
            &b_exp,
        ),
    ]);
    ereal_and_all(vec![
        ereal_valid_core(a, wv, m_width),
        ereal_valid_core(b, wv, m_width),
        ereal_valid_core(r, wv, m_width),
        ereal_min_eq(&pr, &pa, &pb),
        ereal_or_all(vec![case1, case2]),
        ereal_add_window(a, b, r, sign, wv),
    ])
}

/// `k = combine_k(ell + max(t1, t2), bExp)` with exact widening
/// arithmetic (see `ereal_max_combine_eq` for the wrapping variant).
fn ereal_max_combine_eq_wide(
    k: &IntExpr,
    ell: &IntExpr,
    t1: &IntExpr,
    t2: &IntExpr,
    b_exp: &IntExpr,
) -> Formula {
    ereal_or_all(vec![
        ereal_and_all(vec![
            ereal_icmp(IntCmpOp::Gte, t1.clone(), t2.clone()),
            ereal_combine_eq_wide(k, &ereal_wadd(ell.clone(), t1.clone()), b_exp),
        ]),
        ereal_and_all(vec![
            ereal_icmp(IntCmpOp::Gt, t2.clone(), t1.clone()),
            ereal_combine_eq_wide(k, &ereal_wadd(ell.clone(), t2.clone()), b_exp),
        ]),
    ])
}

/// Exact negation for widening arithmetic (`0 - x`, grows exactly).
fn ereal_wneg(a: IntExpr) -> IntExpr {
    IntExpr::Widen(
        WidenOp::Sub,
        Box::new(IntExpr::Lit(0, 0)),
        Box::new(a),
    )
}

/// Centre window pin for add/sub (Phase 1):
/// `|c_r − (c_a ± c_b)| ≤ 2^B` with `B = e_r − p_r`, scaled to the common
/// exponent `s0 = min(lsb_a, lsb_b, lsb_r, B)` so every shift amount is
/// non-negative (same widening pattern as `ereal_scaled_cmp`).
///
/// Soundness: with `|x1±x2 − S| ≤ 2^A` (doc §3, `S` the exact scaled sum)
/// and `|c_r − S| ≤ 2^B` (this constraint), the triangle inequality gives
/// `|x1±x2 − c_r| ≤ 2^A + 2^B ≤ 2^(B+k') = R'` with the unchanged
/// `k' = combine_k(A, B)`. The invariant is preserved for chaining, and
/// every scaled interval still contains the true value whatever `e_r`
/// the solver picks (`hi ≥ exact`, `lo ≤ exact`, since `R' ≥ 2·2^B`).
/// Exact-centre rounding (`m_r = round(T)`) is a future tightening.
fn ereal_add_window(a: &ERealOp, b: &ERealOp, r: &ERealOp, sign: i8, wv: u32) -> Formula {
    let lsb_a = ereal_lsb_wide(a);
    let lsb_b = ereal_lsb_wide(b);
    let lsb_r = ereal_lsb_wide(r);
    let b_exp = IntExpr::Widen(
        WidenOp::Sub,
        Box::new(ereal_lane_of(r, "e")),
        Box::new(ereal_lane_of(r, "p")),
    );
    let s0 = ereal_min(
        ereal_min(lsb_a.clone(), lsb_b.clone()),
        ereal_min(lsb_r.clone(), b_exp.clone()),
    );
    let ca = ereal_wshl(ereal_lane_of(a, "m"), ereal_wsub(lsb_a, s0.clone()), wv);
    let cb = ereal_wshl(ereal_lane_of(b, "m"), ereal_wsub(lsb_b, s0.clone()), wv);
    let s = if sign == 1 {
        ereal_wadd(ca, cb)
    } else {
        ereal_wsub(ca, cb)
    };
    let cr = ereal_wshl(ereal_lane_of(r, "m"), ereal_wsub(lsb_r, s0.clone()), wv);
    let diff = ereal_wsub(cr, s);
    let bound = ereal_wshl(IntExpr::Lit(1, 0), ereal_wsub(b_exp, s0), wv);
    ereal_and_all(vec![
        ereal_icmp(IntCmpOp::Lte, diff.clone(), bound.clone()),
        ereal_icmp(IntCmpOp::Lte, ereal_wneg(bound), diff),
    ])
}

/// `2^p` and `2^(p-1)` as widening shifts (exact while `p ≤ m_width`;
/// callers conjoin the cap; see `ereal_valid_core`).
fn ereal_pow2(x: &ERealOp, wv: u32) -> (IntExpr, IntExpr) {
    let p = ereal_lane_of(x, "p");
    let full = ereal_wshl(IntExpr::Lit(1, 0), p.clone(), wv);
    let half = ereal_wshl(
        IntExpr::Lit(1, 0),
        ereal_sub(p, ereal_lit(1)),
        wv,
    );
    (full, half)
}

/// Nonzero normalization: `2^(p−1) ≤ |m| < 2^p` with `p ≤ m_width`.
/// `p ≤ m_width` loses no legitimate model (a nonzero `m` in an
/// `m_width`-bit lane has `p ≤ m_width`). Hand-made lanes violating this
/// are rejected (UNSAT), like the `m == 0` denominator guard.
/// Downstream mul/div proofs (doc §4–§5) assume normalized inputs
/// (`|c| < 2^(e+1)`, `|c| ≥ 2^e`); without the lower bound the `k < p`
/// div guard is insufficient (a denormalized `m` can span zero at `k < p`).
fn ereal_m_normalized_nz(x: &ERealOp, wv: u32, m_width: u32) -> Formula {
    let m = ereal_lane_of(x, "m");
    let (full, half) = ereal_pow2(x, wv);
    let cap = ereal_icmp(
        IntCmpOp::Lte,
        ereal_lane_of(x, "p"),
        ereal_lit(m_width as i64),
    );
    ereal_or_all(vec![
        ereal_and_all(vec![
            cap.clone(),
            ereal_icmp(IntCmpOp::Gte, m.clone(), half.clone()),
            ereal_icmp(IntCmpOp::Lt, m.clone(), full.clone()),
        ]),
        ereal_and_all(vec![
            cap,
            ereal_icmp(IntCmpOp::Lte, m.clone(), ereal_wneg(half)),
            ereal_icmp(IntCmpOp::Gt, m, ereal_wneg(full)),
        ]),
    ])
}

/// Result normalization for add/sub/mul/div: `m_r == 0` (exact
/// cancellation) or nonzero normalization (see `ereal_m_normalized_nz`).
fn ereal_result_normalized(r: &ERealOp, wv: u32, m_width: u32) -> Formula {
    ereal_or_all(vec![
        ereal_icmp(IntCmpOp::Eq, ereal_lane_of(r, "m"), ereal_lit(0)),
        ereal_m_normalized_nz(r, wv, m_width),
    ])
}

/// Permanent `Valid` core (rev3 §1): `wellformed` (`p > 0`, `k >= 0`)
/// plus `p <= m_width` and mantissa normalization (`m == 0` or
/// `2^(p-1) <= |m| < 2^p`). `e`-consistency follows automatically from
/// normalization (`|c| = |m|·2^(e-p+1)`); `m == 0` leaves `e` free (zero
/// special, rev3 §10.1(a)). Conjoined on every operand and result of
/// `erealAdd/Sub/Mul/Div`, so denormalized lanes are UNSAT at the point
/// of use. `k < p` is NOT part of the core: intermediate precision loss
/// (`k >= p`) must stay representable for `erealNeedsRefine`/CEGAR;
/// only division denominators additionally require `k < p`
/// (`ereal_div_guard`) plus `m != 0`.
fn ereal_valid_core(x: &ERealOp, wv: u32, m_width: u32) -> Formula {
    ereal_and_all(vec![
        ereal_wellformed(x),
        ereal_icmp(
            IntCmpOp::Lte,
            ereal_lane_of(x, "p"),
            ereal_lit(m_width as i64),
        ),
        ereal_result_normalized(x, wv, m_width),
    ])
}

/// Strict goal-state `Valid`: core plus `k < p` (rev3 §5). Exposed as the
/// `erealValid` predicate for users who want to assert a fully-precise
/// value; not conjoined internally (see `ereal_valid_core`).
fn ereal_valid_strict(x: &ERealOp, wv: u32, m_width: u32) -> Formula {
    ereal_and_all(vec![
        ereal_valid_core(x, wv, m_width),
        ereal_icmp(
            IntCmpOp::Lt,
            ereal_lane_of(x, "k"),
            ereal_lane_of(x, "p"),
        ),
    ])
}

/// Multiplication (§4): `C = e1+e2 + M + extra` with B2 dominant-term
/// tightening (`extra = 1` iff the dominant term leads both others by
/// >= 2, else 2 — mirror of `int_ext::mul_c`), 3-way max split.
/// Plus a centre window pin and Valid operands/results
/// (Phase 2; see `ereal_mul_window`).
/// The `k'` path is end-to-end widening-exact (P2-2; see `ereal_add_sub`).
fn ereal_mul(a: &ERealOp, b: &ERealOp, r: &ERealOp, wv: u32, m_width: u32) -> Formula {
    let (ea, pa, ka) = (ereal_lane_of(a, "e"), ereal_lane_of(a, "p"), ereal_lane_of(a, "k"));
    let (eb, pb, kb) = (ereal_lane_of(b, "e"), ereal_lane_of(b, "p"), ereal_lane_of(b, "k"));
    let (er, pr, kr) = (ereal_lane_of(r, "e"), ereal_lane_of(r, "p"), ereal_lane_of(r, "k"));
    let t1 = ereal_wadd(ereal_wsub(ka.clone(), pa.clone()), ereal_lit(1));
    let t2 = ereal_wadd(ereal_wsub(kb.clone(), pb.clone()), ereal_lit(1));
    let t3 = ereal_wsub(
        ereal_wadd(ka.clone(), kb.clone()),
        ereal_wadd(pa.clone(), pb.clone()),
    );
    let base = ereal_wadd(ea.clone(), eb.clone());
    let b_exp = ereal_wsub(er, pr.clone());
    let gap_ge2 = |x: &IntExpr, y: &IntExpr| {
        ereal_icmp(
            IntCmpOp::Gt,
            ereal_wsub(x.clone(), y.clone()),
            ereal_lit(1),
        )
    };
    let gap_le1 = |x: &IntExpr, y: &IntExpr| {
        ereal_icmp(
            IntCmpOp::Lte,
            ereal_wsub(x.clone(), y.clone()),
            ereal_lit(1),
        )
    };
    let case = |dom: &IntExpr, lo1: Formula, lo2: Formula, o1: &IntExpr, o2: &IntExpr| {
        ereal_or_all(vec![
            // Separated: both gaps >= 2, tight `+ 1`.
            ereal_and_all(vec![
                lo1.clone(),
                lo2.clone(),
                gap_ge2(dom, o1),
                gap_ge2(dom, o2),
                ereal_combine_eq_wide(
                    &kr,
                    &ereal_wadd(ereal_wadd(base.clone(), dom.clone()), ereal_lit(1)),
                    &b_exp,
                ),
            ]),
            // Close: some gap <= 1, conservative `+ 2`.
            ereal_and_all(vec![
                lo1,
                lo2,
                ereal_or_all(vec![gap_le1(dom, o1), gap_le1(dom, o2)]),
                ereal_combine_eq_wide(
                    &kr,
                    &ereal_wadd(ereal_wadd(base.clone(), dom.clone()), ereal_lit(2)),
                    &b_exp,
                ),
            ]),
        ])
    };
    ereal_and_all(vec![
        ereal_valid_core(a, wv, m_width),
        ereal_valid_core(b, wv, m_width),
        ereal_valid_core(r, wv, m_width),
        ereal_min_eq(&pr, &pa, &pb),
        ereal_or_all(vec![
            case(
                &t1,
                ereal_icmp(IntCmpOp::Gte, t1.clone(), t2.clone()),
                ereal_icmp(IntCmpOp::Gte, t1.clone(), t3.clone()),
                &t2,
                &t3,
            ),
            case(
                &t2,
                ereal_icmp(IntCmpOp::Gt, t2.clone(), t1.clone()),
                ereal_icmp(IntCmpOp::Gte, t2.clone(), t3.clone()),
                &t1,
                &t3,
            ),
            case(
                &t3,
                ereal_icmp(IntCmpOp::Gt, t3.clone(), t1.clone()),
                ereal_icmp(IntCmpOp::Gt, t3.clone(), t2.clone()),
                &t1,
                &t2,
            ),
        ]),
        ereal_mul_window(a, b, r, wv),
    ])
}

/// `max(x, y)` over integer expressions (desugar-internal `Max`: exact
/// choice-based circuit, never wraps — unlike `Add`/`Sub`, which wrap at
/// the problem bitwidth).
fn ereal_max(a: IntExpr, b: IntExpr) -> IntExpr {
    IntExpr::Bin(IntBinOp::Max, Box::new(a), Box::new(b))
}

/// `k = combine_k(a, b)` with exact widening arithmetic (see
/// `ereal_combine_eq` for the wrapping variant). Used on the div `k'`
/// path so the P0-1 rounding budget is end-to-end exact.
fn ereal_combine_eq_wide(k: &IntExpr, a: &IntExpr, b: &IntExpr) -> Formula {
    let d = ereal_wsub(a.clone(), b.clone());
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
                ereal_wadd(d, ereal_lit(1)),
            ),
        ]),
    ])
}
/// Centre window pin for multiplication (Phase 2):
/// `|c_r − c_a·c_b| ≤ 2^B` with `B = e_r − p_r`, scaled to the common
/// exponent `s0 = min(lsb_r, lsb_a+lsb_b, B)`. The mantissa product uses
/// exact widening multiplication (`WidenOp::Mul`, never the wrapping
/// `IntBinOp::Mul`).
///
/// Soundness: `|x1·x2 − c_a·c_b| ≤ 2^C` (doc §4; needs `|m| < 2^p` on
/// both operands, i.e. `ereal_valid_core`) plus `|c_r − c_a·c_b| ≤ 2^B`
/// (this constraint) give `|x1·x2 − c_r| ≤ 2^C + 2^B ≤ R'` with the
/// unchanged `k' = combine_k(C, B)`.
fn ereal_mul_window(a: &ERealOp, b: &ERealOp, r: &ERealOp, wv: u32) -> Formula {
    let lsb_ab = ereal_wadd(ereal_lsb_wide(a), ereal_lsb_wide(b));
    let lsb_r = ereal_lsb_wide(r);
    let b_exp = IntExpr::Widen(
        WidenOp::Sub,
        Box::new(ereal_lane_of(r, "e")),
        Box::new(ereal_lane_of(r, "p")),
    );
    let s0 = ereal_min(
        ereal_min(lsb_r.clone(), lsb_ab.clone()),
        b_exp.clone(),
    );
    let prod = ereal_wmul(ereal_lane_of(a, "m"), ereal_lane_of(b, "m"));
    let cr = ereal_wshl(ereal_lane_of(r, "m"), ereal_wsub(lsb_r, s0.clone()), wv);
    let cp = ereal_wshl(prod, ereal_wsub(lsb_ab, s0.clone()), wv);
    let diff = ereal_wsub(cr, cp);
    let bound = ereal_wshl(IntExpr::Lit(1, 0), ereal_wsub(b_exp, s0), wv);
    ereal_and_all(vec![
        ereal_icmp(IntCmpOp::Lte, diff.clone(), bound.clone()),
        ereal_icmp(IntCmpOp::Lte, ereal_wneg(bound), diff),
    ])
}

/// Division (§5 + rev2 §9.1(a) + P0-1 Q-fix + B3 tightening):
/// `D = e1-e2 + max(u1,u2) + extra` with `extra = 2` iff `|u1-u2| >= 2`,
/// else 3 (mirror of `int_ext::div_d`), split into two disjoint branches.
/// Plus the `divGuard` conjunct and an `m_b != 0` conjunct (violations are
/// UNSAT: no finite bound absorbs a denominator interval spanning zero;
/// exact cancellation `m == 0` has infinite relative error even when
/// `k < p` holds).
/// Plus a centre window pin, operand bounds, denominator normalization,
/// and result normalization (Phase 2; see `ereal_div_window`).
/// The `k'` path is end-to-end widening-exact and uses the corrected
/// input-error budget `D' = max(D, Q) + 1` (`Q = q_lsb − 1` is the scaled
/// pre-rounding exponent; omitting it is unsound — see `mepk_div`).
/// `guard` is the caller's `MepkWidths::guard` as a literal.
fn ereal_div(a: &ERealOp, b: &ERealOp, r: &ERealOp, wv: u32, m_width: u32, guard: u32) -> Formula {
    let (ea, pa, ka) = (ereal_lane_of(a, "e"), ereal_lane_of(a, "p"), ereal_lane_of(a, "k"));
    let (eb, pb, kb) = (ereal_lane_of(b, "e"), ereal_lane_of(b, "p"), ereal_lane_of(b, "k"));
    let (er, pr, kr) = (ereal_lane_of(r, "e"), ereal_lane_of(r, "p"), ereal_lane_of(r, "k"));
    // B3: `D = base + max(u1, u2) + extra` with `extra = 2` iff
    // `|u1 - u2| >= 2`, else 3 (mirror of `int_ext::div_d`),
    // all widening-exact. Two disjoint branches (integers: either both
    // diffs `<= 1`, or some diff `>= 2`), each with its own budget.
    let u1 = ereal_wsub(ka.clone(), pa.clone());
    let u2 = ereal_wsub(kb.clone(), pb.clone());
    let d_base = ereal_wadd(
        ereal_wsub(ea.clone(), eb.clone()),
        ereal_max(u1.clone(), u2.clone()),
    );
    let d_tight = ereal_wadd(d_base.clone(), ereal_lit(2));
    let d_loose = ereal_wadd(d_base, ereal_lit(3));
    // `D' = max(D, Q) + 1` with `Q = lsb_a − lsb_b − guard − 1`
    // (exact wide scales).
    let lsb_a = ereal_lsb_wide(a);
    let lsb_b = ereal_lsb_wide(b);
    let b_wide = ereal_wsub(er.clone(), pr.clone());
    let q_exp = ereal_wsub(
        ereal_wsub(
            ereal_wsub(lsb_a, lsb_b),
            ereal_lit(guard as i64),
        ),
        ereal_lit(1),
    );
    // `D' = max(D, Q) + 1` per branch (`Q = lsb_a − lsb_b − guard − 1`,
    // exact wide scales); `k' = combine(D', B)` is pinned per branch.
    let star = |d: &IntExpr| {
        ereal_wadd(
            ereal_max(d.clone(), q_exp.clone()),
            ereal_lit(1),
        )
    };
    let separated = ereal_or_all(vec![
        ereal_icmp(
            IntCmpOp::Gt,
            ereal_wsub(u1.clone(), u2.clone()),
            ereal_lit(1),
        ),
        ereal_icmp(
            IntCmpOp::Gt,
            ereal_wsub(u2.clone(), u1.clone()),
            ereal_lit(1),
        ),
    ]);
    let close = ereal_and_all(vec![
        ereal_icmp(
            IntCmpOp::Lte,
            ereal_wsub(u1.clone(), u2.clone()),
            ereal_lit(1),
        ),
        ereal_icmp(
            IntCmpOp::Lte,
            ereal_wsub(u2.clone(), u1.clone()),
            ereal_lit(1),
        ),
    ]);
    let k_branch = ereal_or_all(vec![
        ereal_and_all(vec![
            separated,
            ereal_combine_eq_wide(&kr, &star(&d_tight), &b_wide),
        ]),
        ereal_and_all(vec![
            close,
            ereal_combine_eq_wide(&kr, &star(&d_loose), &b_wide),
        ]),
    ]);
    ereal_and_all(vec![
        ereal_valid_core(a, wv, m_width),
        // Denominator: Valid core (normalization makes the `k < p` guard
        // sufficient — a denormalized `m` could span zero at `k < p`) plus
        // the strict domain conjuncts below.
        ereal_valid_core(b, wv, m_width),
        ereal_valid_core(r, wv, m_width),
        ereal_div_guard(b),
        // rev2 §9.1(a): denominator centre exactly zero is always
        // out of domain, even when `k < p` holds.
        ereal_icmp(IntCmpOp::Neq, ereal_lane_of(b, "m"), ereal_lit(0)),
        ereal_min_eq(&pr, &pa, &pb),
        k_branch,
        ereal_div_window(a, b, r, wv),
    ])
}

/// Centre window pin for division (Phase 2): `|c_r − c_a/c_b| ≤ 2^B`
/// with `B = e_r − p_r`, written without a division circuit by
/// cross-multiplying: `|c_r·c_b − c_a| ≤ 2^B·|c_b|`, scaled to the common
/// exponent `s0 = min(lsb_r+lsb_b, lsb_a, B+lsb_b)`. The two products use
/// exact widening multiplication. `|m_b|` is `±m_b` by a case split on
/// the denominator sign (`m_b ≠ 0` is conjoined separately).
///
/// Soundness: `|x_a/x_b − c_a/c_b| ≤ 2^D` (doc §5; needs `Valid` operands
/// via `ereal_valid_core` — in particular a normalized nonzero
/// denominator — and `k_b < p_b`) plus the window bound
/// give `|x_a/x_b − c_r| ≤ 2^D + 2^B ≤ R'` with the unchanged
/// `k' = combine_k(D, B)`.
fn ereal_div_window(a: &ERealOp, b: &ERealOp, r: &ERealOp, wv: u32) -> Formula {
    let lsb_a = ereal_lsb_wide(a);
    let lsb_b = ereal_lsb_wide(b);
    let lsb_rb = ereal_wadd(ereal_lsb_wide(r), lsb_b.clone());
    let b_exp = IntExpr::Widen(
        WidenOp::Sub,
        Box::new(ereal_lane_of(r, "e")),
        Box::new(ereal_lane_of(r, "p")),
    );
    let bl = ereal_wadd(b_exp.clone(), lsb_b.clone());
    let s0 = ereal_min(
        ereal_min(lsb_rb.clone(), lsb_a.clone()),
        bl.clone(),
    );
    // `lhs = m_r·m_b·2^(lsb_r+lsb_b) − m_a·2^lsb_a` (sign-independent).
    let lhs = ereal_wsub(
        ereal_wshl(
            ereal_wmul(ereal_lane_of(r, "m"), ereal_lane_of(b, "m")),
            ereal_wsub(lsb_rb, s0.clone()),
            wv,
        ),
        ereal_wshl(ereal_lane_of(a, "m"), ereal_wsub(lsb_a, s0.clone()), wv),
    );
    // `rhs = |m_b|·2^(B+lsb_b)`; one case per denominator sign.
    let window = |am2: IntExpr| {
        let rhs = ereal_wshl(am2, ereal_wsub(bl.clone(), s0.clone()), wv);
        ereal_and_all(vec![
            ereal_icmp(IntCmpOp::Lte, lhs.clone(), rhs.clone()),
            ereal_icmp(IntCmpOp::Lte, ereal_wneg(rhs), lhs.clone()),
        ])
    };
    let m2 = ereal_lane_of(b, "m");
    ereal_or_all(vec![
        ereal_and_all(vec![
            ereal_icmp(IntCmpOp::Gt, m2.clone(), ereal_lit(0)),
            window(m2.clone()),
        ]),
        ereal_and_all(vec![
            ereal_icmp(IntCmpOp::Lt, m2.clone(), ereal_lit(0)),
            window(ereal_wneg(m2)),
        ]),
    ])
}


/// `setEReal[x, lit]`: bind `x`'s lanes to the optimal conversion of
/// the decimal literal (same conversion as `:mepk lit` at `max_p`).
/// Desugars to four lane equalities; the literal text is never rounded
/// through `f64`. Out-of-range literals fail loudly at lowering.
fn ereal_set(x: &Expr, lit: &Expr, max_p: u32) -> LResult<Formula> {
    let s = match lit {
        Expr::RealLit(s, _) | Expr::ApproxRealLit(s, _) => s.clone(),
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

// ---- builtin `Real` desugar (exact-centre counterparts) --------------------
// `Real` values are `c = m * 2^e` with `m == 0 || odd(m)` (shared `m`/`e`
// lanes with `EReal`). All arithmetic is exact: scaled to a common
// exponent `s0 = min(...)` (same widening pattern as `ereal_scaled_cmp`),
// so every shift amount is non-negative. Division cross-multiplies
// (`a == r*b`), hence exact with no remainder check.

/// A `Real` operand: atom-valued expression (lane joins) or a constant
/// centre (`RealConstant`, fixed `(m, e)`, no universe atom).
#[derive(Clone, Copy)]
enum RealOp<'e> {
    Ref(&'e Expr),
    Const(RealCenter),
}

/// Lane read through a `Real` operand.
// FLAT-EXPERIMENT: atom operands read through the bit partition
// (`x & $M`), not the `Real.m` join.
fn real_lane_of(op: &RealOp, lane: &str) -> IntExpr {
    match op {
        RealOp::Ref(e) => match lane {
            "m" => IntExpr::BitsVal(Box::new(flat_partition_read(e, "$M")), 0),
            "e" => IntExpr::BitsVal(Box::new(flat_partition_read(e, "$E")), 0),
            _ => unreachable!("unknown Real lane {lane}"),
        },
        RealOp::Const(v) => {
            let n = match lane {
                "m" => v.m as i64,
                "e" => v.e as i64,
                _ => unreachable!("unknown Real lane {lane}"),
            };
            ereal_lit(n)
        }
    }
}

/// `Real` wellformedness: `m == 0` or odd `m` (even check via
/// `(m/2)*2 == m` is exact under any Div semantics, so `!=` means odd).
fn real_wellformed(x: &RealOp) -> Formula {
    let m = real_lane_of(x, "m");
    let half = IntExpr::Bin(
        IntBinOp::Div,
        Box::new(m.clone()),
        Box::new(ereal_lit(2)),
    );
    let twice = IntExpr::Bin(IntBinOp::Mul, Box::new(half), Box::new(ereal_lit(2)));
    ereal_or_all(vec![
        ereal_icmp(IntCmpOp::Eq, m.clone(), ereal_lit(0)),
        ereal_icmp(IntCmpOp::Neq, twice, m),
    ])
}

fn real_all_wellformed(ops: &[&RealOp]) -> Vec<Formula> {
    ops.iter().map(|o| real_wellformed(o)).collect()
}

/// Exact scaled equality of two centres at `s0 = min(e_a, e_b)`.
fn real_scaled_eq(a: &RealOp, b: &RealOp, wv: u32) -> Formula {
    let ea = real_lane_of(a, "e");
    let eb = real_lane_of(b, "e");
    let s0 = ereal_min(ea.clone(), eb.clone());
    let ca = ereal_wshl(real_lane_of(a, "m"), ereal_wsub(ea, s0.clone()), wv);
    let cb = ereal_wshl(real_lane_of(b, "m"), ereal_wsub(eb, s0), wv);
    ereal_icmp(IntCmpOp::Eq, ca, cb)
}

/// Exact scaled comparison `a OP b` at `s0 = min(e_a, e_b)`.
fn real_scaled_cmp(a: &RealOp, b: &RealOp, op: IntCmpOp, wv: u32) -> Formula {
    let ea = real_lane_of(a, "e");
    let eb = real_lane_of(b, "e");
    let s0 = ereal_min(ea.clone(), eb.clone());
    let ca = ereal_wshl(real_lane_of(a, "m"), ereal_wsub(ea, s0.clone()), wv);
    let cb = ereal_wshl(real_lane_of(b, "m"), ereal_wsub(eb, s0), wv);
    ereal_icmp(op, ca, cb)
}

/// Exact addition / subtraction: `m_r·2^e_r == m_a·2^e_a ± m_b·2^e_b`
/// scaled to `s0 = min(e_a, e_b, e_r)`.
fn real_add_sub(a: &RealOp, b: &RealOp, r: &RealOp, sign: i8, wv: u32) -> Formula {
    let ea = real_lane_of(a, "e");
    let eb = real_lane_of(b, "e");
    let er = real_lane_of(r, "e");
    let s0 = ereal_min(ereal_min(ea.clone(), eb.clone()), er.clone());
    let ca = ereal_wshl(real_lane_of(a, "m"), ereal_wsub(ea, s0.clone()), wv);
    let cb = ereal_wshl(real_lane_of(b, "m"), ereal_wsub(eb, s0.clone()), wv);
    let cr = ereal_wshl(real_lane_of(r, "m"), ereal_wsub(er, s0), wv);
    let s = if sign == 1 {
        ereal_wadd(ca, cb)
    } else {
        ereal_wsub(ca, cb)
    };
    let mut parts = real_all_wellformed(&[a, b, r]);
    parts.push(ereal_icmp(IntCmpOp::Eq, cr, s));
    ereal_and_all(parts)
}

/// Exact multiplication: `(m_a·m_b)·2^(e_a+e_b) == m_r·2^e_r`
/// scaled to `s0 = min(e_a+e_b, e_r)`.
fn real_mul(a: &RealOp, b: &RealOp, r: &RealOp, wv: u32) -> Formula {
    let eab = ereal_wadd(real_lane_of(a, "e"), real_lane_of(b, "e"));
    let er = real_lane_of(r, "e");
    let s0 = ereal_min(eab.clone(), er.clone());
    let lhs = ereal_wshl(
        ereal_wmul(real_lane_of(a, "m"), real_lane_of(b, "m")),
        ereal_wsub(eab, s0.clone()),
        wv,
    );
    let rhs = ereal_wshl(real_lane_of(r, "m"), ereal_wsub(er, s0), wv);
    let mut parts = real_all_wellformed(&[a, b, r]);
    parts.push(ereal_icmp(IntCmpOp::Eq, lhs, rhs));
    ereal_and_all(parts)
}

/// Exact division by cross-multiplication:
/// `m_a·2^e_a == (m_r·m_b)·2^(e_r+e_b)`, plus `m_b != 0`.
fn real_div(a: &RealOp, b: &RealOp, r: &RealOp, wv: u32) -> Formula {
    let ea = real_lane_of(a, "e");
    let erb = ereal_wadd(real_lane_of(r, "e"), real_lane_of(b, "e"));
    let s0 = ereal_min(ea.clone(), erb.clone());
    let lhs = ereal_wshl(real_lane_of(a, "m"), ereal_wsub(ea, s0.clone()), wv);
    let rhs = ereal_wshl(
        ereal_wmul(real_lane_of(r, "m"), real_lane_of(b, "m")),
        ereal_wsub(erb, s0),
        wv,
    );
    let mut parts = real_all_wellformed(&[a, b, r]);
    parts.push(ereal_icmp(
        IntCmpOp::Neq,
        real_lane_of(b, "m"),
        ereal_lit(0),
    ));
    parts.push(ereal_icmp(IntCmpOp::Eq, lhs, rhs));
    ereal_and_all(parts)
}

/// `setReal[x, lit]`: bind `x`'s `(m, e)` lanes to the exact dyadic
/// conversion. Non-dyadic literals fail loudly (no rounding; use the
/// `setRealNearest/Down/Up` variants below).
/// Signed range of a lane of `w` bits (two's complement).
fn lane_range(w: u32) -> (i64, i64) {
    if w == 0 {
        return (0, 0);
    }
    if w >= 63 {
        return (i64::MIN, i64::MAX);
    }
    (-(1i64 << (w - 1)), (1i64 << (w - 1)) - 1)
}

/// FLAT-EXPERIMENT: pin a `Real` value's lane through the bit
/// partition (`x & $M`), not the `Real.m` join.
fn real_pin(x: &Expr, lane: &str, v: i64) -> Formula {
    let part = match lane {
        "m" => "$M",
        "e" => "$E",
        _ => unreachable!("unknown Real lane {lane}"),
    };
    Formula::IntCmp(
        IntCmpOp::Eq,
        IntExpr::BitsVal(Box::new(flat_partition_read(x, part)), 0),
        IntExpr::Lit(v, 0),
        0,
    )
}

fn real_set(x: &Expr, lit: &Expr, m_width: u32) -> LResult<Formula> {
    // Plain `d`: exact dyadic only; non-dyadic-but-approximable is UNSAT
    // (no dyadic centre equals it). `(d)`: nearest binding.
    // Malformed/range literals still fail loudly.
    let (s, approx) = match lit {
        Expr::RealLit(s, _) => (s.clone(), false),
        Expr::ApproxRealLit(s, _) => (s.clone(), true),
        _ => {
            return Err(FrontError::Resolve(
                "setReal expects a decimal literal (e.g. 0.5) or (0.1) as its second argument".to_string(),
            ))
        }
    };
    if approx {
        let v = decimal_to_real_rounded(&s, Some(m_width), RealRound::Nearest).ok_or_else(|| {
            FrontError::Resolve(format!(
                "setReal: cannot convert ({s:?}) (malformed or outside the lane range)"
            ))
        })?;
        return Ok(ereal_and_all(vec![
            real_pin(x, "m", v.m as i64),
            real_pin(x, "e", v.e as i64),
        ]));
    }
    if let Some(v) = decimal_to_real(&s, Some(m_width)) {
        return Ok(ereal_and_all(vec![
            real_pin(x, "m", v.m as i64),
            real_pin(x, "e", v.e as i64),
        ]));
    }
    if decimal_to_real_rounded(&s, Some(m_width), RealRound::Nearest).is_some() {
        return Ok(Formula::Const(false));
    }
    Err(FrontError::Resolve(format!(
        "setReal: cannot convert {s:?} exactly (malformed or outside the lane range)"
    )))
}

/// `setRealNearest/Down/Up[x, lit]`: bind `x`'s `(m, e)` lanes to the
/// `m`-width rounded conversion of the decimal literal. Dyadic inputs
/// are exact in every mode; non-dyadic inputs round to nearest
/// (half-even), toward −inf, or toward +inf respectively. The rounding
/// error itself is NOT tracked (unlike `EReal`'s `k`): bracket a value
/// with Down+Up when the error matters.
fn real_set_rounded(x: &Expr, lit: &Expr, m_width: u32, mode: RealRound, name: &str) -> LResult<Formula> {
    let s = match lit {
        Expr::RealLit(s, _) | Expr::ApproxRealLit(s, _) => s.clone(),
        _ => {
            return Err(FrontError::Resolve(format!(
                "{name} expects a decimal literal (e.g. 0.1) as its second argument"
            )))
        }
    };
    let v = decimal_to_real_rounded(&s, Some(m_width), mode).ok_or_else(|| {
        FrontError::Resolve(format!(
            "{name}: cannot convert {s:?} (malformed or outside the lane range)"
        ))
    })?;
    Ok(ereal_and_all(vec![
        real_pin(x, "m", v.m as i64),
        real_pin(x, "e", v.e as i64),
    ]))
}

// ---- lane-successor constraints (`realSucc`/`realPred` core) --------------
// Successor over the finite lane population without quantifiers or
// division-on-wide: per static scale offset `c`, the optimum mantissa
// is built from `Div`/`Rem` on lane-small non-negative values only
// (all wider arithmetic is widened-exact), with parity folded through
// `r²` (`r = Rem(_, 2) ∈ {-1,0,1}`, so `r² = [odd]` under any Div
// semantics); global minimality/maximality is pairwise across scales.
// Static `2^k` constants come from doubling chains (`Lit(2^k)` would
// wrap once `k ≥ E-1`).

/// Exact constant shift-left (free rewiring, no gates, no amount
/// encoding): `x · 2^k` for static `k`.
fn real_shl(x: IntExpr, k: u32) -> IntExpr {
    IntExpr::Widen(
        WidenOp::ShlConst(k),
        Box::new(x),
        Box::new(IntExpr::Lit(0, 0)),
    )
}

/// Widen `x` (exact identity shift, for mixed-width comparisons).
fn real_wide(x: IntExpr) -> IntExpr {
    real_shl(x, 0)
}

/// Static integer as a widened exact value via binary decomposition
/// into constant shifts of one (avoids `Lit` wrap for magnitudes
/// `≥ 2^(E-1)`; avoids the exponential doubling-table trees).
fn real_small(k: i64) -> IntExpr {
    if k == 0 {
        return IntExpr::Lit(0, 0);
    }
    let neg = k < 0;
    let mut mag = k.unsigned_abs();
    let mut acc: Option<IntExpr> = None;
    let mut b = 0u32;
    while mag > 0 {
        if mag & 1 == 1 {
            let p = real_shl(IntExpr::Lit(1, 0), b);
            acc = Some(match acc {
                None => p,
                Some(a) => IntExpr::Widen(WidenOp::Add, Box::new(a), Box::new(p)),
            });
        }
        mag >>= 1;
        b += 1;
    }
    let pos = acc.unwrap_or(IntExpr::Lit(0, 0));
    if neg {
        IntExpr::Widen(
            WidenOp::Sub,
            Box::new(IntExpr::Lit(0, 0)),
            Box::new(pos),
        )
    } else {
        pos
    }
}

/// One per-scale candidate: lane equalities pinning the optimum at
/// this scale, its value for pairwise ordering (`val_m` at static
/// scale offset `off`), and its lane-feasibility gate (`feas`).
/// Gates are load-bearing for pairwise targets: an infeasible scale
/// (mantissa overfull or exponent out of lane) still computes a
/// formula value, typically just above the input, which would
/// spuriously kill the true optimum without gating.
struct RealScaleCand {
    eqs: Vec<Formula>,
    val_m: IntExpr,
    off: i64,
    feas: Option<Formula>,
}

/// Lane-feasibility gate for a per-scale optimum at static offset `c`:
/// the mantissa fits (`m2 ≤ mag_max`) and the exponent lands in lane
/// (`emin ≤ e_a + c ≤ emax`), all widened-exact.
fn real_scale_feas(
    m2_w: &IntExpr,
    ex_w: &IntExpr,
    c: i64,
    mag_max: i64,
    emin: i64,
    emax: i64,
) -> Formula {
    let esc = IntExpr::Widen(
        WidenOp::Add,
        Box::new(ex_w.clone()),
        Box::new(real_small(c)),
    );
    ereal_and_all(vec![
        ereal_icmp(IntCmpOp::Lte, m2_w.clone(), real_wide(IntExpr::Lit(mag_max, 0))),
        ereal_icmp(IntCmpOp::Lte, real_wide(IntExpr::Lit(emin, 0)), esc.clone()),
        ereal_icmp(IntCmpOp::Lte, esc, real_wide(IntExpr::Lit(emax, 0))),
    ])
}

/// Per-scale successor optimum at static offset `c` (`e' = e_a + c`)
/// for strictly positive input lanes (`mx > 0` guarded outside):
/// smallest odd `m''` above `t = mx/2^c`, as
/// `m'' = q + 1 + r²` with `q = Div(mx, 2^c)`, `r = Rem(q, 2)`
/// (branch-free odd rounding; `Div` divisor folded to `q = 0` when
/// `2^c` cannot fit the problem width, where `t < 1` forces `m'' = 1`).
/// No cap construction: overshoot implies the scale is infeasible
/// (nothing in-lane lies above `t`), covered by the gate.
fn real_succ_scale(
    mx: &IntExpr,
    ex_w: &IntExpr,
    my_w: &IntExpr,
    ey_w: &IntExpr,
    c: i64,
    ebits: u32,
    mag_max: i64,
    emin: i64,
    emax: i64,
) -> RealScaleCand {
    let m2 = if c >= 0 && c >= (ebits as i64) - 1 {
        // `2^c` exceeds the lane domain: `t < 1`, so the optimum is 1.
        real_wide(IntExpr::Lit(1, 0))
    } else if c >= 0 {
        let two_c = IntExpr::Lit(1i64 << (c as u32), 0);
        let q = IntExpr::Bin(IntBinOp::Div, Box::new(mx.clone()), Box::new(two_c.clone()));
        let two = IntExpr::Lit(2, 0);
        let r = IntExpr::Bin(IntBinOp::Rem, Box::new(q.clone()), Box::new(two));
        let r2 = IntExpr::Widen(WidenOp::Mul, Box::new(r.clone()), Box::new(r));
        let qw = real_wide(q);
        let r2w = real_wide(r2);
        IntExpr::Widen(
            WidenOp::Add,
            Box::new(IntExpr::Widen(
                WidenOp::Add,
                Box::new(qw),
                Box::new(r2w),
            )),
            Box::new(real_wide(IntExpr::Lit(1, 0))),
        )
    } else {
        // `t = mx·2^|c|` exact (free rewiring); unified odd-rounding
        // on `q = t` (`r²` kills the truncation sign; parity survives).
        let t = real_shl(mx.clone(), (-c) as u32);
        let r = IntExpr::Bin(
            IntBinOp::Rem,
            Box::new(t.clone()),
            Box::new(IntExpr::Lit(2, 0)),
        );
        let r2 = IntExpr::Widen(WidenOp::Mul, Box::new(r.clone()), Box::new(r));
        IntExpr::Widen(
            WidenOp::Add,
            Box::new(IntExpr::Widen(WidenOp::Add, Box::new(t), Box::new(r2))),
            Box::new(real_wide(IntExpr::Lit(1, 0))),
        )
    };
    let e_pin = real_small(c);
    let eqs = vec![
        ereal_icmp(IntCmpOp::Eq, my_w.clone(), m2.clone()),
        ereal_icmp(
            IntCmpOp::Eq,
            ey_w.clone(),
            IntExpr::Widen(WidenOp::Add, Box::new(ex_w.clone()), Box::new(e_pin)),
        ),
    ];
    let feas = real_scale_feas(&m2, ex_w, c, mag_max, emin, emax);
    RealScaleCand {
        eqs,
        val_m: m2,
        off: c,
        feas: Some(feas),
    }
}

/// Per-scale predecessor optima at static offset `c` for strictly
/// positive input: largest below `t`, as up to two gated mains —
/// - fit-main: `Q = Div(mx - 1, 2^c) > 0` with `m'' = Q - 1 + r²`
///   (`r = Rem(Q, 2)`), gated on `Q ≠ 0`, mantissa fit, exponent fit;
/// - cap-main: the lane cap `MAG` itself when it lies below `t`
///   (`MAG·2^c < mx`, needed when the formula overshoots the lane),
///   gated on that strict below-ness plus exponent fit.
/// (The zero answer is a separate global disjunct built by the caller:
/// all mains infeasible.) `Div` divisor folded to `Q = 0` when `2^c`
/// cannot fit the problem width (then only the zero case applies).
/// Returns the mains (each with its gate).
fn real_pred_scale(
    mx: &IntExpr,
    ex_w: &IntExpr,
    my_w: &IntExpr,
    ey_w: &IntExpr,
    c: i64,
    ebits: u32,
    mag_max: i64,
    emin: i64,
    emax: i64,
) -> Vec<RealScaleCand> {
    let e_pin = || {
        ereal_icmp(
            IntCmpOp::Eq,
            ey_w.clone(),
            IntExpr::Widen(
                WidenOp::Add,
                Box::new(ex_w.clone()),
                Box::new(real_small(c)),
            ),
        )
    };
    let e_fit = || {
        let esc = IntExpr::Widen(
            WidenOp::Add,
            Box::new(ex_w.clone()),
            Box::new(real_small(c)),
        );
        ereal_and_all(vec![
            ereal_icmp(IntCmpOp::Lte, real_wide(IntExpr::Lit(emin, 0)), esc.clone()),
            ereal_icmp(IntCmpOp::Lte, esc, real_wide(IntExpr::Lit(emax, 0))),
        ])
    };
    let mag_w = real_wide(IntExpr::Lit(mag_max, 0));
    let mut out = Vec::new();
    if c >= 0 && c >= (ebits as i64) - 1 {
        // `t < 1`: no positive optimum at this scale (zero is global).
        return out;
    }
    // Fit-main: `Q = floor((mx-1)/2^c)`, gate `Q ≠ 0`.
    let q: IntExpr = if c >= 0 {
        let two_c = IntExpr::Lit(1i64 << (c as u32), 0);
        IntExpr::Bin(
            IntBinOp::Div,
            Box::new(IntExpr::Bin(
                IntBinOp::Sub,
                Box::new(mx.clone()),
                Box::new(IntExpr::Lit(1, 0)),
            )),
            Box::new(two_c),
        )
    } else {
        // `t = mx·2^|c|` exact rewiring; `Q = t - 1` (largest int
        // below, `t` integral here).
        IntExpr::Widen(
            WidenOp::Sub,
            Box::new(real_shl(mx.clone(), (-c) as u32)),
            Box::new(real_wide(IntExpr::Lit(1, 0))),
        )
    };
    let gate_nz = ereal_icmp(IntCmpOp::Neq, q.clone(), IntExpr::Lit(0, 0));
    let r = IntExpr::Bin(
        IntBinOp::Rem,
        Box::new(q.clone()),
        Box::new(IntExpr::Lit(2, 0)),
    );
    let r2 = IntExpr::Widen(WidenOp::Mul, Box::new(r.clone()), Box::new(r));
    let qw = real_wide(q.clone());
    let m2 = IntExpr::Widen(
        WidenOp::Sub,
        Box::new(IntExpr::Widen(WidenOp::Add, Box::new(qw), Box::new(r2))),
        Box::new(real_wide(IntExpr::Lit(1, 0))),
    );
    let fit_gate = ereal_and_all(vec![
        gate_nz,
        ereal_icmp(IntCmpOp::Lte, m2.clone(), mag_w.clone()),
        e_fit(),
    ]);
    out.push(RealScaleCand {
        eqs: vec![
            ereal_icmp(IntCmpOp::Eq, my_w.clone(), m2.clone()),
            e_pin(),
        ],
        val_m: m2,
        off: c,
        feas: Some(fit_gate),
    });
    // Cap-main: `MAG` itself, gated on strict below-ness at this scale
    // plus exponent fit (covers formula overshoot of the lane).
    let cap_below = if c >= 0 {
        ereal_icmp(
            IntCmpOp::Lt,
            real_shl(mag_w.clone(), c as u32),
            real_wide(mx.clone()),
        )
    } else {
        ereal_icmp(
            IntCmpOp::Lt,
            mag_w.clone(),
            real_shl(real_wide(mx.clone()), (-c) as u32),
        )
    };
    let cap_gate = ereal_and_all(vec![cap_below, e_fit()]);
    out.push(RealScaleCand {
        eqs: vec![
            ereal_icmp(IntCmpOp::Eq, my_w.clone(), mag_w.clone()),
            e_pin(),
        ],
        val_m: mag_w,
        off: c,
        feas: Some(cap_gate),
    });
    out
}

/// Pairwise ordering across per-scale candidates at balance shift `k`:
/// `b ≤ V` for successor (`up`), `b ≥ V` for predecessor, scaled by
/// exact constant shifts (`K + off ≥ 0` by construction).
fn real_scale_ord(
    up: bool,
    b_w: &IntExpr,
    b_off: i64,
    v_w: &IntExpr,
    v_off: i64,
    k: u32,
) -> Formula {
    let bl = real_shl(b_w.clone(), (k as i64 + b_off) as u32);
    let vr = real_shl(v_w.clone(), (k as i64 + v_off) as u32);
    let (l, r, op) = if up {
        (bl, vr, IntCmpOp::Lte)
    } else {
        (vr, bl, IntCmpOp::Lte)
    };
    ereal_icmp(op, l, r)
}

/// Successor (`up`) / predecessor core over strictly positive input
/// lanes (`mx`, `ex`): disjunction over static scale offsets of
/// [per-scale optimum pins + pairwise extremality]. `r` is the window
/// radius (offsets `-r..=r`, a superset of the oracle window);
/// `k = r + 1` balances pairwise shifts. `mag_max`/`emin`/`emax` are
/// the lane bounds. Callers conjoin wellformedness and the positivity
/// guard, and link mirrored (negated) lanes for negative inputs.
/// Predecessor gains one global zero disjunct (all mains infeasible).
#[allow(clippy::too_many_arguments)]
fn real_next_core(
    up: bool,
    mx: &IntExpr,
    ex: &IntExpr,
    my: &IntExpr,
    ey: &IntExpr,
    ebits: u32,
    mag_max: i64,
    emin: i64,
    emax: i64,
    r: i64,
) -> Formula {
    let ex_w = real_wide(ex.clone());
    let my_w = real_wide(my.clone());
    let ey_w = real_wide(ey.clone());
    // Collect per-scale mains.
    let mut subs: Vec<RealScaleCand> = Vec::new();
    let mut c = -r;
    loop {
        if up {
            subs.push(real_succ_scale(
                mx, &ex_w, &my_w, &ey_w, c, ebits, mag_max, emin, emax,
            ));
        } else {
            subs.extend(real_pred_scale(
                mx, &ex_w, &my_w, &ey_w, c, ebits, mag_max, emin, emax,
            ));
        }
        if c >= r {
            break;
        }
        c += 1;
    }
    let k = (r + 1) as u32;
    // Pairwise extremality between mains (gated by definedness).
    let mut ordered: Vec<Formula> = Vec::new();
    for (i, s) in subs.iter().enumerate() {
        let mut conj = s.eqs.clone();
        for (j, t) in subs.iter().enumerate() {
            if i == j {
                continue;
            }
            let cmp = real_scale_ord(up, &s.val_m, s.off, &t.val_m, t.off, k);
            match &t.feas {
                None => conj.push(cmp),
                Some(f) => conj.push(Formula::Or(
                    Box::new(Formula::Not(Box::new(f.clone()))),
                    Box::new(cmp),
                )),
            }
        }
        ordered.push(ereal_and_all(conj));
    }
    if !up {
        // Global zero: all mains infeasible (zero is below every
        // positive main value, so no ordering is needed).
        let mut conj = vec![ereal_icmp(
            IntCmpOp::Eq,
            my_w.clone(),
            real_wide(IntExpr::Lit(0, 0)),
        )];
        for t in subs.iter() {
            if let Some(f) = &t.feas {
                conj.push(Formula::Not(Box::new(f.clone())));
            }
        }
        ordered.push(ereal_and_all(conj));
    }
    ereal_or_all(ordered)
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
        Expr::Name(..) | Expr::Univ | Expr::None_ | Expr::Iden | Expr::IntAtom | Expr::StepAtom | Expr::Bits(..) | Expr::RealLit(..) | Expr::ApproxRealLit(..) => {
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
        IntExpr::Widen(op, a, b) => IntExpr::Widen(
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
