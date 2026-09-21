//! alloy-front-rs: native Rust frontend for Alloy (.als) models.
//!
//! Pipeline: lex -> parse -> resolve/lower -> kodkod-rs AstArena + Bounds
//! -> Solver. The long-term goal is to replace the Java bridge entirely;
//! the Java path remains as a differential oracle until parity is proven.
//!
//! First slice (Iter 15): single-module models without `open`; sigs with
//! extends hierarchies, fields with multiplicities, facts (named/anonymous/
//! sig facts), predicates, assertions; run/check commands with scopes
//! (`for N`, `but ...`, bitwidth via `k Int`); expressions covering join,
//! product, set ops (+ & - ++), closures (^ * ~), comprehension, ite,
//! quantifiers (all/some/no/lone/one), cardinality # and int arithmetic.

pub mod cegis;
pub mod cnf;
pub mod incremental;
pub mod partial;
pub mod snippet;
/// Structured model generator + brute-force oracle (fuzzing support).
/// Zero extra dependencies; also used by `tests/fuzz_model.rs`.
pub mod fuzzgen;
mod ast;
mod bounds;
mod lex;
mod lower;
mod parser;
pub mod types;

pub use ast::Scope;
pub use ast::{
    BinOp, CmpKind, Command, CommandKind, Decl, Expr, Formula, IntBinOp, IntCmpOp, IntExpr, Module,
    Open, OpenParam, OptSpec, OverflowMode, PartialDef, PartialEntry, PartialOp, QuantKind, SigDecl,
    SigMult, DEFAULT_INT_BITWIDTH, effective_bitwidth, effective_int_count, module_needs_int_atoms,
};
pub use lower::{LoweredOpt, LoweredProblem, LoweredTarget, Lowerer, OptMarker, TimePoint};
pub use cnf::{build_cnf_with, check, run, solve, solve_temporal, validate, validate_temporal, Cnf, CnfKind};
pub use incremental::{IncrementalSession, MultKind, SessionStats};
pub use partial::{verifier_pin_from_partial, PartialInstance, PartialInt, PartialRel};
pub use cegis::{run_cegis, CegisConfig, CegisOutcome, CegisReport};
pub use snippet::{
    eval, fragment_keys, parse_expr, parse_formula, parse_int_expr, query, query_value, QueryValue,
};
pub use alloy_kodkod_rs::tupleset::TupleSet;
pub use alloy_kodkod_rs::instance::Instance;
pub use alloy_kodkod_rs::opt::{Objective as KkObjective, OptSense as KkOptSense, OptSolution};

use alloy_kodkod_rs::ast::IntId;
use alloy_kodkod_rs::solver::Solution;
use std::time::{Duration, Instant};

#[derive(Debug)]
pub struct TimedResult {
    pub solution: Result<Solution, FrontError>,
    pub parse: Duration,
    pub lower: Duration,
    pub solve: Duration,
}

#[derive(Debug)]
pub enum FrontError {
    Lex { pos: usize, msg: String },
    Parse { pos: usize, msg: String },
    Resolve(String),
    Unsupported(String),
    Solve(alloy_kodkod_rs::fol::TranslateError),
}

impl std::fmt::Display for FrontError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FrontError::Lex { pos, msg } => write!(f, "lex error at byte {pos}: {msg}"),
            FrontError::Parse { pos, msg } => write!(f, "parse error at byte {pos}: {msg}"),
            FrontError::Resolve(msg) => write!(f, "resolution error: {msg}"),
            FrontError::Unsupported(what) => {
                write!(f, "unsupported construct: {what}")
            }
            FrontError::Solve(e) => write!(f, "solve error: {e}"),
        }
    }
}

impl std::error::Error for FrontError {}

/// Parses a module source text.
pub fn parse_module(src: &str) -> Result<Module, FrontError> {
    let tokens = lex::lex(src)?;
    parser::Parser::new(tokens).module()
}

/// True when command `index` must run through the optimizer: a
/// `maximize`/`minimize` command, a `run`/`check` whose facts or body
/// carry AlloyMax soft nodes, or one carrying an in-body
/// `maximize`/`minimize` marker. Runs a cheap prepare to read the flags;
/// lowering errors report false (the real path surfaces them).
pub fn command_needs_opt(module: &Module, index: usize) -> bool {
    let cmd = match module.commands.get(index) {
        Some(c) => c,
        None => return false,
    };
    if matches!(
        cmd.kind,
        CommandKind::Maximize { .. } | CommandKind::Minimize { .. }
    ) {
        return true;
    }
    Lowerer::new(module)
        .prepare_command(index)
        .map(|p| p.has_softs || !p.markers.is_empty())
        // A lowering error reports the flag from a shallow module-wide
        // AST scan, so a broken marker still routes to the optimizer
        // (which surfaces the real error) instead of looking like a
        // plain run/check. The scan does not expand calls, so it is an
        // over-approximation; that is harmless because it only kicks in
        // when the command fails to lower anyway.
        .unwrap_or_else(|_| module_has_opt_marker(module))
}

/// Shallow module-wide `maximize`/`minimize` marker scan (bodies, facts,
/// `soft fact`s, sig facts; no call expansion, no lowering). Only the
/// fallback for [`command_needs_opt`] when lowering fails.
fn module_has_opt_marker(module: &Module) -> bool {
    module.paras.iter().any(|p| p.body.has_opt_marker())
        || module.facts.iter().any(|(_, f)| f.has_opt_marker())
        || module.soft_facts.iter().any(|(_, f)| f.has_opt_marker())
        || module
            .sigs
            .iter()
            .filter_map(|sd| sd.fact.as_ref())
            .any(|f| f.has_opt_marker())
}

/// Runs a `maximize`/`minimize` command end-to-end (translate + optimize).
/// Also serves `run`/`check` commands whose bodies carry AlloyMax soft
/// nodes (`maxsome` / `minsome`), modules with `soft fact`s, or bodies
/// carrying `maximize`/`minimize` markers. Returns the optimal model and
/// its exact cost. Errors on plain `run`/`check` commands (use
/// [`run_command`]).
///
/// Temporal commands optimize over the time-expanded problem. A marker
/// objective is evaluated at the trace state pinned by the enclosing
/// `initially` (first state) / `goal` (last state) / `restore` (loop
/// state) operator, so its variable relations are projected to that
/// state. Command-level objectives (`maximize:`) and soft constraints
/// still reference static relations only (mirror trace state into a
/// static sig, e.g. `fact {goal Aopt = A}`).
/// On SAT the returned solution carries the projected lasso trace in
/// `temporal` (with `instance` holding the flat expanded model).
pub fn run_opt_command(module: &Module, index: usize) -> Result<OptSolution, FrontError> {
    run_opt_command_with(module, index, true)
}

/// [`run_opt_command`] with explicit overflow handling (`false` is pure
/// wrapping). Used by the REPL two-phase optimization (gated optimum
/// first, wrapping fallback). A `some Overflow` marker forces wrapping;
/// `some Overflow` on a temporal command is rejected (no CEGAR there).
pub fn run_opt_command_with(
    module: &Module,
    index: usize,
    no_overflow: bool,
) -> Result<OptSolution, FrontError> {
    if module.is_temporal_command(index) {
        return run_opt_temporal_with(module, index, no_overflow);
    }
    let mut lower = Lowerer::new(module);
    let problem = lower.prepare_command(index)?;
    run_opt_static_with(index, problem, no_overflow)
}

/// Static half of [`run_opt_command_with`].
fn run_opt_static_with(
    index: usize,
    problem: LoweredProblem,
    no_overflow: bool,
) -> Result<OptSolution, FrontError> {
    // Explicit `some`/`no Overflow` markers take precedence over the
    // caller's flag (mirrors `build_cnf`).
    let no_overflow = match problem.overflow {
        Some(OverflowMode::Some) => false,
        Some(OverflowMode::No) => true,
        None => no_overflow,
    };
    let marker_targets: Vec<(IntId, KkOptSense)> = problem
        .markers
        .iter()
        .map(|m| (m.target, m.sense))
        .collect();
    let kk_objective = resolve_objective(index, &problem, &marker_targets)?;

    let mut arena = problem.arena;
    let mut bounds = problem.bounds;
    let mut formula = problem.formula;
    // Mirror the Run skolem treatment: positive existentials become witness
    // relations. Sound for optimization: the objective only references
    // user relations, whose optima are preserved by projection.
    if let Some(sk) =
        alloy_kodkod_rs::skolem::skolemize_static(&mut arena, &mut bounds, formula)
            .map_err(|e| FrontError::Solve(e.into()))?
    {
        formula = sk.formula;
    }
    let solver =
        alloy_kodkod_rs::solver::Solver::with_options(alloy_kodkod_rs::solver::SolverOptions {
            bitwidth: problem.bitwidth,
            skolemize: false, // already applied above
            no_overflow,
            ..Default::default()
        });
    solver
        .solve_opt(&arena, formula, &bounds, kk_objective)
        .map_err(FrontError::Solve)
}

/// Temporal half of [`run_opt_command_with`]: expands the bounds, rewrites the
/// formula, and optimizes over the static expanded problem.
fn run_opt_temporal_with(
    module: &Module,
    index: usize,
    no_overflow: bool,
) -> Result<OptSolution, FrontError> {
    let mut lower = Lowerer::new(module);
    let problem = lower.prepare_command(index)?;
    // `some Overflow` seeks an overflowing trace via a CEGAR loop that
    // only exists for static problems; reject loudly for temporal ones.
    if problem.overflow == Some(OverflowMode::Some) {
        return Err(FrontError::Resolve(
            "`some Overflow` is not supported for temporal commands yet (use a static `run`)".to_string(),
        ));
    }
    if problem.overflow == Some(OverflowMode::No) {
        // Explicit marker pins the mode regardless of the caller's flag.
        return run_opt_temporal_inner(module, index, problem, true);
    }
    run_opt_temporal_inner(module, index, problem, no_overflow)
}

fn run_opt_temporal_inner(
    module: &Module,
    index: usize,
    mut problem: LoweredProblem,
    no_overflow: bool,
) -> Result<OptSolution, FrontError> {
    use alloy_kodkod_rs::temporal::{
        add_witness_relation, collect_witness_specs, expand_bounds, extract_temporal_instance,
        translate_temporal_formula,
    };

    let markers = std::mem::take(&mut problem.markers);

    // Soft objectives are collected implicitly across the whole formula,
    // so per-reference auditing is unreliable: uniformly out of scope.
    if problem.has_softs {
        return Err(FrontError::Unsupported(
            "temporal optimization with soft constraints (maxsome/minsome/soft fact) is not supported; use an explicit maximize:/minimize: over static relations".into(),
        ));
    }
    // Objective for the temporal states.
    //
    // Markers carry the trace state they are evaluated at (pinned by the
    // enclosing `initially`/`goal`/`restore`), so their variable
    // relations are projected to that state below. A command-level
    // objective has no state annotation: keep the static-only rule.
    let static_objective = if markers.is_empty() {
        reject_var_objective(&problem)?;
        Some(resolve_objective(index, &problem, &[])?)
    } else {
        for m in &markers {
            if m.time.is_none() {
                let kw = if m.sense == KkOptSense::Maximize {
                    "maximize"
                } else {
                    "minimize"
                };
                return Err(FrontError::Unsupported(format!(
                    "`{kw}` in a temporal command needs a trace state; wrap the target in \
                     `initially` (first state), `goal` (last state) or `restore` (loop state), \
                     e.g. `goal ({kw} X)`"
                )));
            }
        }
        None
    };

    let steps = module.temporal_steps(index);
    let mut arena = problem.arena;
    let bounds = problem.bounds;
    let orig_formula = problem.formula;

    // Mirror the static path's unconditional skolemization with HASLab
    // temporal witnesses.
    let mut specs = Vec::new();
    collect_witness_specs(&mut arena, &bounds, orig_formula, true, true, false, &mut specs, &mut 0);
    let mut expansion =
        expand_bounds(&arena, &bounds, steps, 1).map_err(|e| FrontError::Solve(e.into()))?;
    let mut witnesses = std::collections::HashMap::new();
    let mut witness_domains = Vec::new();
    for sp in &specs {
        let upper = alloy_kodkod_rs::skolem::upper_bound_expr(&arena, sp.domain, &bounds)
            .ok_or(alloy_kodkod_rs::fol::TranslateError::BadDomain)
            .map_err(FrontError::Solve)?;
        let rel = add_witness_relation(&mut expansion, &mut arena, &sp.name, sp.value_arity, &upper)
            .map_err(|e| FrontError::Solve(e.into()))?;
        witnesses.insert(sp.var, rel);
        witness_domains.push((rel, sp.domain));
    }
    let formula = translate_temporal_formula(
        &mut arena,
        orig_formula,
        &expansion,
        &witnesses,
        &witness_domains,
    )
    .map_err(|e| FrontError::Solve(e.into()))?;
    let bounds = expansion.bounds.clone();

    // Marker objectives: rewrite every variable relation to its value at
    // the marker's trace state (`r$t . $t_first|$t_last|$t_loop`), which
    // leaves the existing static objective path untouched.
    let kk_objective = match static_objective {
        Some(objective) => objective,
        None => {
            let targets = rewrite_marker_targets(&mut arena, &expansion, &markers)?;
            marker_objective(&targets)
        }
    };

    let solver =
        alloy_kodkod_rs::solver::Solver::with_options(alloy_kodkod_rs::solver::SolverOptions {
            bitwidth: problem.bitwidth,
            skolemize: false, // witnesses already applied above
            no_overflow,
            ..Default::default()
        });
    let mut sol = solver
        .solve_opt(&arena, formula, &bounds, kk_objective)
        .map_err(FrontError::Solve)?;
    if sol.satisfiable {
        if let Some(inst) = sol.instance.as_ref() {
            sol.temporal =
                Some(extract_temporal_instance(inst, &expansion).map_err(|e| FrontError::Solve(e.into()))?);
        }
    }
    Ok(sol)
}

/// Objective of a command: the `maximize:`/`minimize:` command form,
/// else the in-body markers, else translation-collected softs.
fn resolve_objective(
    index: usize,
    problem: &LoweredProblem,
    markers: &[(IntId, KkOptSense)],
) -> Result<KkObjective, FrontError> {
    if let Some(objective) = &problem.objective {
        return Ok(match (&objective.sense, &objective.target) {
            (KkOptSense::Maximize, LoweredTarget::Int(id)) => KkObjective::max_int(*id),
            (KkOptSense::Minimize, LoweredTarget::Int(id)) => KkObjective::min_int(*id),
            (KkOptSense::Maximize, LoweredTarget::Weighted(w)) => {
                KkObjective::max_weighted(w.clone())
            }
            (KkOptSense::Minimize, LoweredTarget::Weighted(w)) => {
                KkObjective::min_weighted(w.clone())
            }
        });
    }
    if !markers.is_empty() {
        return Ok(marker_objective(markers));
    }
    if problem.has_softs {
        return Ok(KkObjective::collected());
    }
    Err(FrontError::Resolve(format!(
        "command #{index} is not maximize/minimize and carries no soft constraints (use run_command)"
    )))
}

/// Objective pooled from in-body `maximize`/`minimize` markers. A single
/// target keeps the exact single-objective path; several pool their
/// bit-weight soft units with each marker's own sense.
///
/// Weights are the targets' own (bit weights for an `Int` target), so
/// relative influence is expressed in the target expressions themselves
/// (e.g. `maximize (2*#A + #B)`) rather than by a separate weight syntax.
fn marker_objective(markers: &[(IntId, KkOptSense)]) -> KkObjective {
    if let [(id, sense)] = markers {
        return match sense {
            KkOptSense::Maximize => KkObjective::max_int(*id),
            KkOptSense::Minimize => KkObjective::min_int(*id),
        };
    }
    KkObjective::ints(markers.to_vec())
}

/// Relation ids referenced by one integer target (reuses the objective
/// walker for the temporal marker projection).
fn collect_target_relations(
    arena: &alloy_kodkod_rs::AstArena,
    target: IntId,
    out: &mut std::collections::HashSet<alloy_kodkod_rs::RelationId>,
) {
    let tmp = Some(LoweredOpt {
        sense: KkOptSense::Maximize,
        target: LoweredTarget::Int(target),
    });
    collect_opt_relations(arena, &tmp, out);
}

/// Rejects a temporal command-level objective (`maximize:`) that
/// references variable relations: unlike markers, it has no trace state
/// annotation, so the original relation id is unbound after expansion.
fn reject_var_objective(problem: &LoweredProblem) -> Result<(), FrontError> {
    let mut refs = std::collections::HashSet::new();
    collect_opt_relations(&problem.arena, &problem.objective, &mut refs);
    let mut vars: Vec<String> = refs
        .into_iter()
        .filter(|r| problem.arena.is_variable(*r))
        .map(|r| problem.bounds.pool().name(r).to_string())
        .collect();
    vars.sort();
    if vars.is_empty() {
        return Ok(());
    }
    Err(FrontError::Unsupported(format!(
        "temporal objective references variable relation(s) {}; optimize over static relations \
         only (mirror var state via goal/initially into a static sig, e.g. fact {{goal Aopt = A}}), \
         or write the target as an in-body marker (`goal (maximize X)`)",
        vars.join(", ")
    )))
}

/// Rewrites every variable relation of each marker target to its value at
/// the marker's trace state: `r` becomes `r$t . $t_first|$t_last|$t_loop`
/// (the same projection the temporal translator uses for `T::At(t)`).
/// Static relations are left untouched, so the result can go through the
/// existing static objective path.
fn rewrite_marker_targets(
    arena: &mut alloy_kodkod_rs::AstArena,
    expansion: &alloy_kodkod_rs::temporal::TemporalExpansion,
    markers: &[OptMarker],
) -> Result<Vec<(IntId, KkOptSense)>, FrontError> {
    use alloy_kodkod_rs::ast::BinaryOp;
    let mut out = Vec::with_capacity(markers.len());
    let mut cache: std::collections::HashMap<
        (u32, TimePoint),
        std::collections::HashMap<alloy_kodkod_rs::RelationId, alloy_kodkod_rs::ast::ExprId>,
    > = std::collections::HashMap::new();
    for m in markers {
        // Checked by the caller: a temporal command needs a trace state.
        let tp = m.time.ok_or_else(|| {
            FrontError::Unsupported(
                "`maximize`/`minimize` in a temporal command needs a trace state \
                 (`initially` / `goal` / `restore`)"
                    .into(),
            )
        })?;
        let map = match cache.get(&(m.target.0, tp)) {
            Some(m) => m.clone(),
            None => {
                let state = match tp {
                    TimePoint::First => expansion.ids.first,
                    TimePoint::Last => expansion.ids.last,
                    TimePoint::Loop => expansion.ids.loop_,
                };
                let mut refs = std::collections::HashSet::new();
                collect_target_relations(arena, m.target, &mut refs);
                let mut map = std::collections::HashMap::new();
                for r in refs {
                    if !arena.is_variable(r) {
                        continue;
                    }
                    let exp = expansion.mapping.get(&r).copied().ok_or_else(|| {
                        FrontError::Unsupported(format!(
                            "internal: variable relation `{}` has no temporal expansion",
                            arena.relation_name(r)
                        ))
                    })?;
                    let left = arena.expr_relation(exp);
                    let right = arena.expr_relation(state);
                    let joined = arena
                        .binary_expr(BinaryOp::Join, left, right)
                        .map_err(|e| FrontError::Resolve(e.to_string()))?;
                    map.insert(r, joined);
                }
                cache.insert((m.target.0, tp), map.clone());
                map
            }
        };
        let target = alloy_kodkod_rs::ast::subst_relation_int(arena, m.target, &map);
        out.push((target, m.sense));
    }
    Ok(out)
}

/// Collects every relation id referenced by an optimization target
/// (transitively through int/expr/formula/decl nodes) for the temporal
/// static-only check.
fn collect_opt_relations(
    arena: &alloy_kodkod_rs::AstArena,
    objective: &Option<LoweredOpt>,
    out: &mut std::collections::HashSet<alloy_kodkod_rs::RelationId>,
) {
    use alloy_kodkod_rs::ast::{ExprNode, FormulaNode, IntNode};
    fn int(
        arena: &alloy_kodkod_rs::AstArena,
        i: alloy_kodkod_rs::ast::IntId,
        out: &mut std::collections::HashSet<alloy_kodkod_rs::RelationId>,
    ) {
        match arena.int(i).clone() {
            IntNode::Constant(_) => {}
            IntNode::OfExpr { expr, .. } => expr_rec(arena, expr, out),
            IntNode::Binary { left, right, .. } => {
                int(arena, left, out);
                int(arena, right, out);
            }
            IntNode::If { cond, then, els } => {
                formula(arena, cond, out);
                int(arena, then, out);
                int(arena, els, out);
            }
            IntNode::Sum { decls, body } => {
                decls_rec(arena, decls, out);
                int(arena, body, out);
            }
        }
    }
    fn expr_rec(
        arena: &alloy_kodkod_rs::AstArena,
        e: alloy_kodkod_rs::ast::ExprId,
        out: &mut std::collections::HashSet<alloy_kodkod_rs::RelationId>,
    ) {
        match arena.expr(e).clone() {
            ExprNode::Relation(r) => {
                out.insert(r);
            }
            ExprNode::Variable(_) | ExprNode::Constant(_) | ExprNode::Atoms(_) => {}
            ExprNode::Unary { child, .. } | ExprNode::Temporal { child, .. } => {
                expr_rec(arena, child, out)
            }
            ExprNode::Binary { left, right, .. } => {
                expr_rec(arena, left, out);
                expr_rec(arena, right, out);
            }
            ExprNode::Nary { children, .. } => {
                for c in children {
                    expr_rec(arena, c, out);
                }
            }
            ExprNode::If { cond, then, els } => {
                formula(arena, cond, out);
                expr_rec(arena, then, out);
                expr_rec(arena, els, out);
            }
            ExprNode::Project { expr, columns } => {
                expr_rec(arena, expr, out);
                for c in columns {
                    int(arena, c, out);
                }
            }
            ExprNode::Comprehension { decls, body } => {
                decls_rec(arena, decls, out);
                formula(arena, body, out);
            }
            ExprNode::FromInt(i) => int(arena, i, out),
        }
    }
    fn formula(
        arena: &alloy_kodkod_rs::AstArena,
        f: alloy_kodkod_rs::ast::FormulaId,
        out: &mut std::collections::HashSet<alloy_kodkod_rs::RelationId>,
    ) {
        match arena.formula(f).clone() {
            FormulaNode::Constant(_) => {}
            FormulaNode::Not(c) => formula(arena, c, out),
            FormulaNode::Nary { children, .. } => {
                for c in children {
                    formula(arena, c, out);
                }
            }
            FormulaNode::Comparison { left, right, .. } => {
                expr_rec(arena, left, out);
                expr_rec(arena, right, out);
            }
            FormulaNode::IntComparison { left, right, .. } => {
                int(arena, left, out);
                int(arena, right, out);
            }
            FormulaNode::Multiplicity { expr, .. } => expr_rec(arena, expr, out),
            FormulaNode::Quantified { decls, body, .. } => {
                decls_rec(arena, decls, out);
                formula(arena, body, out);
            }
            FormulaNode::TemporalUnary { child, .. } => formula(arena, child, out),
            FormulaNode::TemporalBinary { left, right, .. } => {
                formula(arena, left, out);
                formula(arena, right, out);
            }
            FormulaNode::MaxSome(e) | FormulaNode::MinSome(e) => expr_rec(arena, e, out),
            FormulaNode::SoftFact(c) => formula(arena, c, out),
        }
    }
    fn decls_rec(
        arena: &alloy_kodkod_rs::AstArena,
        d: alloy_kodkod_rs::ast::DeclsId,
        out: &mut std::collections::HashSet<alloy_kodkod_rs::RelationId>,
    ) {
        for decl in arena.decls(d) {
            expr_rec(arena, decl.expr, out);
        }
    }
    let Some(opt) = objective else { return };
    match &opt.target {
        LoweredTarget::Int(id) => int(arena, *id, out),
        LoweredTarget::Weighted(w) => {
            out.extend(w.keys().copied());
        }
    }
}

/// Target of a REPL `:max`/`:min`/`:maxw`/`:minw` request.
#[derive(Debug, Clone)]
pub enum OptTarget {
    /// Maximize/minimize a parsed integer expression.
    Int(crate::ast::IntExpr, KkOptSense),
    /// Maximize/minimize Σ w·#rel over named relations.
    Weights(Vec<(String, i64)>, KkOptSense),
}

/// Optimizes over an already-built [`Cnf`] (REPL `:max`/`:min`/`:maxw`/`:minw`).
///
/// The integer expression is lowered into a clone of the Cnf's arena
/// (relation IDs line up: same pool); weight names resolve against the
/// Cnf bounds' pool. The stored (possibly skolemized) formula is used
/// as-is, so no extra skolem step is needed here.
pub fn optimize(module: &Module, cnf: &Cnf, target: &OptTarget) -> Result<OptSolution, FrontError> {
    optimize_with(module, cnf, target, true)
}

/// [`optimize`] with explicit overflow handling (`false` is pure
/// wrapping). A `some Overflow` Cnf is already built wrapping; callers
/// pass `false` for it (the OLL loop itself has no CEGAR, so the
/// optimum is a wrapping optimum with an evaluator note, not a
/// guaranteed-overflowing one).
pub fn optimize_with(
    module: &Module,
    cnf: &Cnf,
    target: &OptTarget,
    no_overflow: bool,
) -> Result<OptSolution, FrontError> {
    if cnf.is_temporal {
        return Err(FrontError::Unsupported(
            "temporal Cnfs cannot be optimized (objectives over traces are undefined)".into(),
        ));
    }
    let scope = module
        .commands
        .get(cnf.command_index)
        .map(|c| c.scope.clone())
        .ok_or_else(|| {
            FrontError::Resolve(format!("command #{} is gone", cnf.command_index))
        })?;
    let mut lower = Lowerer::new(module);
    // Lower the Int target into a clone of the Cnf arena (same pool, so
    // relation IDs line up with the stored formula and bounds).
    let mut arena = cnf.arena.clone();
    let kk_objective = match target {
        OptTarget::Int(ie, sense) => {
            let id = lower.lower_int_in_scope(&scope, &mut arena, ie)?;
            match sense {
                KkOptSense::Maximize => KkObjective::max_int(id),
                KkOptSense::Minimize => KkObjective::min_int(id),
            }
        }
        OptTarget::Weights(pairs, sense) => {
            // Resolve against the Cnf bounds' pool (no scope needed).
            let mut name_to_id = std::collections::HashMap::new();
            for r in cnf.bounds.relations() {
                name_to_id.insert(cnf.bounds.pool().name(r).to_string(), r);
            }
            let mut weights = std::collections::HashMap::new();
            for (name, w) in pairs {
                // Bare field names resolve like the lowerer (unique suffix).
                let r = name_to_id.get(name).copied().or_else(|| {
                    let mut hits = name_to_id.iter().filter(|(k, _)| {
                        k.ends_with(&format!(".{name}"))
                    });
                    let first = hits.next().map(|(_, &v)| v);
                    if first.is_some() && hits.next().is_none() {
                        first
                    } else {
                        None
                    }
                });
                match r {
                    Some(r) => {
                        weights.insert(r, *w);
                    }
                    None => {
                        return Err(FrontError::Resolve(format!(
                            "unknown relation '{name}' in weights"
                        )))
                    }
                }
            }
            match sense {
                KkOptSense::Maximize => KkObjective::max_weighted(weights),
                KkOptSense::Minimize => KkObjective::min_weighted(weights),
            }
        }
    };
    // NOTE: `lower_int_in_scope` interns into a *cloned* arena; the IntId
    // above refers to that clone's numbering. Kodkod arenas intern
    // deterministically from the Cnf arena state, so ids coincide with a
    // fresh clone — which is exactly the `arena` used for the solve below.
    let solver =
        alloy_kodkod_rs::solver::Solver::with_options(alloy_kodkod_rs::solver::SolverOptions {
            bitwidth: cnf.bitwidth,
            no_overflow,
            ..Default::default()
        });
    solver
        .solve_opt(&arena, cnf.formula, &cnf.bounds, kk_objective)
        .map_err(FrontError::Solve)
}

/// Runs one command of a parsed module end-to-end (translate + solve).
pub fn run_command(module: &Module, index: usize) -> Result<Solution, FrontError> {
    let cmd = module
        .commands
        .get(index)
        .ok_or_else(|| FrontError::Resolve(format!("no command #{index}")))?;
    let mut lower = Lowerer::new(module);
    let problem = lower.prepare_command(index)?;

    // AlloyMax softs need the optimizer (plain SAT would silently drop
    // them, and the temporal path cannot see them at all). Same for an
    // in-body `maximize`/`minimize` marker, whose hard meaning is true.
    if problem.has_softs {
        return Err(FrontError::Resolve(format!(
            "command #{index} carries soft constraints (maxsome/minsome/soft fact); use run_opt_command"
        )));
    }
    if !problem.markers.is_empty() {
        return Err(FrontError::Resolve(format!(
            "command #{index} carries an optimization target (`maximize`/`minimize` in its body); use run_opt_command"
        )));
    }
    // `some Overflow` needs the CEGAR search on the `Cnf` path; solving
    // the bare body here would silently degrade to a prohibited search.
    if problem.overflow == Some(OverflowMode::Some) {
        return Err(FrontError::Resolve(format!(
            "command #{index} uses `some Overflow`; solve it via `:solve` on a `:run`-built Cnf instead of `als`"
        )));
    }

    let is_temporal = module.is_temporal_command(index);

    let solver =
        alloy_kodkod_rs::solver::Solver::with_options(alloy_kodkod_rs::solver::SolverOptions {
            bitwidth: problem.bitwidth,
            skolemize: matches!(cmd.kind, CommandKind::Run(_)),
            ..Default::default()
        });
    let mut arena = problem.arena;

    if is_temporal {
        let steps = module.temporal_steps(index);
        solver
            .solve_temporal(&mut arena, problem.formula, &problem.bounds, steps)
            .map_err(FrontError::Solve)
    } else {
        solver
            .solve(&mut arena, problem.formula, &problem.bounds)
            .map_err(FrontError::Solve)
    }
}

/// Parses source text, then runs one command with per-phase timing.
pub fn parse_and_run_timed(src: &str, index: usize) -> TimedResult {
    let t0 = Instant::now();
    let module = match parse_module(src) {
        Ok(m) => m,
        Err(e) => {
            return TimedResult {
                solution: Err(e),
                parse: t0.elapsed(),
                lower: Duration::ZERO,
                solve: Duration::ZERO,
            };
        }
    };
    let t1 = Instant::now();
    let cmd = match module.commands.get(index) {
        Some(c) => c,
        None => {
            return TimedResult {
                solution: Err(FrontError::Resolve(format!("no command #{index}"))),
                parse: t1 - t0,
                lower: Duration::ZERO,
                solve: Duration::ZERO,
            };
        }
    };
    let mut lower = Lowerer::new(&module);
    let problem = match lower.prepare_command(index) {
        Ok(p) => p,
        Err(e) => {
            let t2 = Instant::now();
            return TimedResult {
                solution: Err(e),
                parse: t1 - t0,
                lower: t2 - t1,
                solve: Duration::ZERO,
            };
        }
    };
    let t2 = Instant::now();
    let is_temporal = module.is_temporal_command(index);
    let solver =
        alloy_kodkod_rs::solver::Solver::with_options(alloy_kodkod_rs::solver::SolverOptions {
            bitwidth: problem.bitwidth,
            skolemize: matches!(cmd.kind, CommandKind::Run(_)),
            ..Default::default()
        });
    let mut arena = problem.arena;
    let solve_result = if is_temporal {
        let steps = module.temporal_steps(index);
        solver.solve_temporal(&mut arena, problem.formula, &problem.bounds, steps)
    } else {
        solver.solve(&mut arena, problem.formula, &problem.bounds)
    };
    let t3 = Instant::now();
    TimedResult {
        solution: solve_result.map_err(FrontError::Solve),
        parse: t1 - t0,
        lower: t2 - t1,
        solve: t3 - t2,
    }
}
