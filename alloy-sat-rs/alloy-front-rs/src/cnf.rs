//! REPL-oriented split API: `run` / `check` build a `Cnf` value,
//! `solve` inspects it and returns an `Instance` (or nothing).
//!
//! - `run`  : satisfiability search. `solve` SAT => example instance.
//! - `check`: negated assertion search (lowering already negates).
//!   `solve` SAT => counterexample instance,
//!   `solve` UNSAT => `None` (assertion holds, empty).
//! - `validate(cnf, instance)`: builtin check. Returns the instance
//!   as-is (`Some`) iff it is a model of the `Cnf`,
//!   otherwise `None` (empty).
//!
//! `Cnf` keeps both levels (as requested):
//! high-level (`AstArena` + `Bounds` + `FormulaId`) for inspection,
//! low-level (`num_vars` + `clauses`) for direct SAT solving,
//! plus `origins` needed to materialize an `Instance` from a SAT assignment.

use std::collections::HashMap;

use alloy_kodkod_rs::ast::FormulaId;
use alloy_kodkod_rs::bounds::Bounds;
use alloy_kodkod_rs::fol::{TranslateError, VarOrigin};
use alloy_kodkod_rs::instance::Instance;
use alloy_kodkod_rs::temporal::{TemporalExpansion, TemporalInstance};
use alloy_kodkod_rs::{AstArena, BoolCtx};

use crate::ast::{CommandKind, Module, OverflowMode};
use crate::lower::Lowerer;
use crate::FrontError;

/// Whether this `Cnf` came from `run` (example search) or
/// `check` (counterexample search; formula already negated).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CnfKind {
    Run,
    Check,
}

impl std::fmt::Display for CnfKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CnfKind::Run => write!(f, "run"),
            CnfKind::Check => write!(f, "check"),
        }
    }
}

/// A built (lowered + translated) problem, ready for `solve`.
///
/// Holds the high-level problem (`arena`/`bounds`/`formula`) and the
/// low-level CNF (`num_vars`/`clauses`), plus `origins` for model
/// reconstruction.
#[derive(Debug, Clone)]
pub struct Cnf {
    pub kind: CnfKind,
    pub command_index: usize,
    pub command_name: Option<String>,
    pub arena: AstArena,
    pub bounds: Bounds,
    pub formula: FormulaId,
    pub bitwidth: u32,
    pub skolemize: bool,
    pub num_vars: usize,
    pub clauses: Vec<Vec<i64>>,
    pub origins: Vec<VarOrigin>,
    /// Compiler-style build warnings (e.g. unconstrained relations).
    /// Populated from preprocessing, before translation.
    pub warnings: Vec<String>,
    /// `some`/`no Overflow` marker from the command body (`None` when
    /// absent). `Some` forces a wrapping build whose `solve` runs a
    /// CEGAR loop for an overflowing model; `No` forces the gated build.
    pub overflow: Option<OverflowMode>,
    /// True when built from a temporal command (bounds/formula are the
    /// time-expanded ones; `solve` returns the first state, use
    /// `solve_temporal` for the full lasso trace).
    pub is_temporal: bool,
    /// Trace length for temporal Cnfs (`temporal_steps`), 0 when static.
    pub steps: usize,
    /// Pre-expansion formula for temporal Cnfs (for `TemporalEval`-based
    /// validation over a `TemporalInstance`).
    pub orig_formula: Option<FormulaId>,
    /// Expansion metadata needed to project a flat SAT model back into a
    /// `TemporalInstance` (`None` when static).
    pub temporal: Option<TemporalExpansion>,
}

impl Cnf {
    pub fn is_run(&self) -> bool {
        self.kind == CnfKind::Run
    }

    pub fn is_check(&self) -> bool {
        self.kind == CnfKind::Check
    }

    pub fn num_clauses(&self) -> usize {
        self.clauses.len()
    }

    /// One-line summary for REPL display.
    pub fn summary(&self) -> String {
        if self.is_temporal {
            format!(
                "{} #{} {} vars={} clauses={} temporal steps={}",
                self.kind,
                self.command_index,
                self.command_name.as_deref().unwrap_or("(anon)"),
                self.num_vars,
                self.clauses.len(),
                self.steps,
            )
        } else {
            format!(
                "{} #{} {} vars={} clauses={}",
                self.kind,
                self.command_index,
                self.command_name.as_deref().unwrap_or("(anon)"),
                self.num_vars,
                self.clauses.len()
            )
        }
    }
}

/// A `maximize`/`minimize` marker is hard `true`: solving the hard part
/// as a plain Cnf would silently ignore the objective.
fn reject_opt_markers(index: usize, problem: &crate::lower::LoweredProblem) -> Result<(), FrontError> {
    if problem.markers.is_empty() {
        return Ok(());
    }
    Err(FrontError::Resolve(format!(
        "command #{index} carries an optimization target (`maximize`/`minimize` in its body); \
         use run_opt_command or :optimize"
    )))
}

fn command_name_of(module: &Module, index: usize) -> Option<String> {
    module.commands.get(index).and_then(|c| match &c.kind {
        CommandKind::Run(n) | CommandKind::Check(n) => n.clone(),
        CommandKind::Maximize { name: n, .. } | CommandKind::Minimize { name: n, .. } => n.clone(),
    })
}

/// Relations that are bounded but never referenced by the formula.
///
/// Detected purely in preprocessing (`arena` + `bounds` + `formula`,
/// before translation): a relation with `upper != lower` that no
/// expression in the formula mentions is free — any subset is a model.
/// Returns `(relation name, free tuple count)` sorted by name.
///
/// Unlike an origins-based check this does not depend on lazy leaf
/// creation, so it stays valid if translation ever materializes every
/// relation up front (Kodkod parity).
pub fn unconstrained_relations(
    arena: &AstArena,
    bounds: &Bounds,
    formula: FormulaId,
) -> Vec<(String, usize)> {
    use alloy_kodkod_rs::ast::{DeclsId, ExprId, ExprNode, FormulaId as Fid, FormulaNode, IntId, IntNode};
    use alloy_kodkod_rs::relation::RelationId;
    use std::collections::HashSet;

    struct Walk<'a> {
        arena: &'a AstArena,
        used: HashSet<u32>,
        seen_e: HashSet<u32>,
        seen_f: HashSet<u32>,
        seen_i: HashSet<u32>,
        seen_d: HashSet<u32>,
    }

    impl<'a> Walk<'a> {
        fn expr(&mut self, id: ExprId) {
            if !self.seen_e.insert(id.0) {
                return;
            }
            match self.arena.expr(id) {
                ExprNode::Relation(r) => {
                    self.used.insert(r.0);
                }
                ExprNode::Variable(_) | ExprNode::Constant(_) | ExprNode::Atoms(_) => {}
                ExprNode::Unary { child, .. } | ExprNode::Temporal { child, .. } => self.expr(*child),
                ExprNode::Binary { left, right, .. } => {
                    self.expr(*left);
                    self.expr(*right);
                }
                ExprNode::Nary { children, .. } => {
                    for c in children.clone() {
                        self.expr(c);
                    }
                }
                ExprNode::If { cond, then, els } => {
                    let (c, t, e) = (*cond, *then, *els);
                    self.formula(c);
                    self.expr(t);
                    self.expr(e);
                }
                ExprNode::Project { expr, columns } => {
                    let (e, cols) = (*expr, columns.clone());
                    self.expr(e);
                    for c in cols {
                        self.int(c);
                    }
                }
                ExprNode::Comprehension { decls, body } => {
                    let (d, b) = (*decls, *body);
                    self.decls(d);
                    self.formula(b);
                }
                ExprNode::FromInt(i) => self.int(*i),
            }
        }

        fn int(&mut self, id: IntId) {
            if !self.seen_i.insert(id.0) {
                return;
            }
            match self.arena.int(id).clone() {
                IntNode::Constant(_) => {}
                IntNode::OfExpr { expr, .. } => self.expr(expr),
                IntNode::Binary { left, right, .. } => {
                    self.int(left);
                    self.int(right);
                }
                IntNode::If { cond, then, els } => {
                    self.formula(cond);
                    self.int(then);
                    self.int(els);
                }
                IntNode::Sum { decls, body } => {
                    self.decls(decls);
                    self.int(body);
                }
            }
        }

        fn decls(&mut self, id: DeclsId) {
            if !self.seen_d.insert(id.0) {
                return;
            }
            for d in self.arena.decls(id).to_vec() {
                self.expr(d.expr);
            }
        }

        fn formula(&mut self, id: Fid) {
            if !self.seen_f.insert(id.0) {
                return;
            }
            match self.arena.formula(id).clone() {
                FormulaNode::Constant(_) => {}
                FormulaNode::Not(c) => self.formula(c),
                FormulaNode::Nary { children, .. } => {
                    for c in children.clone() {
                        self.formula(c);
                    }
                }
                FormulaNode::Comparison { left, right, .. } => {
                    self.expr(left);
                    self.expr(right);
                }
                FormulaNode::IntComparison { left, right, .. } => {
                    self.int(left);
                    self.int(right);
                }
                FormulaNode::Quantified { decls, body, .. } => {
                    self.decls(decls);
                    self.formula(body);
                }
                FormulaNode::MaxSome(e) | FormulaNode::MinSome(e) => self.expr(e),
                FormulaNode::SoftFact(inner) => self.formula(inner),
                FormulaNode::Multiplicity { expr, .. } => self.expr(expr),
                FormulaNode::TemporalUnary { child, .. } => self.formula(child),
                FormulaNode::TemporalBinary { left, right, .. } => {
                    self.formula(left);
                    self.formula(right);
                }
            }
        }
    }

    let mut w = Walk {
        arena,
        used: HashSet::new(),
        seen_e: HashSet::new(),
        seen_f: HashSet::new(),
        seen_i: HashSet::new(),
        seen_d: HashSet::new(),
    };
    w.formula(formula);

    let mut out: Vec<(String, usize)> = Vec::new();
    for r in bounds.relations() {
        if w.used.contains(&r.0) {
            continue;
        }
        let upper_len = bounds.upper_bound(r).map(|t| t.len()).unwrap_or(0);
        let lower_len = bounds.lower_bound(r).map(|t| t.len()).unwrap_or(0);
        let free = upper_len.saturating_sub(lower_len);
        if free == 0 {
            continue;
        }
        let rel_id = RelationId(r.0);
        out.push((bounds.pool().name(rel_id).to_string(), free));
    }
    out.sort();
    out
}

/// Compiler-style warning text for one unconstrained relation:
/// `warning: 'A' is unconstrained: 5 free tuples -> 32 models`.
pub fn unconstrained_warning(name: &str, free_tuples: usize) -> String {
    let models = if free_tuples >= 64 {
        format!("2^{free_tuples}")
    } else {
        format!("{}", 1u128 << free_tuples)
    };
    format!("warning: '{name}' is unconstrained: {free_tuples} free tuples -> {models} models")
}

/// Shared builder: lower, optionally skolemize (Run only), then
/// FOL -> bool circuit -> CNF, capturing origins for later materialize.
fn build_cnf(
    module: &Module,
    index: usize,
    kind: CnfKind,
    no_overflow: bool,
) -> Result<Cnf, FrontError> {
    let cmd = module
        .commands
        .get(index)
        .ok_or_else(|| FrontError::Resolve(format!("no command #{index}")))?;

    // Enforce kind match so `run` never silently builds a `check` and vice versa.
    // Maximize/minimize commands are not buildable as plain Cnfs (they
    // carry an objective; use run_opt_command / optimize instead).
    match (&cmd.kind, kind) {
        (CommandKind::Run(_), CnfKind::Run) | (CommandKind::Check(_), CnfKind::Check) => {}
        (CommandKind::Run(_), CnfKind::Check) => {
            return Err(FrontError::Resolve(format!(
                "command #{index} is `run`, use `run` not `check`"
            )));
        }
        (CommandKind::Check(_), CnfKind::Run) => {
            return Err(FrontError::Resolve(format!(
                "command #{index} is `check`, use `check` not `run`"
            )));
        }
        (CommandKind::Maximize { .. } | CommandKind::Minimize { .. }, _) => {
            return Err(FrontError::Resolve(format!(
                "command #{index} is maximize/minimize, use `:max`/`:min` or run_opt_command"
            )));
        }
    }

    if module.is_temporal_command(index) {
        // Temporal commands build a time-expanded Cnf (same pipeline as
        // `Solver::solve_temporal_with` up to the CNF). `check` searches
        // for a counterexample trace (lowering already negates); witnesses
        // apply to `run` only, mirroring `run_command`.
        return build_temporal_cnf(module, index, kind, no_overflow);
    }

    let mut lower = Lowerer::new(module);
    let problem = lower.prepare_command(index)?;
    // AlloyMax softs need the optimizer loop, not a static Cnf: refuse
    // loudly rather than solving the hard part only.
    if problem.has_softs {
        return Err(FrontError::Resolve(format!(
            "command #{index} carries soft constraints (maxsome/minsome/soft fact); use run_opt_command or :max"
        )));
    }
    reject_opt_markers(index, &problem)?;
    let mut arena = problem.arena;
    let mut bounds = problem.bounds;
    let mut formula = problem.formula;
    let skolemize = kind == CnfKind::Run;
    // Explicit `some`/`no Overflow` markers take precedence over the
    // caller's flag: `some` needs the wrapping build (CEGAR at solve),
    // `no` needs the gated build.
    let overflow = problem.overflow;
    let no_overflow = match overflow {
        Some(OverflowMode::Some) => false,
        Some(OverflowMode::No) => true,
        None => no_overflow,
    };

    // Compiler-style warnings from preprocessing (pre-skolem, so generated
    // witness relations are naturally excluded).
    let warnings: Vec<String> = unconstrained_relations(&arena, &bounds, formula)
        .iter()
        .map(|(n, f)| unconstrained_warning(n, *f))
        .collect();

    // Mirror Solver::solve skolem handling: positive existentials become
    // witness relations on a cloned bounds set (Run only).
    if skolemize {
        if let Some(sk) = alloy_kodkod_rs::skolem::skolemize_static(&mut arena, &mut bounds, formula)
            .map_err(|e| FrontError::Solve(e.into()))?
        {
            formula = sk.formula;
        }
    }

    let ctx = BoolCtx::new();
    // FolTranslator borrows bounds; collect owned data then drop it.
    let (root, origins) = {
        let mut translator = alloy_kodkod_rs::fol::FolTranslator::with_options(
            ctx.clone(),
            &bounds,
            problem.bitwidth,
            no_overflow,
        );
        let root = translator
            .formula_ref(&arena, formula, &[])
            .map_err(FrontError::Solve)?;
        let origins = translator.var_origins().to_vec();
        (root, origins)
    };
    let max_primary = ctx.num_slots();
    let cnf = ctx.with_factory(|factory| {
        alloy_kodkod_rs::cnf::translate_to_cnf(factory, root, max_primary)
    })
    .map_err(|e| FrontError::Solve(e.into()))?;

    Ok(Cnf {
        kind,
        command_index: index,
        command_name: command_name_of(module, index),
        arena,
        bounds,
        formula,
        bitwidth: problem.bitwidth,
        skolemize,
        num_vars: cnf.num_vars,
        clauses: cnf.clauses,
        origins,
        warnings,
        overflow,
        is_temporal: false,
        steps: 0,
        orig_formula: None,
        temporal: None,
    })
}

/// Build a `Cnf` from a temporal `run`/`check` command.
///
/// Mirrors `Solver::solve_temporal_with` up to the CNF: HASLab witness
/// collection (`run` only), `expand_bounds(steps, unrolls=1)`,
/// `translate_temporal_formula`, then the same FOL -> bool circuit -> CNF
/// translation over the expanded bounds. The stored `bounds`/`formula` are
/// the expanded ones; `orig_formula` keeps the pre-expansion id for
/// `TemporalEval`-based validation. For `check` the formula is already the
/// negated assertion search, so SAT yields a counterexample trace.
fn build_temporal_cnf(
    module: &Module,
    index: usize,
    kind: CnfKind,
    no_overflow: bool,
) -> Result<Cnf, FrontError> {
    use alloy_kodkod_rs::temporal::{
        add_witness_relation, collect_witness_specs, expand_bounds, translate_temporal_formula,
    };

    let mut lower = Lowerer::new(module);
    let problem = lower.prepare_command(index)?;
    if problem.has_softs {
        return Err(FrontError::Resolve(format!(
            "command #{index} carries soft constraints (maxsome/minsome/soft fact); use run_opt_command or :max"
        )));
    }
    reject_opt_markers(index, &problem)?;
    let steps = module.temporal_steps(index);
    // `some Overflow` seeks an overflowing trace via a CEGAR loop that
    // only exists for static Cnfs; reject loudly for temporal commands.
    if problem.overflow == Some(OverflowMode::Some) {
        return Err(FrontError::Resolve(
            "`some Overflow` is not supported for temporal commands yet (use a static `run`)".to_string(),
        ));
    }
    let overflow = problem.overflow;
    let no_overflow = match overflow {
        Some(OverflowMode::No) => true,
        _ => no_overflow,
    };
    // Pre-expansion warnings (generated r$t relations excluded).
    let warnings: Vec<String> = unconstrained_relations(&problem.arena, &problem.bounds, problem.formula)
        .iter()
        .map(|(n, f)| unconstrained_warning(n, *f))
        .collect();
    let mut arena = problem.arena;
    let bounds = problem.bounds;
    let orig_formula = problem.formula;
    let skolemize = kind == CnfKind::Run;

    // HASLab witnesses (run-only, mirrors solve_temporal_with).
    let mut specs = Vec::new();
    if skolemize {
        collect_witness_specs(
            &mut arena,
            &bounds,
            orig_formula,
            true,
            true,
            false,
            &mut specs,
            &mut 0,
        );
    }
    let mut expansion =
        expand_bounds(&arena, &bounds, steps, 1).map_err(|e| FrontError::Solve(e.into()))?;
    let mut witnesses = HashMap::new();
    let mut witness_domains = Vec::new();
    for sp in &specs {
        let upper = alloy_kodkod_rs::skolem::upper_bound_expr(&arena, sp.domain, &bounds)
            .ok_or(TranslateError::BadDomain)
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

    let ctx = BoolCtx::new();
    let (root, origins) = {
        let mut translator = alloy_kodkod_rs::fol::FolTranslator::with_options(
            ctx.clone(),
            &bounds,
            problem.bitwidth,
            no_overflow,
        );
        let root = translator
            .formula_ref(&arena, formula, &[])
            .map_err(FrontError::Solve)?;
        let origins = translator.var_origins().to_vec();
        (root, origins)
    };
    let max_primary = ctx.num_slots();
    let cnf = ctx
        .with_factory(|factory| {
            alloy_kodkod_rs::cnf::translate_to_cnf(factory, root, max_primary)
        })
        .map_err(|e| FrontError::Solve(e.into()))?;

    Ok(Cnf {
        kind,
        command_index: index,
        command_name: command_name_of(module, index),
        arena,
        bounds,
        formula,
        bitwidth: problem.bitwidth,
        skolemize,
        num_vars: cnf.num_vars,
        clauses: cnf.clauses,
        origins,
        warnings,
        overflow,
        is_temporal: true,
        steps,
        orig_formula: Some(orig_formula),
        temporal: Some(expansion),
    })
}
/// Build a `Cnf` from a `run` command (example search).
///
/// Overflow prohibition is ON (overflowing assignments cannot satisfy
/// integer comparisons).
pub fn run(module: &Module, index: usize) -> Result<Cnf, FrontError> {
    build_cnf(module, index, CnfKind::Run, true)
}

/// Build a `Cnf` from a `check` command (counterexample search;
/// the assertion is already negated by lowering).
///
/// Overflow prohibition is ON, like [`run`].
pub fn check(module: &Module, index: usize) -> Result<Cnf, FrontError> {
    build_cnf(module, index, CnfKind::Check, true)
}

/// Build a `Cnf` with explicit overflow handling: `no_overflow = true`
/// is [`run`]/[`check`]; `false` is pure wrapping (overflowing models
/// are kept). Used by the REPL two-phase search (`run`: overflow-free
/// first, wrapping fallback; `check`: wrapping first).
pub fn build_cnf_with(
    module: &Module,
    index: usize,
    kind: CnfKind,
    no_overflow: bool,
) -> Result<Cnf, FrontError> {
    build_cnf(module, index, kind, no_overflow)
}

/// Reconstruct an `Instance` from a SAT assignment over `cnf.origins`.
pub(crate) fn materialize(
    bounds: &Bounds,
    origins: &[VarOrigin],
    truth: impl Fn(u32) -> bool,
) -> Result<Instance, TranslateError> {
    use alloy_kodkod_rs::tupleset::TupleSet;
    let mut inst = Instance::new(bounds.universe(), bounds.pool());
    let mut extras: HashMap<alloy_kodkod_rs::RelationId, Vec<i64>> = HashMap::new();
    for o in origins {
        if truth(o.slot) {
            extras.entry(o.relation).or_default().push(o.tuple_index);
        }
    }
    for r in bounds.relations() {
        let arity = bounds.pool().arity(r);
        let mut ts =
            TupleSet::new(bounds.universe(), arity).map_err(|_| TranslateError::BadDomain)?;
        if let Some(lower) = bounds.lower_bound(r) {
            for idx in lower.index_view().iter() {
                ts.insert_index(idx);
            }
        }
        if let Some(extra) = extras.get(&r) {
            for idx in extra {
                ts.insert_index(*idx);
            }
        }
        let _ = inst.add(r, &ts);
    }
    Ok(inst)
}

/// Builtin validation: is `instance` a model of `cnf`?
///
/// Returns the instance as-is (`Some`, cloned) iff both hold:
/// 1. it respects the `Cnf` bounds (`lower ⊆ instance ⊆ upper`, arity match
///    for every bounded relation), and
/// 2. it satisfies the stored formula (already negated for `check` Cnfs),
///    evaluated semantically with [`alloy_kodkod_rs::eval::Evaluator`].
///
/// Anything else (bounds violation, unsatisfied formula, evaluation error
/// such as a missing relation, universe mismatch) yields `None` (empty).
///
/// Note: instances are expected over the same universe/pool as the `Cnf`
/// (e.g. produced by [`solve`] of the same `Cnf`, or clones modified via
/// [`Instance::add`]); integer bounds are ignored, mirroring `materialize`.
///
/// Temporal Cnfs store time-expanded bounds/formula, so single-state
/// validation is meaningless: returns `None` always. Use
/// [`validate_temporal`] with the full trace instead.
pub fn validate(cnf: &Cnf, instance: &Instance) -> Option<Instance> {
    if cnf.is_temporal {
        return None;
    }
    if instance.universe().size() != cnf.bounds.universe().size() {
        return None;
    }
    for r in cnf.bounds.relations() {
        let inst_ts = instance.tuples(r)?;
        if inst_ts.arity() != cnf.bounds.pool().arity(r) {
            return None;
        }
        if let Some(lower) = cnf.bounds.lower_bound(r) {
            if !inst_ts.covers(lower) {
                return None;
            }
        }
        if let Some(upper) = cnf.bounds.upper_bound(r) {
            if !upper.covers(inst_ts) {
                return None;
            }
        }
    }
    let empty_env = Vec::new();
    let holds = alloy_kodkod_rs::eval::Evaluator::new(instance)
        .with_bitwidth(cnf.bitwidth)
        .formula_bool(&cnf.arena, cnf.formula, &empty_env)
        .unwrap_or(false);
    if holds {
        Some(instance.clone())
    } else {
        None
    }
}

/// Inspect a `Cnf` with the default IPASIR backend.
///
/// - SAT   => `Ok(Some(instance))` (example for `run`, counterexample for `check`)
/// - UNSAT => `Ok(None)` (empty: no example / assertion holds)
///
/// A `some Overflow` Cnf (wrapping build) runs a CEGAR loop instead:
/// models are enumerated until one using integer overflow is found
/// (see [`solve_some_overflow`]).
///
/// For temporal Cnfs this returns the first trace state (`states[0]`) for
/// backwards compatibility; use [`solve_temporal`] for the full lasso trace.
pub fn solve(cnf: &Cnf) -> Result<Option<Instance>, FrontError> {
    if cnf.overflow == Some(OverflowMode::Some) {
        return solve_some_overflow(cnf);
    }
    use alloy_kodkod_rs::ipasir_bridge::IpasirSolver;
    use alloy_kodkod_rs::sat::SatSolver;

    let mut solver =
        IpasirSolver::new().map_err(|e| FrontError::Solve(TranslateError::Solver(e)))?;
    if cnf.num_vars > solver.num_variables() {
        solver.add_variables(cnf.num_vars - solver.num_variables());
    }
    for clause in &cnf.clauses {
        solver.add_clause(clause);
    }
    if SatSolver::solve(&mut solver) {
        let inst = materialize(&cnf.bounds, &cnf.origins, |slot| {
            SatSolver::value_of(&solver, slot as i64)
        })
        .map_err(FrontError::Solve)?;
        if cnf.is_temporal {
            let exp = cnf.temporal.as_ref().ok_or_else(|| {
                FrontError::Resolve("temporal Cnf lacks expansion metadata".into())
            })?;
            let ti = alloy_kodkod_rs::temporal::extract_temporal_instance(&inst, exp)
                .map_err(|e| FrontError::Solve(e.into()))?;
            Ok(ti.states().first().cloned())
        } else {
            Ok(Some(inst))
        }
    } else {
        Ok(None)
    }
}

/// Solve a `some Overflow` Cnf: enumerate wrapping models until one
/// using integer overflow is found.
///
/// Each candidate is checked with the E-bit evaluator
/// (`Evaluator::overflowed`); overflow-free models are excluded with a
/// blocking clause and the search continues. Exhaustion (`None`) means
/// no overflowing model exists. Static Cnfs only (temporal commands
/// with `some Overflow` are rejected at build).
pub fn solve_some_overflow(cnf: &Cnf) -> Result<Option<Instance>, FrontError> {
    use crate::incremental::IncrementalSession;

    let mut sess = IncrementalSession::open(cnf)?;
    let bitwidth = cnf.bitwidth;
    let arena = &cnf.arena;
    let formula = cnf.formula;
    sess.solve_until(|inst| {
        let ev = alloy_kodkod_rs::eval::Evaluator::new(inst).with_bitwidth(bitwidth);
        let empty_env = Vec::new();
        let _ = ev.formula_bool(arena, formula, &empty_env);
        ev.overflowed()
    })
}

/// Inspect a temporal `Cnf`, returning the full lasso trace.
///
/// - SAT   => `Ok(Some(trace))` with `trace.states().len() == steps`
/// - UNSAT => `Ok(None)`
/// - static Cnf => `Err` (use [`solve`]).
pub fn solve_temporal(cnf: &Cnf) -> Result<Option<TemporalInstance>, FrontError> {
    use alloy_kodkod_rs::ipasir_bridge::IpasirSolver;
    use alloy_kodkod_rs::sat::SatSolver;

    if !cnf.is_temporal {
        return Err(FrontError::Resolve(
            "solve_temporal needs a temporal Cnf (use solve)".into(),
        ));
    }
    let exp = cnf.temporal.as_ref().ok_or_else(|| {
        FrontError::Resolve("temporal Cnf lacks expansion metadata".into())
    })?;
    let mut solver =
        IpasirSolver::new().map_err(|e| FrontError::Solve(TranslateError::Solver(e)))?;
    if cnf.num_vars > solver.num_variables() {
        solver.add_variables(cnf.num_vars - solver.num_variables());
    }
    for clause in &cnf.clauses {
        solver.add_clause(clause);
    }
    if SatSolver::solve(&mut solver) {
        let flat = materialize(&cnf.bounds, &cnf.origins, |slot| {
            SatSolver::value_of(&solver, slot as i64)
        })
        .map_err(FrontError::Solve)?;
        let ti = alloy_kodkod_rs::temporal::extract_temporal_instance(&flat, exp)
            .map_err(|e| FrontError::Solve(e.into()))?;
        Ok(Some(ti))
    } else {
        Ok(None)
    }
}

/// Validate a lasso trace against a temporal `Cnf`.
///
/// Returns the trace as-is (`Some`, cloned) iff `TemporalEval` holds for the
/// pre-expansion formula at position 0. Static Cnfs always yield `None`
/// (use [`validate`]).
pub fn validate_temporal(cnf: &Cnf, trace: &TemporalInstance) -> Option<TemporalInstance> {
    if !cnf.is_temporal {
        return None;
    }
    let orig = cnf.orig_formula?;
    if trace.len() != cnf.steps {
        return None;
    }
    let holds = alloy_kodkod_rs::temporal::TemporalEval::new(trace)
        .with_bitwidth(cnf.bitwidth)
        .holds(&cnf.arena, orig)
        .unwrap_or(false);
    if holds {
        Some(trace.clone())
    } else {
        None
    }
}
