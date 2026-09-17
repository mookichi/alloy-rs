//! REPL-oriented split API: `run` / `check` build a `Cnf` value,
//! `solve` inspects it and returns an `Instance` (or nothing).
//!
//! - `run`  : satisfiability search. `solve` SAT => example instance.
//! - `check`: negated assertion search (lowering already negates).
//!            `solve` SAT => counterexample instance,
//!            `solve` UNSAT => `None` (assertion holds, empty).
//! - `validate(cnf, instance)`: builtin check. Returns the instance
//!            as-is (`Some`) iff it is a model of the `Cnf`,
//!            otherwise `None` (empty).
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

use crate::ast::{CommandKind, Module};
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

fn command_name_of(module: &Module, index: usize) -> Option<String> {
    module.commands.get(index).and_then(|c| match &c.kind {
        CommandKind::Run(n) | CommandKind::Check(n) => n.clone(),
        CommandKind::Maximize { name: n, .. } | CommandKind::Minimize { name: n, .. } => n.clone(),
    })
}

/// Shared builder: lower, optionally skolemize (Run only), then
/// FOL -> bool circuit -> CNF, capturing origins for later materialize.
fn build_cnf(module: &Module, index: usize, kind: CnfKind) -> Result<Cnf, FrontError> {
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
        return build_temporal_cnf(module, index, kind);
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
    let mut arena = problem.arena;
    let mut bounds = problem.bounds;
    let mut formula = problem.formula;
    let skolemize = kind == CnfKind::Run;

    // Mirror Solver::solve skolem handling: positive existentials become
    // witness relations on a cloned bounds set (Run only).
    if skolemize {
        match alloy_kodkod_rs::skolem::skolemize_static(&mut arena, &mut bounds, formula)
            .map_err(|e| FrontError::Solve(e.into()))?
        {
            Some(sk) => formula = sk.formula,
            None => {}
        }
    }

    let ctx = BoolCtx::new();
    // FolTranslator borrows bounds; collect owned data then drop it.
    let (root, origins) = {
        let mut translator = alloy_kodkod_rs::fol::FolTranslator::new(ctx.clone(), &bounds);
        translator.set_bitwidth(problem.bitwidth);
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
fn build_temporal_cnf(module: &Module, index: usize, kind: CnfKind) -> Result<Cnf, FrontError> {
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
    let steps = module.temporal_steps(index);
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
        let mut translator = alloy_kodkod_rs::fol::FolTranslator::new(ctx.clone(), &bounds);
        translator.set_bitwidth(problem.bitwidth);
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
        is_temporal: true,
        steps,
        orig_formula: Some(orig_formula),
        temporal: Some(expansion),
    })
}
/// Build a `Cnf` from a `run` command (example search).
pub fn run(module: &Module, index: usize) -> Result<Cnf, FrontError> {
    build_cnf(module, index, CnfKind::Run)
}

/// Build a `Cnf` from a `check` command (counterexample search;
/// the assertion is already negated by lowering).
pub fn check(module: &Module, index: usize) -> Result<Cnf, FrontError> {
    build_cnf(module, index, CnfKind::Check)
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
        let inst_ts = match instance.tuples(r) {
            Some(t) => t,
            None => return None,
        };
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
/// For temporal Cnfs this returns the first trace state (`states[0]`) for
/// backwards compatibility; use [`solve_temporal`] for the full lasso trace.
pub fn solve(cnf: &Cnf) -> Result<Option<Instance>, FrontError> {
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
        .holds(&cnf.arena, orig)
        .unwrap_or(false);
    if holds {
        Some(trace.clone())
    } else {
        None
    }
}
