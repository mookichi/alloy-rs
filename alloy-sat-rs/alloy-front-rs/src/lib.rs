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

pub use ast::Scope;
pub use ast::{
    BinOp, CmpKind, Command, CommandKind, Decl, Expr, Formula, IntBinOp, IntCmpOp, IntExpr, Module,
    Open, OpenParam, OptSpec, PartialDef, PartialEntry, PartialOp, QuantKind, SigDecl, SigMult,
    DEFAULT_INT_BITWIDTH, effective_bitwidth, effective_int_count, module_needs_int_atoms,
};
pub use lower::{LoweredOpt, LoweredTarget, Lowerer, LoweredProblem};
pub use cnf::{check, run, solve, validate, Cnf, CnfKind};
pub use incremental::{IncrementalSession, MultKind, SessionStats};
pub use partial::{verifier_pin_from_partial, PartialInstance, PartialInt, PartialRel};
pub use cegis::{run_cegis, CegisConfig, CegisOutcome, CegisReport};
pub use snippet::{
    eval, fragment_keys, parse_expr, parse_formula, parse_int_expr, query, query_value, QueryValue,
};
pub use alloy_kodkod_rs::tupleset::TupleSet;
pub use alloy_kodkod_rs::instance::Instance;
pub use alloy_kodkod_rs::opt::{Objective as KkObjective, OptSense as KkOptSense, OptSolution};

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
/// `maximize`/`minimize` command, or a `run`/`check` whose facts or body
/// carry AlloyMax soft nodes. Runs a cheap prepare to read the flag;
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
        .map(|p| p.has_softs)
        .unwrap_or(false)
}

/// Runs a `maximize`/`minimize` command end-to-end (translate + optimize).
/// Also serves `run`/`check` commands whose bodies carry AlloyMax soft
/// nodes (`maxsome` / `minsome`) or modules with `soft fact`s, using
/// [`KkObjective::collected`]. Returns the optimal model and its exact
/// cost. Errors on plain `run`/`check` commands (use [`run_command`])
/// and on temporal commands.
pub fn run_opt_command(module: &Module, index: usize) -> Result<OptSolution, FrontError> {
    let mut lower = Lowerer::new(module);
    let problem = lower.prepare_command(index)?;
    let kk_objective = match problem.objective {
        Some(objective) => match (objective.sense, objective.target) {
            (KkOptSense::Maximize, LoweredTarget::Int(id)) => KkObjective::max_int(id),
            (KkOptSense::Minimize, LoweredTarget::Int(id)) => KkObjective::min_int(id),
            (KkOptSense::Maximize, LoweredTarget::Weighted(w)) => KkObjective::max_weighted(w),
            (KkOptSense::Minimize, LoweredTarget::Weighted(w)) => KkObjective::min_weighted(w),
        },
        None if problem.has_softs => KkObjective::collected(),
        None => {
            return Err(FrontError::Resolve(format!(
                "command #{index} is not maximize/minimize and carries no soft constraints (use run_command)"
            )));
        }
    };
    if module.is_temporal_command(index) {
        return Err(FrontError::Unsupported(
            "temporal optimization is not supported yet".into(),
        ));
    }

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
            ..Default::default()
        });
    solver
        .solve_opt(&arena, formula, &bounds, kk_objective)
        .map_err(FrontError::Solve)
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
    // them, and the temporal path cannot see them at all).
    if problem.has_softs {
        return Err(FrontError::Resolve(format!(
            "command #{index} carries soft constraints (maxsome/minsome/soft fact); use run_opt_command"
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
