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

mod ast;
mod bounds;
mod lex;
mod lower;
mod parser;

pub use ast::Scope;
pub use ast::{
    Command, CommandKind, Decl, Expr, Formula, IntBinOp, IntCmpOp, IntExpr, Module, Open,
    OpenParam, SigDecl, SigMult,
};
pub use lower::Lowerer;

use alloy_kodkod_rs::solver::Solution;

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

/// Runs one command of a parsed module end-to-end (translate + solve).
pub fn run_command(module: &Module, index: usize) -> Result<Solution, FrontError> {
    let cmd = module
        .commands
        .get(index)
        .ok_or_else(|| FrontError::Resolve(format!("no command #{index}")))?;
    let mut lower = Lowerer::new(module);
    let problem = lower.prepare_command(index)?;

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
