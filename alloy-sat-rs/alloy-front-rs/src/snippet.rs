//! REPL snippets: single declarations, bare expressions, and ad-hoc queries.
//!
//! - [`fragment_keys`] classifies one input fragment for the accumulating
//!   REPL buffer. Single named declarations (`sig`/`pred`/`fun`/`assert`/
//!   named `fact`) yield replace keys; everything else is append-only.
//! - [`parse_expr`] parses a bare relational expression (`let`..`in` allowed).
//! - [`eval`] checks a bare formula, or a bare expression lifted with `some`,
//!   as `run { ... }` (satisfiability check).
//! - [`query`] lowers an expression reusing a solved `Cnf`'s arena (so
//!   relation IDs line up with the instance) and evaluates it against that
//!   instance (Java-Evaluator style).

use alloy_kodkod_rs::instance::Instance;
use alloy_kodkod_rs::tupleset::TupleSet;

use crate::ast::{Expr, Formula, Module, Scope};
use crate::cnf::Cnf;
use crate::lower::Lowerer;
use crate::FrontError;

/// Parse a bare relational expression (`let x = e in ...` allowed).
pub fn parse_expr(src: &str) -> Result<Expr, FrontError> {
    let toks = crate::lex::lex(src)?;
    crate::parser::Parser::new(toks).expr()
}

/// Parse a bare top-level formula.
pub fn parse_formula(src: &str) -> Result<Formula, FrontError> {
    let toks = crate::lex::lex(src)?;
    crate::parser::Parser::new(toks).formula_top()
}

/// Classify a REPL fragment for the accumulating buffer.
///
/// Returns replace keys: at most one entry per declared name, so re-entering
/// a `sig`/`pred`/`fun`/`assert`/named-`fact` swaps the old fragment out.
/// An empty vector means append-only (anonymous facts, commands, `open`s,
/// multi-declaration pastes).
pub fn fragment_keys(src: &str) -> Result<Vec<String>, FrontError> {
    let m: Module = crate::parse_module(src)?;
    let mut keys = Vec::new();
    let total = m.sigs.len() + m.facts.len() + m.paras.len() + m.commands.len() + m.opens.len();
    if total != 1 {
        return Ok(keys);
    }
    for sd in &m.sigs {
        for name in &sd.names {
            keys.push(format!("sig:{name}"));
        }
    }
    for (name, _) in &m.facts {
        if let Some(n) = name {
            keys.push(format!("fact:{n}"));
        }
    }
    for p in &m.paras {
        keys.push(format!("para:{}", p.name));
    }
    Ok(keys)
}

/// Satisfiability check of bare input over `source`.
///
/// A bare formula is used as-is; a bare relational expression is lifted
/// with `some (...)` (non-emptiness check). Either way it runs as a
/// synthesized trailing `run { ... }` (same trick as `als -e`).
pub fn eval(
    source: &str,
    input: &str,
) -> Result<alloy_kodkod_rs::solver::Solution, FrontError> {
    let body = if parse_formula(input).is_ok() {
        input.to_string()
    } else {
        // Sharper error when it is neither formula nor expression.
        parse_expr(input)?;
        format!("some ({input})")
    };
    let wrapped = format!("{source}\nrun {{ {body} }}");
    let m = crate::parse_module(&wrapped)?;
    let idx = m
        .commands
        .len()
        .checked_sub(1)
        .ok_or_else(|| FrontError::Resolve("eval produced no command".to_string()))?;
    crate::run_command(&m, idx)
}

/// Evaluate a bare relational expression against a solved instance.
///
/// The expression is lowered reusing `cnf`'s arena clone (relation IDs stay
/// aligned with `instance`, which must come from the same `Cnf`), in `scope`'s
/// typing context, then read out with the kodkod evaluator.
/// Returns `(arity, tuple set)`.
pub fn query(
    module: &Module,
    scope: &Scope,
    cnf: &Cnf,
    expr_src: &str,
    instance: &Instance,
) -> Result<(u32, TupleSet), FrontError> {
    let e = parse_expr(expr_src)?;
    let mut arena = cnf.arena.clone();
    let mut lower = Lowerer::new(module);
    let (eid, arity) = lower.lower_expr_in_scope(scope, &mut arena, &e)?;
    let empty_env = Vec::new();
    let ts = alloy_kodkod_rs::eval::Evaluator::new(instance)
        .expr_set(&arena, eid, &empty_env)
        .map_err(|e| FrontError::Resolve(e.to_string()))?;
    Ok((arity, ts))
}
