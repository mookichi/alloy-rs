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
use alloy_kodkod_rs::intset::IntSet;
use alloy_kodkod_rs::tupleset::TupleSet;

use crate::ast::{Expr, Formula, IntExpr, Module, Scope};
use crate::cnf::Cnf;
use crate::lower::Lowerer;
use crate::FrontError;

/// Parse a bare relational expression (`let x = e in ...` allowed).
pub fn parse_expr(src: &str) -> Result<Expr, FrontError> {
    let toks = crate::lex::lex(src)?;
    crate::parser::Parser::new(toks).expr()
}

/// Parse a bare integer expression (`#A`, `#A + 1`, ...).
pub fn parse_int_expr(src: &str) -> Result<IntExpr, FrontError> {
    let toks = crate::lex::lex(src)?;
    crate::parser::Parser::new(toks).int_expr_top()
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
    match query_value(module, scope, cnf, expr_src, instance)? {
        QueryValue::Set(arity, ts) => Ok((arity, ts)),
        QueryValue::Int(_) => Err(FrontError::Resolve(format!(
            "`{expr_src}` is an integer expression, not a set"
        ))),
    }
}

/// A `:query` result: either a tuple set or an integer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QueryValue {
    Set(u32, TupleSet),
    Int(i64),
}

/// Evaluate a bare expression against a solved instance, accepting both
/// relational expressions (`A`, `A.f`) and integer expressions (`#A`).
///
/// Integer-shaped input (literals, `#A`, `sum ...`, arithmetic over them —
/// anything [`IntExpr::int_typed`]) evaluates as an integer, so `1+1`
/// yields `2` rather than the `{1}` union. Anything involving a set-typed
/// operand falls through to the relational path below. When both fail,
/// the relational parse error is reported.
pub fn query_value(
    module: &Module,
    scope: &Scope,
    cnf: &Cnf,
    expr_src: &str,
    instance: &Instance,
) -> Result<QueryValue, FrontError> {
    if let Ok(ie) = parse_int_expr(expr_src) {
        if ie.int_typed() {
            return query_int_parsed(module, scope, cnf, &ie, instance);
        }
    }
    match parse_expr(expr_src) {
        Ok(e) => {
            if matches!(e, Expr::IntAtom(_)) {
                // `Int` (or `int`): every in-scope integer, i.e. the union
                // of the Cnf's exact int bounds. Handled here because the
                // evaluator only sees instance tuples, not bounds.
                let mut set = IntSet::new();
                for (_, ts) in cnf.bounds.int_bounds() {
                    for idx in ts.index_view().iter() {
                        set.insert(idx);
                    }
                }
                let ts = TupleSet::from_indices(instance.universe(), 1, set)
                    .map_err(|_| FrontError::Resolve("cannot build Int tuple set".to_string()))?;
                return Ok(QueryValue::Set(1, ts));
            }
            let mut arena = cnf.arena.clone();
            let mut lower = Lowerer::new(module);
            let (eid, arity) = lower.lower_expr_in_scope(scope, &mut arena, &e)?;
            let empty_env = Vec::new();
            let ts = alloy_kodkod_rs::eval::Evaluator::new(instance)
                .expr_set(&arena, eid, &empty_env)
                .map_err(|e| FrontError::Resolve(e.to_string()))?;
            Ok(QueryValue::Set(arity, ts))
        }
        Err(expr_err) => Err(expr_err),
    }
}

/// Evaluate an already-parsed integer expression against `instance`.
fn query_int_parsed(
    module: &Module,
    scope: &Scope,
    cnf: &Cnf,
    ie: &IntExpr,
    instance: &Instance,
) -> Result<QueryValue, FrontError> {
    // `#Int` (or `#int`): the int-atom count is known from the
    // Cnf's exact int bounds; no solving or evaluation needed.
    if matches!(&ie, IntExpr::Card(e, _) if matches!(e.as_ref(), Expr::IntAtom(_))) {
        return Ok(QueryValue::Int(cnf.bounds.int_bounds().count() as i64));
    }
    // Out-of-range literals wrap (two's complement truncation), matching
    // both the solve path and Java's evaluator.
    let ie = wrap_int_literals(&ie, cnf.bitwidth);
    let mut arena = cnf.arena.clone();
    let mut lower = Lowerer::new(module);
    let iid = lower.lower_int_in_scope(scope, &mut arena, &ie)?;
    let empty_env = Vec::new();
    let v = alloy_kodkod_rs::eval::Evaluator::new(instance)
        .int_value(&arena, iid, &empty_env)
        .map_err(|e| FrontError::Resolve(e.to_string()))?;
    Ok(QueryValue::Int(v))
}

/// Truncate `v` to `bitwidth`-bit two's complement, mirroring
/// `IntCircuit::constant` (low bits kept, sign-extended).
fn wrap_lit(v: i64, bitwidth: u32) -> i64 {
    if bitwidth >= 64 {
        return v;
    }
    if bitwidth == 0 {
        return 0;
    }
    let shift = 64 - bitwidth;
    (v << shift) >> shift
}

/// Rewrite every integer literal in `ie` to its bitwidth-wrapped value so
/// query evaluation observes the same wrapping as the solve path (and as
/// Java's evaluator).
fn wrap_int_literals(ie: &IntExpr, bitwidth: u32) -> IntExpr {
    match ie {
        IntExpr::Lit(v, p) => IntExpr::Lit(wrap_lit(*v, bitwidth), *p),
        IntExpr::Bin(op, a, b) => IntExpr::Bin(
            *op,
            Box::new(wrap_int_literals(a, bitwidth)),
            Box::new(wrap_int_literals(b, bitwidth)),
        ),
        IntExpr::Sum(decls, body, p) => IntExpr::Sum(
            decls.clone(),
            Box::new(wrap_int_literals(body, bitwidth)),
            *p,
        ),
        IntExpr::Card(..) | IntExpr::Val(..) | IntExpr::SumOf(..) => ie.clone(),
    }
}
