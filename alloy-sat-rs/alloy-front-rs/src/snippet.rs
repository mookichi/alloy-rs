//! REPL snippets: single declarations, bare expressions, and ad-hoc queries.
//!
//! - [`fragment_keys`] classifies one input fragment for the accumulating
//!   REPL buffer. Single named declarations (`sig`/`pred`/`fun`/`assert`/
//!   named `fact`) yield replace keys; everything else is append-only.
//! - [`parse_expr`] parses a bare relational expression (`let`..`in` allowed).
//! - [`eval`] checks a bare formula, or a bare expression lifted with `some`,
//!   as `run { ... }` (satisfiability check).
//! - [`query`] lowers an expression into a scratch arena sharing the
//!   instance's relation pool (so relation IDs line up with the instance
//!   even when `cnf` comes from an independent lowering whose own pool
//!   assigns different IDs) and evaluates it against that instance
//!   (Java-Evaluator style). `cnf` still supplies int bounds + bitwidth.

use std::sync::Arc;

use alloy_kodkod_rs::ast::AstArena;
use alloy_kodkod_rs::instance::Instance;
use alloy_kodkod_rs::intset::IntSet;
use alloy_kodkod_rs::real::{
    decimal_to_real, decimal_to_real_rounded, next_down, next_up, RealCenter, RealRound,
};
use alloy_kodkod_rs::tupleset::TupleSet;

use crate::ast::{Expr, Formula, IntExpr, Module, Scope};
use crate::cnf::Cnf;
use crate::lower::Lowerer;
use crate::types::is_int_query;
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
/// a `sig`/`pred`/`fun`/`assert`/named-`fact`/`partial` swaps the old
/// fragment out. An empty vector means append-only (anonymous facts,
/// commands, `open`s, multi-declaration pastes).
pub fn fragment_keys(src: &str) -> Result<Vec<String>, FrontError> {
    let m: Module = crate::parse_module(src)?;
    let mut keys = Vec::new();
    let total = m.sigs.len()
        + m.facts.len()
        + m.paras.len()
        + m.commands.len()
        + m.opens.len()
        + m.partials.len();
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
    for p in &m.partials {
        keys.push(format!("partial:{}", p.name));
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
    eval_in_scope(source, input, None)
}

/// [`eval`], but the synthesized trailing `run { ... }` uses `scope` when
/// given (REPL `:eval` inherits the selected Cnf's command scope so ad-hoc
/// checks explore the same problem, e.g. the same `for N Int` widths that
/// `setEReal` conversions depend on). `None` keeps the default scope.
pub fn eval_in_scope(
    source: &str,
    input: &str,
    scope: Option<&Scope>,
) -> Result<alloy_kodkod_rs::solver::Solution, FrontError> {
    let body = if parse_formula(input).is_ok() {
        input.to_string()
    } else {
        // Sharper error when it is neither formula nor expression.
        parse_expr(input)?;
        format!("some ({input})")
    };
    let wrapped = format!("{source}\nrun {{ {body} }}");
    let mut m = crate::parse_module(&wrapped)?;
    let idx = m
        .commands
        .len()
        .checked_sub(1)
        .ok_or_else(|| FrontError::Resolve("eval produced no command".to_string()))?;
    if let Some(scope) = scope {
        m.commands[idx].scope = scope.clone();
    }
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
        QueryValue::Bool(_) => Err(FrontError::Resolve(format!(
            "`{expr_src}` is a formula, not a set"
        ))),
        QueryValue::Real(_) => Err(FrontError::Resolve(format!(
            "`{expr_src}` is a computed Real value, not a set"
        ))),
    }
}

/// A `:query` result: either a tuple set, an integer, a formula verdict,
/// or a computed exact-centre Real value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QueryValue {
    Set(u32, TupleSet),
    Int(i64),
    Bool(bool),
    /// Computed `Real` centre from a `realUp`/`realDown` query or a
    /// `{ v: Real | v.realSucc[e] }`-shaped comprehension. Unlike
    /// `Set` this is not an instance atom: the lane successor of a value
    /// generally lies outside the solved atom population (e.g. with
    /// `one sig X extends Real`, `Real = {X$0}`), so evaluating the
    /// desugared comprehension by instance enumeration would yield `{}`.
    /// The lane oracle (`next_up`/`next_down`) answers it instead.
    Real(RealCenter),
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
        // A bare `{...}` (or `+`/`-` over one) keeps the set reading,
        // mirroring the parser's `=`/`!=` rewind rule; pure `*`/`/`/`%`
        // trees read as integers.
        if is_int_query(&ie) {
            return query_int_parsed(module, scope, cnf, &ie, instance);
        }
    }
    match parse_expr(expr_src) {
        Ok(e) => {
            if matches!(e, Expr::IntAtom) {
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
            // `realUp`/`realDown` are computed functions, not relations:
            // answer via the lane oracle (see `QueryValue::Real`).
            if let Expr::Call(name, args, _) = &e {
                if (name == "realUp" || name == "realDown") && args.len() == 1 {
                    return query_real_fun(module, scope, &e, name == "realUp", &args[0], instance);
                }
            }
            if let Some(qv) = query_succ_set(module, scope, &e, instance)? {
                return Ok(qv);
            }
            let (arity, ts) = query_set_parsed(module, scope, &e, instance)?;
            Ok(QueryValue::Set(arity, ts))
        }
        Err(expr_err) => {
            // Not an expression: try a closed formula (`1 = 1`, `A = A`).
            // Garbage reports the relational parse error, not the
            // formula one.
            match parse_formula(expr_src) {
                Ok(_) => query_formula(module, scope, cnf, expr_src, instance),
                Err(_) => Err(expr_err),
            }
        }
    }
}

/// Lower a parsed relational expression and evaluate it against
/// `instance` (shared relational path for `:query`).
fn query_set_parsed(
    module: &Module,
    scope: &Scope,
    e: &Expr,
    instance: &Instance,
) -> Result<(u32, TupleSet), FrontError> {
    let mut arena = AstArena::with_pool(Arc::clone(instance.pool()));
    let mut lower = Lowerer::new(module);
    let (eid, arity) = lower.lower_expr_in_scope(scope, &mut arena, e)?;
    let empty_env = Vec::new();
    let ts = alloy_kodkod_rs::eval::Evaluator::new(instance)
        .expr_set(&arena, eid, &empty_env)
        .map_err(|e| FrontError::Resolve(e.to_string()))?;
    Ok((arity, ts))
}

/// Lane widths for oracle queries (`realUp`/`realDown`, successor
/// comprehensions) from the query command's scope.
fn real_lane_widths(module: &Module, scope: &Scope) -> Result<(u32, u32), FrontError> {
    let w = crate::bounds::resolve(module, scope)
        .map_err(FrontError::Resolve)?
        .mepk_widths;
    Ok((w.m_width, w.e_width))
}

/// Resolve a Real-valued query argument to its exact centre.
///
/// Decimal literals fold like the solve path (`RealLit` exact dyadic
/// only; `(d)` nearest). Anything else must evaluate to a singleton
/// atom set whose `(m, e)` lanes are read from the instance.
/// Returns `None` when no centre applies (non-dyadic plain literal,
/// empty/multi-element set, undecodable lanes): the caller falls back
/// to instance enumeration, which stays sound there.
fn real_arg_centre(
    module: &Module,
    scope: &Scope,
    mw: u32,
    arg: &Expr,
    instance: &Instance,
) -> Option<RealCenter> {
    match arg {
        Expr::RealLit(s, _) => {
            if let Some(v) = decimal_to_real(s, Some(mw)) {
                return Some(v);
            }
            // Approximable-but-plain literal: predicate position treats
            // it as UNSAT (enumeration), so fall through rather than
            // erroring here.
            None
        }
        Expr::ApproxRealLit(s, _) => {
            decimal_to_real_rounded(s, Some(mw), RealRound::Nearest)
        }
        _ => {
            let (arity, ts) = query_set_parsed(module, scope, arg, instance).ok()?;
            if arity != 1 {
                return None;
            }
            let idxs: Vec<_> = ts.index_view().iter().collect();
            if idxs.len() != 1 {
                return None;
            }
            let decoded = crate::display::decode_ereal(instance)?;
            let d = decoded.get(&(idxs[0] as u32))?;
            RealCenter::new(d.lanes.0 as i128, d.lanes.1 as i32)
        }
    }
}

/// Step a centre through the lane oracle, reporting a range exit loudly
/// (mirrors the solve path, where a missing successor is UNSAT).
fn real_oracle_step(
    name: &str,
    up: bool,
    centre: &RealCenter,
    mw: u32,
    ew: u32,
) -> Result<QueryValue, FrontError> {
    let next = if up {
        next_up(centre, mw, ew)
    } else {
        next_down(centre, mw, ew)
    };
    match next {
        Some(v) => Ok(QueryValue::Real(v)),
        None => Err(FrontError::Resolve(format!(
            "`{name}` of {} [m={} e={}] leaves the lane range",
            centre.centre_short(),
            centre.m,
            centre.e,
        ))),
    }
}

/// Evaluate a `realUp[x]` / `realDown[x]` query via the lane oracle.
///
/// The solve-path desugaring (`{ $r: Real | realSucc[$r, x] }`) only
/// ranges over the solved atom population, so a `:query` of it yields
/// `{}` whenever the successor is not itself an atom of the instance
/// (the common case, e.g. `one sig X extends Real`). The argument is
/// resolved to its exact centre instead and stepped with
/// `next_up`/`next_down`. Non-centre arguments fall back to instance
/// enumeration.
fn query_real_fun(
    module: &Module,
    scope: &Scope,
    orig: &Expr,
    up: bool,
    arg: &Expr,
    instance: &Instance,
) -> Result<QueryValue, FrontError> {
    let name = if up { "realUp" } else { "realDown" };
    let (mw, ew) = real_lane_widths(module, scope)?;
    match real_arg_centre(module, scope, mw, arg, instance) {
        Some(centre) => real_oracle_step(name, up, &centre, mw, ew),
        None => {
            let (arity, ts) = query_set_parsed(module, scope, orig, instance)?;
            Ok(QueryValue::Set(arity, ts))
        }
    }
}

/// Evaluate a `{ v: Real | v.realSucc[e] }` / `{ v: Real | v.realPred[e] }`
/// query (either orientation) via the lane oracle.
///
/// Same atom-population limitation as [`query_real_fun`]: the successor
/// is computed from `e`'s centre instead of enumerated. Only the exact
/// shape qualifies — a single `Real`-typed binding whose body is one
/// `realSucc`/`realPred` call with the bound variable bare on one side
/// and a variable-free closed argument (literal or plain name) on the
/// other. Anything else (domain-restricted bindings, compound bodies,
/// nested bound variables) falls through to instance enumeration, which
/// stays sound there.
fn query_succ_set(
    module: &Module,
    scope: &Scope,
    e: &Expr,
    instance: &Instance,
) -> Result<Option<QueryValue>, FrontError> {
    let (decls, body) = match e {
        Expr::Comprehension(decls, body) => (decls, body),
        _ => return Ok(None),
    };
    if decls.len() != 1 || decls[0].names.len() != 1 {
        return Ok(None);
    }
    if !matches!(&decls[0].expr, Expr::Name(n, _) if n == "Real") {
        return Ok(None);
    }
    let var = &decls[0].names[0];
    let (name, args) = match body.as_ref() {
        Formula::Call(n, a, _) => (n.as_str(), a),
        _ => return Ok(None),
    };
    if args.len() != 2 {
        return Ok(None);
    }
    // `realSucc[B, A]`: B = succ(A); `realPred[B, A]`: B = pred(A).
    let succ = match name {
        "realSucc" => true,
        "realPred" => false,
        _ => return Ok(None),
    };
    let var_side = if matches!(&args[0], Expr::Name(n, _) if n == var) {
        0
    } else if matches!(&args[1], Expr::Name(n, _) if n == var) {
        1
    } else {
        return Ok(None);
    };
    // The other side must be closed over a literal or a plain,
    // non-shadowed name (no nesting of the bound variable, no computed
    // shapes that could rebind it).
    let other = &args[1 - var_side];
    let closed = match other {
        Expr::RealLit(..) | Expr::ApproxRealLit(..) => true,
        Expr::Name(n, _) => n != var,
        _ => false,
    };
    if !closed {
        return Ok(None);
    }
    let (mw, ew) = real_lane_widths(module, scope)?;
    let centre = match real_arg_centre(module, scope, mw, other, instance) {
        Some(c) => c,
        None => return Ok(None),
    };
    // Forward (solving for the result side) steps with the predicate's
    // own direction; backward (solving for the input side) inverts it.
    let fwd = succ == (var_side == 0);
    Ok(Some(real_oracle_step(name, fwd, &centre, mw, ew)?))
}

/// Evaluate a bare formula against a solved instance (REPL `:query` of
/// closed formulas such as `1 = 1` or `7 = {0, 1, 2}`).
fn query_formula(
    module: &Module,
    scope: &Scope,
    cnf: &Cnf,
    form_src: &str,
    instance: &Instance,
) -> Result<QueryValue, FrontError> {
    let f = parse_formula(form_src)?;
    // Same lazy-allocation guard as the int path: a formula mentioning
    // Int atoms cannot evaluate against an atom-free instance.
    {
        let mut needs = false;
        crate::ast::scan_formula_int_set(&f, &mut needs);
        if needs && cnf.bounds.int_bounds().count() == 0 {
            return Err(FrontError::Resolve(
                "integer set is not in scope (this model materializes no Int atoms; mention Int in the model or add `for N Int` to the scope)".to_string(),
            ));
        }
    }
    let mut arena = AstArena::with_pool(Arc::clone(instance.pool()));
    let mut lower = Lowerer::new(module);
    let fid = lower.lower_formula_in_scope(scope, &mut arena, &f)?;
    let empty_env = Vec::new();
    let v = alloy_kodkod_rs::eval::Evaluator::new(instance)
        .with_bitwidth(cnf.bitwidth)
        .formula_bool(&arena, fid, &empty_env)
        .map_err(|e| FrontError::Resolve(e.to_string()))?;
    Ok(QueryValue::Bool(v))
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
    if matches!(&ie, IntExpr::Card(e, _) if matches!(e.as_ref(), Expr::IntAtom)) {
        return Ok(QueryValue::Int(cnf.bounds.int_bounds().count() as i64));
    }
    // A bit-value over atoms the model never materialized cannot
    // evaluate: report the out-of-scope error instead of a silent 0
    // (mirrors the set-position literal path).
    {
        let mut needs = false;
        crate::ast::scan_intexpr_int_set(ie, &mut needs);
        if needs && cnf.bounds.int_bounds().count() == 0 {
            return Err(FrontError::Resolve(
                "integer set is not in scope (this model materializes no Int atoms; mention Int in the model or add `for N Int` to the scope)".to_string(),
            ));
        }
    }
    // Out-of-range literals wrap at evaluation (`Evaluator` truncates
    // constants to the problem bitwidth, matching the solve path and
    // Java's evaluator), so no literal rewriting is needed here.
    let mut arena = AstArena::with_pool(Arc::clone(instance.pool()));
    let mut lower = Lowerer::new(module);
    let iid = lower.lower_int_in_scope(scope, &mut arena, ie)?;
    let empty_env = Vec::new();
    let v = alloy_kodkod_rs::eval::Evaluator::new(instance)
        .with_bitwidth(cnf.bitwidth)
        .int_value(&arena, iid, &empty_env)
        .map_err(|e| FrontError::Resolve(e.to_string()))?;
    Ok(QueryValue::Int(v))
}
