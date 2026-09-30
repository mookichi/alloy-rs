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
    decimal_to_real, decimal_to_real_rounded, next_down, next_up, real_add, real_div,
    real_mul, RealCenter, RealRound,
};
use alloy_kodkod_rs::tupleset::TupleSet;

use crate::ast::{BinOp, Decl, Expr, FindSel, Formula, IntExpr, Module, Scope};
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
    /// Computed `Real` centre from a `realUp`/`realDown` function query,
    /// or from an oracle-answered comprehension whose centre has no
    /// lane-bit set in this instance (the bit-free exact zero, or a
    /// model whose universe carries no `M$`/`E$` lane atoms, e.g.
    /// `one sig X extends Real`). Unlike `Set` this is not an instance
    /// tuple set: the computed value generally lies outside the solved
    /// atom population, so evaluating the desugared comprehension by
    /// instance enumeration would yield `{}`. Whenever the centre does
    /// expand to a non-empty lane-bit set, the oracle paths below return
    /// `Set` instead, so comprehensions always denote sets.
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
            // Bare decimal literals decode to their centre (mirrors the
            // solve path: exact dyadic for `d`, nearest for `(d)`), then
            // expand to the lane-bit atom set when possible.
            if matches!(e, Expr::RealLit(..) | Expr::ApproxRealLit(..)) {
                return query_real_lit(module, scope, &e, instance);
            }
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
            // Value-finding `{[any|min|max] x in D | F}`: explicit opt-in
            // to value computation (oracle fast path + bounded value-space
            // enumeration in `query_find`). Plain `{x: D | F}`
            // comprehensions stay purely enumerative and are evaluated
            // below via `query_set_parsed`.
            if let Expr::Find(sel, decls, body) = &e {
                return query_find(module, scope, cnf, *sel, decls, body, instance);
            }
            // `realUp`/`realDown` are computed functions, not relations:
            // answer via the lane oracle (see `QueryValue::Real`).
            if let Expr::Call(name, args, _) = &e {
                if (name == "realUp" || name == "realDown") && args.len() == 1 {
                    return query_real_fun(module, scope, &e, name == "realUp", &args[0], instance);
                }
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

/// Resolve a bare decimal literal query to its exact centre.
///
/// `d` needs an exact dyadic conversion (a plain non-dyadic literal
/// errors loudly instead of rounding silently — use the `(d)`
/// spelling for the nearest centre); `(d)` rounds to nearest.
/// Malformed/range literals fail loudly, as in `setReal`.
///
/// The centre then expands to its lane-bit atom set (`M$i`/`E$j`,
/// two's complement — the inverse of `display::decode_bitset`), so the
/// query prints `{M$0, ...} = 1.25 [m=.. e=..]`. Expansion failures
/// (missing lane atoms, out-of-range lanes, the bit-free exact zero)
/// keep the computed `Real` reading.
fn query_real_lit(
    module: &Module,
    scope: &Scope,
    e: &Expr,
    instance: &Instance,
) -> Result<QueryValue, FrontError> {
    let (mw, ew) = real_lane_widths(module, scope)?;
    let centre = crate::lower::decimal_centre(e, mw)?;
    if let Some(ts) = centre_atom_set(instance, mw, ew, &centre) {
        return Ok(QueryValue::Set(1, ts));
    }
    Ok(QueryValue::Real(centre))
}

/// Lane-bit atom set for a decoded centre via the shared
/// `centre_lane_indices`; `None` keeps the `Real` reading.
fn centre_atom_set(
    instance: &Instance,
    mw: u32,
    ew: u32,
    centre: &RealCenter,
) -> Option<TupleSet> {
    let idxs = crate::lower::centre_lane_indices(instance.universe(), mw, ew, centre)?;
    if idxs.is_empty() {
        return None;
    }
    let mut set = IntSet::new();
    for i in idxs {
        set.insert(i as i64);
    }
    TupleSet::from_indices(instance.universe(), 1, set).ok()
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
/// only; `(d)` nearest). Anything else must evaluate to a set whose
/// `(m, e)` centre can be read from the instance: either a singleton
/// `extends Real` member atom (via [`crate::display::decode_ereal`]) or
/// a flat lane bit set (`sig R in Real`, via [`bitset_centre`]).
/// Returns `None` when no centre applies (non-dyadic plain literal,
/// empty/undecodable set): the caller falls back to instance
/// enumeration, which stays sound there.
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
            if idxs.len() == 1 {
                if let Some(decoded) = crate::display::decode_ereal(instance) {
                    if let Some(d) = decoded.get(&(idxs[0] as u32)) {
                        if let Some(v) = RealCenter::new(d.lanes.0 as i128, d.lanes.1 as i32) {
                            return Some(v);
                        }
                    }
                }
            }
            // Flat bit-set value (`sig R in Real`): decode the whole set.
            let all: Vec<u32> = idxs.iter().map(|i| *i as u32).collect();
            bitset_centre(instance.universe(), &all, mw, real_lane_ew(module, scope)?)
        }
    }
}

/// Lane `E` width companion for [`bitset_centre`] (scope-derived).
fn real_lane_ew(module: &Module, scope: &Scope) -> Option<u32> {
    real_lane_widths(module, scope).ok().map(|(_, ew)| ew)
}

/// Exact centre of a flat lane bit set (`{M$.., E$..}`).
/// `P`/`K` bits, non-lane atoms, and out-of-range positions yield `None`.
fn bitset_centre(
    universe: &alloy_kodkod_rs::universe::Universe,
    idxs: &[u32],
    mw: u32,
    ew: u32,
) -> Option<RealCenter> {
    if idxs.is_empty() {
        return None;
    }
    let mut mbits = Vec::new();
    let mut ebits = Vec::new();
    for &i in idxs {
        let atom = universe.atom(i as usize).ok()?;
        let (pre, suf) = atom.split_once('$')?;
        let pos: i64 = suf.parse().ok()?;
        match pre {
            "M" => mbits.push(pos),
            "E" => ebits.push(pos),
            _ => return None,
        }
    }
    let m = lane_twos_comp(&mbits, mw as i64)?;
    let e = lane_twos_comp(&ebits, ew as i64)?;
    RealCenter::new(m as i128, e as i32)
}

/// Two's-complement value of lane-bit positions (MSB weighs `-2^(W-1)`);
/// empty reads as 0.
fn lane_twos_comp(bits: &[i64], width: i64) -> Option<i64> {
    if width <= 0 || width >= 63 {
        return None;
    }
    let mut total: i64 = 0;
    for &v in bits {
        if v < 0 || v >= width {
            return None;
        }
        let w = if v == width - 1 {
            -(1i64.checked_shl((width - 1) as u32)?)
        } else {
            1i64.checked_shl(v as u32)?
        };
        total = total.checked_add(w)?;
    }
    Some(total)
}

/// Present a computed centre the way comprehensions must: as the
/// lane-bit set it denotes whenever that set is non-empty and
/// representable in this instance's universe, otherwise as the bare
/// computed-`Real` reading (exact zero, missing lane atoms). This keeps
/// `{x: Real | ...}` oracle answers composable with the relational
/// language (`#`, `in`, `=` against other bit sets) exactly like
/// enumerated comprehensions such as `{x: Real | one x}`.
fn centre_as_set_or_real(
    instance: &Instance,
    mw: u32,
    ew: u32,
    centre: RealCenter,
) -> QueryValue {
    if let Some(ts) = centre_atom_set(instance, mw, ew, &centre) {
        return QueryValue::Set(1, ts);
    }
    QueryValue::Real(centre)
}

/// Step a centre through the lane oracle, reporting a range exit loudly
/// (mirrors the solve path, where a missing successor is UNSAT).
fn real_oracle_centre(
    name: &str,
    up: bool,
    centre: &RealCenter,
    mw: u32,
    ew: u32,
) -> Result<RealCenter, FrontError> {
    let next = if up {
        next_up(centre, mw, ew)
    } else {
        next_down(centre, mw, ew)
    };
    match next {
        Some(v) => Ok(v),
        None => Err(FrontError::Resolve(format!(
            "`{name}` of {} [m={} e={}] leaves the lane range",
            centre.centre_short(),
            centre.m,
            centre.e,
        ))),
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
    real_oracle_centre(name, up, centre, mw, ew).map(QueryValue::Real)
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

/// Evaluate a `{ v in Real | v.realSucc[e] }` / `{ v in Real | v.realPred[e] }`
/// find-form query (either orientation) via the lane oracle.
///
/// Same atom-population limitation as [`query_real_fun`]: the successor
/// is computed from `e`'s centre instead of enumerated, then presented
/// as a lane-bit set via [`centre_as_set_or_real`]. Only the exact
/// shape qualifies — a single `Real`-typed binding whose body is one
/// `realSucc`/`realPred` call with the bound variable bare on one side
/// and a variable-free closed argument (literal or plain name) on the
/// other. Anything else returns `None` so the caller can fall back to
/// value-space enumeration.
fn query_succ_set(
    module: &Module,
    scope: &Scope,
    decls: &[Decl],
    body: &Formula,
    instance: &Instance,
) -> Result<Option<QueryValue>, FrontError> {
    if decls.len() != 1 || decls[0].names.len() != 1 {
        return Ok(None);
    }
    if !matches!(&decls[0].expr, Expr::Name(n, _) if n == "Real") {
        return Ok(None);
    }
    let var = &decls[0].names[0];
    let (name, args) = match body {
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
    // The answer is presented as a lane-bit set (see
    // `centre_as_set_or_real`), so the comprehension denotes a set just
    // like `{x: Real | one x}` does.
    let fwd = succ == (var_side == 0);
    let next = real_oracle_centre(name, fwd, &centre, mw, ew)?;
    Ok(Some(centre_as_set_or_real(instance, mw, ew, next)))
}

/// Evaluate a `{ r in Real | r.realAdd[a, b] }`-shaped arithmetic
/// find-form (`realAdd`/`realSub`/`realMul`/`realDiv`) via the
/// exact-centre oracle, presented as a lane-bit set via
/// [`centre_as_set_or_real`].
///
/// Same atom-population limitation as [`query_succ_set`]: the result is
/// computed from the closed arguments' centres instead of enumerated.
/// Only the exact shape qualifies — a single `Real`-typed binding whose
/// body is one arithmetic call with the bound variable bare in exactly
/// one of the three positions and closed arguments (literal or plain
/// name) elsewhere. Anything else returns `None` so the caller can fall
/// back to value-space enumeration.
///
/// Inexact results (e.g. inexact `realDiv`), overflows, or lane-width
/// violations also return `None` (enumeration then correctly yields no
/// solutions, mirroring the solve path's UNSAT).
fn query_arith_set(
    module: &Module,
    scope: &Scope,
    decls: &[Decl],
    body: &Formula,
    instance: &Instance,
) -> Result<Option<QueryValue>, FrontError> {
    if decls.len() != 1 || decls[0].names.len() != 1 {
        return Ok(None);
    }
    if !matches!(&decls[0].expr, Expr::Name(n, _) if n == "Real") {
        return Ok(None);
    }
    let var = &decls[0].names[0];
    let (name, args) = match body {
        Formula::Call(n, a, _) => (n.as_str(), a),
        _ => return Ok(None),
    };
    if args.len() != 3 {
        return Ok(None);
    }
    // Arg order is `[R, A, B]` (`R = A op B`).
    let kind = match name {
        "realAdd" | "realSub" | "realMul" | "realDiv" => name,
        _ => return Ok(None),
    };
    let var_side = args
        .iter()
        .position(|a| matches!(a, Expr::Name(n, _) if n == var));
    let var_side = match var_side {
        Some(i) => i,
        None => return Ok(None),
    };
    // Bound variable must occur exactly once.
    if args
        .iter()
        .filter(|a| matches!(a, Expr::Name(n, _) if n == var))
        .count()
        != 1
    {
        return Ok(None);
    }
    // Other sides must be closed over a literal or a plain,
    // non-shadowed name.
    for (i, other) in args.iter().enumerate() {
        if i == var_side {
            continue;
        }
        let closed = match other {
            Expr::RealLit(..) | Expr::ApproxRealLit(..) => true,
            Expr::Name(n, _) => n != var,
            _ => return Ok(None),
        };
        if !closed {
            return Ok(None);
        }
    }
    let (mw, ew) = real_lane_widths(module, scope)?;
    let centre_of = |expr: &Expr| real_arg_centre(module, scope, mw, expr, instance);
    // Resolve the two known sides to centres.
    let known: Vec<Option<RealCenter>> = args
        .iter()
        .enumerate()
        .map(|(i, a)| {
            if i == var_side {
                None
            } else {
                centre_of(a)
            }
        })
        .collect();
    // `known[i]` is None exactly at `var_side`; the other two must resolve.
    let mut vals: [Option<RealCenter>; 3] = [None, None, None];
    for (i, v) in known.into_iter().enumerate() {
        vals[i] = v;
    }
    if vals.iter().enumerate().any(|(i, v)| i != var_side && v.is_none()) {
        return Ok(None);
    }
    // Compute the unknown side. Conventions: R=A+B, R=A-B, R=A*B, R=A/B.
    let result = match (kind, var_side) {
        ("realAdd", 0) => real_add(&vals[1].unwrap(), &vals[2].unwrap(), 1),
        ("realAdd", 1) => real_add(&vals[0].unwrap(), &vals[2].unwrap(), -1),
        ("realAdd", 2) => real_add(&vals[0].unwrap(), &vals[1].unwrap(), -1),
        ("realSub", 0) => real_add(&vals[1].unwrap(), &vals[2].unwrap(), -1),
        ("realSub", 1) => real_add(&vals[0].unwrap(), &vals[2].unwrap(), 1),
        // B = A - R.
        ("realSub", 2) => real_add(&vals[1].unwrap(), &vals[0].unwrap(), -1),
        ("realMul", 0) => real_mul(&vals[1].unwrap(), &vals[2].unwrap()),
        ("realMul", 1) => real_div(&vals[0].unwrap(), &vals[2].unwrap()),
        ("realMul", 2) => real_div(&vals[0].unwrap(), &vals[1].unwrap()),
        ("realDiv", 0) => real_div(&vals[1].unwrap(), &vals[2].unwrap()),
        ("realDiv", 1) => real_mul(&vals[0].unwrap(), &vals[2].unwrap()),
        // B = A / R.
        ("realDiv", 2) => real_div(&vals[1].unwrap(), &vals[0].unwrap()),
        _ => return Ok(None),
    };
    let result = match result {
        Some(v) => v,
        // Inexact (e.g. inexact `realDiv`): no value satisfies.
        None => return Ok(None),
    };
    // Fire only if the centre is exactly lane-representable: the lane
    // circuits compute modulo 2^width, so an out-of-range exact result
    // would diverge from the solver. Deferring to enumeration keeps the
    // answer solver-faithful (wrapping) in that case. Exact zero keeps
    // the shared presentation (its value is unambiguous either way).
    if result.m != 0 && !centre_in_lane_range(&result, mw, ew) {
        return Ok(None);
    }
    Ok(Some(centre_as_set_or_real(instance, mw, ew, result)))
}

/// Lane-range validity of a computed centre: mantissa fits `mw` plus the
/// exponent fits the signed `ew` lanes.
fn centre_in_lane_range(c: &RealCenter, mw: u32, ew: u32) -> bool {
    if !c.is_valid(Some(mw)) || ew == 0 || ew > 30 {
        return false;
    }
    let lo = -(1i64 << (ew - 1));
    let hi = (1i64 << (ew - 1)) - 1;
    lo <= c.e as i64 && (c.e as i64) <= hi
}

/// Cap on find-form value-space enumeration: candidate counts above this
/// fail loudly with a scope-narrowing hint instead of hanging.
const FIND_ENUM_CAP: u64 = 65536;

/// A candidate value of a find-form binder in ascending numeric order.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FindVal {
    Int(i64),
    Real(RealCenter),
}

/// Exact numeric order on centres (`m*2^e`, no floats). Zeros compare
/// equal regardless of scale. Nonzero values align mantissas with checked
/// shifts; on shift overflow the shifted side provably exceeds the other
/// in magnitude (overflow needs magnitude ≥ 2^127 while mantissas fit in
/// `mw ≤ 127` bits), so its sign decides.
fn real_center_cmp(a: &RealCenter, b: &RealCenter) -> std::cmp::Ordering {
    use std::cmp::Ordering;
    match (a.m == 0, b.m == 0) {
        (true, true) => return Ordering::Equal,
        (true, false) => return if b.m > 0 { Ordering::Less } else { Ordering::Greater },
        (false, true) => return if a.m > 0 { Ordering::Greater } else { Ordering::Less },
        (false, false) => {}
    }
    if a.m.signum() != b.m.signum() {
        return a.m.cmp(&b.m);
    }
    let ell = a.e.min(b.e);
    match (
        a.m.checked_shl((a.e - ell) as u32),
        b.m.checked_shl((b.e - ell) as u32),
    ) {
        (Some(x), Some(y)) => x.cmp(&y),
        (None, Some(_)) => a.m.signum().cmp(&0),
        (Some(_), None) => 0.cmp(&b.m.signum()),
        // Unreachable: one shift is always 0 (`ell` is the minimum).
        (None, None) => Ordering::Equal,
    }
}

/// Ascending candidate values of a find-form domain. `Int`: the faithful
/// range `[-2^(W-1), 2^W - 1]` (signed integer values, not just atoms —
/// `{n in Int | n < 0}` must see negatives). `Real`: normalized centres
/// within the lane widths (odd mantissas plus zero at every scale;
/// value-equal centres dedupe to the finest scale). Counts above
/// [`FIND_ENUM_CAP`] error out.
fn find_candidates(
    _cnf: &Cnf,
    _instance: &Instance,
    is_int: bool,
    w: u32,
    mw: u32,
    ew: u32,
) -> Result<Vec<FindVal>, FrontError> {
    if is_int {
        if w == 0 || w > 62 {
            return Ok(Vec::new());
        }
        let total = 2u64.checked_pow(w).unwrap_or(u64::MAX);
        if total > FIND_ENUM_CAP {
            return Err(FrontError::Resolve(format!(
                "`in`-form enumeration over {total} integers exceeds the cap ({FIND_ENUM_CAP}); narrow the `Int` scope"
            )));
        }
        let lo = -(1i64.checked_shl(w - 1).unwrap_or(i64::MAX));
        let hi = (1i64.checked_shl(w - 1).unwrap_or(i64::MAX)) - 1;
        return Ok((lo..=hi).map(FindVal::Int).collect());
    }
    // Real: 2^(mw-1) odd mantissas x 2^ew exponents, plus zero scales.
    let e_count = 2u64.checked_pow(ew).unwrap_or(u64::MAX);
    let m_odd = if mw == 0 {
        0
    } else {
        2u64.checked_pow(mw - 1).unwrap_or(u64::MAX)
    };
    let total = m_odd.saturating_mul(e_count).saturating_add(e_count);
    if total > FIND_ENUM_CAP {
        return Err(FrontError::Resolve(format!(
            "`in`-form enumeration over ~{total} centres exceeds the cap ({FIND_ENUM_CAP}); narrow the lane widths (`for N Int`)"
        )));
    }
    let (m_lo, m_hi) = (-(1i128 << (mw.saturating_sub(1))), (1i128 << (mw.saturating_sub(1))) - 1);
    let (e_lo, e_hi) = (
        -(1i64.checked_shl(ew.saturating_sub(1)).unwrap_or(i64::MAX)),
        (1i64.checked_shl(ew.saturating_sub(1)).unwrap_or(i64::MAX)) - 1,
    );
    let mut out: Vec<(RealCenter, i32)> = Vec::new();
    let mut m = m_lo;
    while m <= m_hi {
        if m == 0 || m % 2 != 0 {
            let mut e = e_lo;
            while e <= e_hi {
                if let Some(c) = RealCenter::new(m, e as i32) {
                    out.push((c, e as i32));
                }
                if e == e_hi {
                    break;
                }
                e += 1;
            }
        }
        if m == m_hi {
            break;
        }
        m += 1;
    }
    out.sort_by(|(a, ea), (b, eb)| real_center_cmp(a, b).then(ea.cmp(eb)));
    let mut deduped: Vec<FindVal> = Vec::new();
    for (c, _) in out {
        let same = deduped.last().is_some_and(|last| match last {
            FindVal::Real(d) => real_center_cmp(d, &c) == std::cmp::Ordering::Equal,
            FindVal::Int(_) => false,
        });
        if !same {
            deduped.push(FindVal::Real(c));
        }
    }
    Ok(deduped)
}

/// Test one candidate: substitute the binder and evaluate the closed body
/// against `instance`.
///
/// The binder reads as a *value*: in set positions it becomes the exact
/// bit union (`Int` and `Real` alike, see [`find_lit`] — never decimal
/// text, whose re-parse can leave the lane); in integer `Val` positions
/// an `Int` binder becomes the integer literal itself (naive integer
/// arithmetic, not the bitmask cast). Nested redeclarations of the binder
/// stop the substitution.
///
/// Lowering/evaluation failures for a candidate mean the candidate does
/// not satisfy the body (its denotation may reference unmaterialized
/// atoms, or an operation may be undefined on it, e.g. division by zero).
/// Genuine body errors are surfaced once by the caller-side pilot instead.
#[allow(clippy::too_many_arguments)]
fn find_holds(
    module: &Module,
    scope: &Scope,
    cnf: &Cnf,
    var: &str,
    cand: &FindVal,
    body: &Formula,
    instance: &Instance,
    w: u32,
    mw: u32,
    ew: u32,
) -> Result<bool, FrontError> {
    let lit = find_lit(w, mw, ew, cand);
    let int_val = match cand {
        FindVal::Int(v) => Some(*v),
        FindVal::Real(_) => None,
    };
    let closed = subst_find_formula(body, var, &lit, int_val);
    let mut arena = AstArena::with_pool(Arc::clone(instance.pool()));
    let mut lower = Lowerer::new(module);
    let fid = match lower.lower_formula_in_scope(scope, &mut arena, &closed) {
        Ok(fid) => fid,
        Err(_) => return Ok(false),
    };
    let empty_env = Vec::new();
    match alloy_kodkod_rs::eval::Evaluator::new(instance)
        .with_bitwidth(cnf.bitwidth)
        .formula_bool(&arena, fid, &empty_env)
    {
        Ok(v) => Ok(v),
        Err(_) => Ok(false),
    }
}

/// Present one found value: integer (`Int`) or lane-bit set (`Real`,
/// sharing [`centre_as_set_or_real`]'s bit-free-zero fallback).
fn present_find_val(
    instance: &Instance,
    mw: u32,
    ew: u32,
    cand: &FindVal,
) -> Result<QueryValue, FrontError> {
    match cand {
        FindVal::Int(v) => Ok(QueryValue::Int(*v)),
        FindVal::Real(c) => Ok(centre_as_set_or_real(instance, mw, ew, *c)),
    }
}

/// Evaluate `{[any|min|max] x in D | F}`: the value-finding form.
///
/// The oracle fast path answers `Real` functional shapes directly (a
/// closed functional body determines at most one value, so every
/// selector agrees with it). Otherwise the domain's value space is
/// enumerated in ascending order ([`find_candidates`]) and each
/// candidate is tested ([`find_holds`]):
/// - `any`: first hit (short-circuits), `{}` when nothing satisfies;
/// - bare: the single hit, `{}` when nothing satisfies, an explicit
///   ambiguity error past one hit (use a selector instead);
/// - `min`/`max`: extremal hit by the sort's numeric order, `{}` when
///   nothing satisfies.
fn query_find(
    module: &Module,
    scope: &Scope,
    cnf: &Cnf,
    sel: FindSel,
    decls: &[Decl],
    body: &Formula,
    instance: &Instance,
) -> Result<QueryValue, FrontError> {
    if decls.len() != 1 || decls[0].names.len() != 1 {
        return Err(FrontError::Resolve("`in`-form takes a single binder".to_string()));
    }
    let var = decls[0].names[0].clone();
    let is_int = matches!(&decls[0].expr, Expr::IntAtom);
    let is_real = matches!(&decls[0].expr, Expr::Name(n, _) if n == "Real");
    if !is_int && !is_real {
        // Defensive: the parser restricts `in`-form domains to value sorts.
        return Err(FrontError::Resolve(
            "`{x in D | F}` needs a value sort (`Int` or `Real`)".to_string(),
        ));
    }
    if is_real {
        if let Some(qv) = query_succ_set(module, scope, decls, body, instance)? {
            return Ok(qv);
        }
        if let Some(qv) = query_arith_set(module, scope, decls, body, instance)? {
            return Ok(qv);
        }
    }
    // `Int` needs materialized bit atoms for value denotations (mirrors
    // the integer-scope guard on the int path).
    if is_int && cnf.bounds.int_bounds().count() == 0 {
        return Err(FrontError::Resolve(
            "integer set is not in scope (this model materializes no Int atoms; mention Int in the model or add `for N Int` to the scope)".to_string(),
        ));
    }
    let w = crate::ast::effective_int_count(scope);
    let (mw, ew) = real_lane_widths(module, scope)?;
    let cands = find_candidates(cnf, instance, is_int, w, mw, ew)?;
    // Pilot: lower the body once with the first candidate's denotation so
    // genuine body errors surface loudly instead of collapsing every
    // candidate to non-hits. Later per-candidate lowering failures mean
    // that candidate is unevaluable (unmaterialized atoms, undefined
    // operations like division by zero) and count as non-hits.
    if !cands.is_empty() {
        let rep = find_lit(w, mw, ew, &cands[0]);
        let probe = subst_find_formula(body, &var, &rep, None);
        let mut arena = AstArena::with_pool(Arc::clone(instance.pool()));
        let mut lower = Lowerer::new(module);
        lower.lower_formula_in_scope(scope, &mut arena, &probe)?;
    }
    let mut hits: Vec<FindVal> = Vec::new();
    for cand in &cands {
        if find_holds(module, scope, cnf, &var, cand, body, instance, w, mw, ew)? {
            match sel {
                // Ascending scan: the first hit is both `any` and `min`.
                FindSel::Any | FindSel::Min => {
                    return present_find_val(instance, mw, ew, cand)
                }
                FindSel::All if !hits.is_empty() => {
                    return Err(FrontError::Resolve(
                        "multiple values satisfy the `in`-form; refine with `any`, `min` or `max`"
                            .to_string(),
                    ));
                }
                _ => hits.push(*cand),
            }
        }
    }
    let empty = || {
        TupleSet::from_indices(instance.universe(), 1, IntSet::new())
            .map_err(|_| FrontError::Resolve("cannot build empty set".to_string()))
            .map(|ts| QueryValue::Set(1, ts))
    };
    match sel {
        FindSel::Any => empty(),
        FindSel::All => match hits.len() {
            0 => empty(),
            _ => present_find_val(instance, mw, ew, &hits[0]),
        },
        FindSel::Min => match hits.first() {
            Some(c) => present_find_val(instance, mw, ew, c),
            None => empty(),
        },
        FindSel::Max => match hits.last() {
            Some(c) => present_find_val(instance, mw, ew, c),
            None => empty(),
        },
    }
}

/// Value-reading substitution for find-form enumeration (see
/// [`find_holds`]).
/// Value-reading substitution for find-form enumeration (see
/// [`find_holds`]): a complete mirror of `fold_formula` threading
/// integer-mode substitution ([`subst_find_int`]) through every position
/// that can hold an `IntExpr` (`IntCmp`, `Maximize`/`Minimize`). All other
/// shapes recurse structurally; nested redeclarations of the binder stop
/// the substitution exactly like `fold_formula`.
fn subst_find_formula(f: &Formula, var: &str, lit: &Expr, int_val: Option<i64>) -> Formula {
    match f {
        Formula::Const(_) | Formula::Pin(..) => f.clone(),
        Formula::IntCmp(op, a, b, p) => Formula::IntCmp(
            *op,
            subst_find_int(a, var, lit, int_val),
            subst_find_int(b, var, lit, int_val),
            *p,
        ),
        Formula::Maximize(ie) => Formula::Maximize(subst_find_int(ie, var, lit, int_val)),
        Formula::Minimize(ie) => Formula::Minimize(subst_find_int(ie, var, lit, int_val)),
        Formula::MaxSome(e) => Formula::MaxSome(Box::new(subst_find_set(e, var, lit))),
        Formula::MinSome(e) => Formula::MinSome(Box::new(subst_find_set(e, var, lit))),
        Formula::OverflowCond(m, body) => {
            Formula::OverflowCond(*m, Box::new(subst_find_formula(body, var, lit, int_val)))
        }
        Formula::MaxSomeDecl(ds, body) => Formula::MaxSomeDecl(
            subst_find_decls(ds, var, lit),
            Box::new(subst_find_formula(body, var, lit, int_val)),
        ),
        Formula::Not(x) => Formula::Not(Box::new(subst_find_formula(x, var, lit, int_val))),
        Formula::And(a, b) => Formula::And(
            Box::new(subst_find_formula(a, var, lit, int_val)),
            Box::new(subst_find_formula(b, var, lit, int_val)),
        ),
        Formula::Or(a, b) => Formula::Or(
            Box::new(subst_find_formula(a, var, lit, int_val)),
            Box::new(subst_find_formula(b, var, lit, int_val)),
        ),
        Formula::Implies(a, b) => Formula::Implies(
            Box::new(subst_find_formula(a, var, lit, int_val)),
            Box::new(subst_find_formula(b, var, lit, int_val)),
        ),
        Formula::Iff(a, b) => Formula::Iff(
            Box::new(subst_find_formula(a, var, lit, int_val)),
            Box::new(subst_find_formula(b, var, lit, int_val)),
        ),
        Formula::Cmp(k, a, b, p) => Formula::Cmp(
            *k,
            subst_find_set(a, var, lit),
            subst_find_set(b, var, lit),
            *p,
        ),
        Formula::BadIn(a, p) => Formula::BadIn(Box::new(subst_find_set(a, var, lit)), *p),
        Formula::Multi(k, e, p) => {
            Formula::Multi(*k, subst_find_set(e, var, lit), *p)
        }
        Formula::Quant(k, decls, body) => {
            if decls.iter().any(|d| d.names.iter().any(|n| n == var)) {
                f.clone()
            } else {
                Formula::Quant(
                    *k,
                    subst_find_decls(decls, var, lit),
                    Box::new(subst_find_formula(body, var, lit, int_val)),
                )
            }
        }
        Formula::LetBind(binds, body) => {
            if binds.iter().any(|(n, _)| n == var) {
                f.clone()
            } else {
                Formula::LetBind(
                    binds.clone(),
                    Box::new(subst_find_formula(body, var, lit, int_val)),
                )
            }
        }
        Formula::Call(name, args, p) => Formula::Call(
            name.clone(),
            args.iter().map(|a| subst_find_set(a, var, lit)).collect(),
            *p,
        ),
        Formula::Always(inner) => Formula::Always(Box::new(subst_find_formula(inner, var, lit, int_val))),
        Formula::Eventually(inner) => {
            Formula::Eventually(Box::new(subst_find_formula(inner, var, lit, int_val)))
        }
        Formula::Until(a, b) => Formula::Until(
            Box::new(subst_find_formula(a, var, lit, int_val)),
            Box::new(subst_find_formula(b, var, lit, int_val)),
        ),
        Formula::Releases(a, b) => Formula::Releases(
            Box::new(subst_find_formula(a, var, lit, int_val)),
            Box::new(subst_find_formula(b, var, lit, int_val)),
        ),
        Formula::Before(inner) => Formula::Before(Box::new(subst_find_formula(inner, var, lit, int_val))),
        Formula::Historically(inner) => {
            Formula::Historically(Box::new(subst_find_formula(inner, var, lit, int_val)))
        }
        Formula::Once(inner) => Formula::Once(Box::new(subst_find_formula(inner, var, lit, int_val))),
        Formula::Since(a, b) => Formula::Since(
            Box::new(subst_find_formula(a, var, lit, int_val)),
            Box::new(subst_find_formula(b, var, lit, int_val)),
        ),
        Formula::Triggered(a, b) => Formula::Triggered(
            Box::new(subst_find_formula(a, var, lit, int_val)),
            Box::new(subst_find_formula(b, var, lit, int_val)),
        ),
        Formula::Keeping(inner) => {
            Formula::Keeping(Box::new(subst_find_formula(inner, var, lit, int_val)))
        }
        Formula::Goal(inner) => Formula::Goal(Box::new(subst_find_formula(inner, var, lit, int_val))),
        Formula::Restore(inner) => {
            Formula::Restore(Box::new(subst_find_formula(inner, var, lit, int_val)))
        }
        Formula::Initially(inner) => {
            Formula::Initially(Box::new(subst_find_formula(inner, var, lit, int_val)))
        }
        Formula::Regularly(inner) => {
            Formula::Regularly(Box::new(subst_find_formula(inner, var, lit, int_val)))
        }
        Formula::Consistently(inner) => {
            Formula::Consistently(Box::new(subst_find_formula(inner, var, lit, int_val)))
        }
    }
}

/// Declaration substitution for [`subst_find_formula`].
fn subst_find_decls(ds: &[Decl], var: &str, lit: &Expr) -> Vec<Decl> {
    ds.iter()
        .map(|d| crate::ast::Decl {
            disj: d.disj,
            names: d.names.clone(),
            expr: subst_find_set(&d.expr, var, lit),
            pos: d.pos,
            is_var: d.is_var,
        })
        .collect()
}

/// Set-position substitution: the binder becomes its denotation
/// (singleton atom / exact decimal); nested redeclarations stop it via
/// the shared traversal.
fn subst_find_set(e: &Expr, var: &str, lit: &Expr) -> Expr {
    crate::lower::fold_expr(e, var, &crate::lower::NameTarget::Replace(lit))
}

/// Integer-position substitution: an `Int` binder reads as the integer
/// itself; anything else substitutes in set positions underneath.
fn subst_find_int(i: &IntExpr, var: &str, lit: &Expr, int_val: Option<i64>) -> IntExpr {
    use crate::ast::IntExpr as IE;
    match i {
        IE::Val(e, p) => match e.as_ref() {
            Expr::Name(n, _) if n == var => match int_val {
                Some(v) => IE::Lit(v, *p),
                // A `Real` binder under an integer operator is nonsense;
                // leave it for lowering to reject loudly.
                None => IE::Val(Box::new(subst_find_set(e, var, lit)), *p),
            },
            _ => IE::Val(Box::new(subst_find_set(e, var, lit)), *p),
        },
        IE::Card(e, p) => IE::Card(Box::new(subst_find_set(e, var, lit)), *p),
        IE::SumOf(e, p) => IE::SumOf(Box::new(subst_find_set(e, var, lit)), *p),
        IE::BitsVal(e, p) => IE::BitsVal(Box::new(subst_find_set(e, var, lit)), *p),
        IE::Sum(decls, body, p) => {
            if decls.iter().any(|d| d.names.iter().any(|n| n == var)) {
                i.clone()
            } else {
                IE::Sum(decls.clone(), Box::new(subst_find_int(body, var, lit, int_val)), *p)
            }
        }
        IE::Bin(op, a, b) => IE::Bin(
            *op,
            Box::new(subst_find_int(a, var, lit, int_val)),
            Box::new(subst_find_int(b, var, lit, int_val)),
        ),
        IE::Widen(op, a, b) => IE::Widen(
            *op,
            Box::new(subst_find_int(a, var, lit, int_val)),
            Box::new(subst_find_int(b, var, lit, int_val)),
        ),
        IE::Lit(..) => i.clone(),
    }
}

/// The binder's denotation for substitution: exact bit unions for both
/// sorts (`Int` bit positions / `Real` lanes).
///
/// Values never go through decimal text: an `e > 0` centre expands to a
/// full integer on re-parse and can leave the mantissa lane even though
/// the `(m, e)` pair itself is lane-valid. Bit unions are exact by
/// construction (same two's-complement rule as `centre_lane_indices` and
/// `lower_expr_bits`); the bit-free exact zero becomes the empty set.
fn find_lit(w: u32, mw: u32, ew: u32, cand: &FindVal) -> Expr {
    match cand {
        FindVal::Int(v) => {
            let names = int_bit_names(*v, w).unwrap_or_default();
            let mut it = names.into_iter().map(|n| Expr::Name(n, 0));
            match it.next() {
                Some(first) => it.fold(first, |acc, e| {
                    Expr::Bin(BinOp::Union, Box::new(acc), Box::new(e))
                }),
                None => Expr::None_,
            }
        }
        FindVal::Real(c) => {
            let mut names: Vec<String> = Vec::new();
            for (prefix, value, width) in [("M", c.m as i64, mw), ("E", c.e as i64, ew)] {
                names.extend(lane_bit_names(prefix, value, width).unwrap_or_default());
            }
            let mut it = names.into_iter().map(|n| Expr::Name(n, 0));
            match it.next() {
                Some(first) => it.fold(first, |acc, e| {
                    Expr::Bin(BinOp::Union, Box::new(acc), Box::new(e))
                }),
                None => Expr::None_,
            }
        }
    }
}

/// Int bit-position names holding `value` (`{i < W : bit i}`, mirroring
/// `lower_expr_bits`; `None` on degenerate widths).
fn int_bit_names(value: i64, w: u32) -> Option<Vec<String>> {
    if w == 0 || w > 62 {
        return None;
    }
    let u = (value as u64) & ((1u64 << w) - 1);
    let mut out = Vec::new();
    for i in 0..w {
        if (u >> i) & 1 == 1 {
            out.push(i.to_string());
        }
    }
    Some(out)
}

/// Lane-bit atom names holding `value` under two's-complement `width`
/// (mirrors `centre_lane_indices`; `None` on degenerate widths).
fn lane_bit_names(prefix: &str, value: i64, width: u32) -> Option<Vec<String>> {
    if width == 0 || width > 30 {
        return None;
    }
    let u = (value as u64) & ((1u64 << width) - 1);
    let mut out = Vec::new();
    for i in 0..width {
        if (u >> i) & 1 == 1 {
            out.push(format!("{prefix}${i}"));
        }
    }
    Some(out)
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
    // Pure literal arithmetic displays faithful values (`7 + 7` reads
    // like the bare `14`, i.e. `-2` under W=4). Trees holding `#`/`sum`
    // report genuine counts and stay raw. (Literals themselves were
    // already folded at lowering; this maps computed results.)
    let v = if ie.has_count() {
        v
    } else {
        crate::types::faithful_int(v, crate::ast::effective_int_count(scope))
    };
    Ok(QueryValue::Int(v))
}
