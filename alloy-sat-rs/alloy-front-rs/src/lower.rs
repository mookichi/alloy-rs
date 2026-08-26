//! Lowers the frontend AST to kodkod-rs (AstArena + Bounds) and solves.

use crate::ast::*;
use crate::bounds::{self, Resolved};
use crate::FrontError;
use alloy_kodkod_rs::ast::{
    self as kk, CastToIntOp, ExprCompOp, ExprId, FormulaId, IntId, Multiplicity, Quantifier,
};
use alloy_kodkod_rs::bounds::Bounds;
use alloy_kodkod_rs::relation::{RelationId, RelationPool};
use std::collections::HashMap;
use std::sync::Arc;

pub struct LoweredProblem {
    pub arena: kk::AstArena,
    pub bounds: Bounds,
    pub formula: FormulaId,
    pub bitwidth: u32,
}

pub struct Lowerer<'m> {
    module: &'m Module,
}

type LResult<T> = Result<T, FrontError>;

/// Variable environment: name -> (kodkod var, arity).
type Env = Vec<(String, kk::VarId, u32)>;

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
        let res = bounds::resolve(self.module, &cmd.scope).map_err(FrontError::Resolve)?;
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
        // global facts collected first so field constraints can join them
        let mut parts: Vec<FormulaId> = Vec::new();

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
                        // type_tuples already yields deterministic rows; reuse it
                        let tuples_list: Vec<Vec<String>> = self.type_tuples(&d.expr, &res)?;
                        if let Some(c) = field_mult_constraint(
                            &mut arena,
                            &res,
                            &mut b,
                            fa,
                            d,
                            owner,
                            &tuples_list,
                        )? {
                            parts.push(c);
                        }
                    }
                }
            }
        }
        // bind sig bounds AFTER field bounds so pool interning is consistent
        bounds::bind_sigs(self.module, &res, &pool, &mut arena, &mut b, &cmd.scope)
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

        // int atom exact bounds
        let half = 1i64 << (res.bitwidth - 1);
        for v in (-half)..half {
            let name = v.to_string();
            let idx = res
                .universe
                .index(&name)
                .map_err(|e| FrontError::Resolve(e.to_string()))?;
            let mut ts = alloy_kodkod_rs::tupleset::TupleSet::new(&res.universe, 1)
                .map_err(|e| FrontError::Resolve(e.to_string()))?;
            ts.insert_index(idx as i64);
            b.bound_exactly_int(v, &ts)
                .map_err(|e| FrontError::Resolve(e.to_string()))?;
        }

        // Insert ordering relations into rels so name resolution can find them
        for (alias, &(first_rel, next_rel)) in &ordering_info {
            rels.insert(format!("{alias}/first"), first_rel);
            rels.insert(format!("{alias}/next"), next_rel);
        }

        let ctx = Ctx {
            module: self.module,
            res: &res,
            rels: &rels,
            field_arity: &field_arity,
            ordering_info: &ordering_info,
            depth: std::cell::Cell::new(0),
        };

        // global facts
        for (_, f) in &self.module.facts {
            parts.push(ctx.lower_formula(&mut arena, f, &mut Vec::new())?);
        }
        // sig facts: all this: S | fact
        for sd in &self.module.sigs {
            if let Some(f) = &sd.fact {
                for owner in &sd.names {
                    let fid = ctx.lower_sig_fact(&mut arena, f, owner)?;
                    parts.push(fid);
                }
            }
        }
        // sig `in` constraints: sig A in B  =>  A in B (subset)
        for sd in &self.module.sigs {
            if sd.rel == crate::ast::SigRel::In {
                if let Some(parent_name) = &sd.extends {
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
        // command body
        let body_name = match &cmd.kind {
            CommandKind::Run(n) => n.clone(),
            CommandKind::Check(n) => n.clone(),
        };
        match body_name {
            None => parts.push(arena.bool_formula(true)),
            Some(name) => {
                let para = self
                    .module
                    .paras
                    .iter()
                    .find(|p| p.name == name)
                    .ok_or_else(|| {
                        FrontError::Resolve(format!("command references unknown '{name}'"))
                    })?;
                if !para.params.is_empty() {
                    return self.unsup(format!("parametrized '{name}' in command"));
                }
                let bf = ctx.lower_formula(&mut arena, &para.body, &mut Vec::new())?;
                // `check F` searches for a counterexample to F
                match cmd.kind {
                    CommandKind::Check(_) => parts.push(arena.not(bf)),
                    CommandKind::Run(_) => parts.push(bf),
                }
            }
        }

        let formula = arena.and(&parts);
        Ok(LoweredProblem {
            arena,
            bounds: b,
            formula,
            bitwidth: res.bitwidth,
        })
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
                if res.sigs.contains_key(n) || n == "univ" || n == "int" || n == "Int" {
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
                } else if n == "int" || n == "Int" {
                    // Int atoms: named by their numeric value
                    let half = 1i64 << (res.bitwidth - 1);
                    ((-half)..half).map(|v| v.to_string()).collect()
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
            Expr::IntAtom => {
                // Int atoms: named by their numeric value
                let half = 1i64 << (res.bitwidth - 1);
                let int_atoms: Vec<Vec<String>> =
                    ((-half)..half).map(|v| vec![v.to_string()]).collect();
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

/// Shared lowering context over resolved names.
struct Ctx<'a> {
    module: &'a Module,
    #[allow(dead_code)]
    res: &'a Resolved,
    rels: &'a HashMap<String, RelationId>,
    #[allow(dead_code)]
    field_arity: &'a HashMap<String, u32>,
    ordering_info: &'a HashMap<String, (RelationId, RelationId)>,
    depth: std::cell::Cell<u32>,
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

    /// Try to resolve an ordering builtin predicate call.
    /// Returns Some(formula) if the name matches an ordering builtin predicate.
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
        let mut env: Env = vec![("this".into(), var, 1)];
        let body = self.lower_formula(arena, f, &mut env)?;
        Ok(arena.quantified(Quantifier::All, ds, body))
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
            Expr::IntAtom => (arena.constant(kk::ConstantExpr::Ints), 1),
            Expr::Name(n, pos) => {
                if let Some((_, v, a)) = env.iter().rev().find(|(nm, _, _)| nm == n) {
                    let (v, a) = (*v, *a);
                    return Ok((arena.expr_variable(v), a));
                }
                if let Some(r) = self.lookup_rel(n) {
                    let ar = arena.relation_arity(r);
                    return Ok((arena.expr_relation(r), ar));
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
                    return self.lower_expr(arena, &body, env);
                }
                return Err(FrontError::Parse {
                    pos: *pos,
                    msg: format!("unresolved name '{n}'"),
                });
            }
            Expr::Bin(op, a, b) => {
                let (ea, aa) = self.lower_expr(arena, a, env)?;
                let (eb, ab) = self.lower_expr(arena, b, env)?;
                let id = (match op {
                    BinOp::Union => arena.binary_expr(kk::BinaryOp::Union, ea, eb),
                    BinOp::Intersect => arena.binary_expr(kk::BinaryOp::Intersection, ea, eb),
                    BinOp::Difference => arena.binary_expr(kk::BinaryOp::Difference, ea, eb),
                    BinOp::Override => arena.binary_expr(kk::BinaryOp::Override, ea, eb),
                    BinOp::Product => arena.binary_expr(kk::BinaryOp::Product, ea, eb),
                    BinOp::Join => {
                        if aa + ab < 2 {
                            return Err(FrontError::Resolve(format!(
                                "join arity too small ({aa}.{ab})"
                            )));
                        }
                        arena.binary_expr(kk::BinaryOp::Join, ea, eb)
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
                let (mut cur, mut car) = self.lower_expr(arena, base, env)?;
                for a in args {
                    let (ai, aa) = self.lower_expr(arena, a, env)?;
                    if car + aa < 2 {
                        return Err(FrontError::Resolve("bracket join arity".into()));
                    }
                    cur = arena
                        .binary_expr(kk::BinaryOp::Join, cur, ai)
                        .map_err(|e| FrontError::Resolve(e.to_string()))?;
                    car -= 1;
                }
                (cur, car)
            }
            Expr::ArrowMult(..) | Expr::LeadMult(..) => {
                return self.unsup("multiplicity outside field declaration")
            }
            Expr::Call(name, args, _) => {
                // Check ordering builtins first
                if let Some(result) = self.try_ordering_expr(arena, name, args, env)? {
                    return Ok(result);
                }
                if args.is_empty() {
                    if let Some(r) = self.lookup_rel(name) {
                        let ar = arena.relation_arity(r);
                        return Ok((arena.expr_relation(r), ar));
                    }
                }
                let para = self
                    .module
                    .paras
                    .iter()
                    .find(|p| p.name == *name && p.is_fun)
                    .ok_or_else(|| FrontError::Resolve(format!("unknown function '{name}'")))?;
                if para.params.len() != args.len() {
                    return Err(FrontError::Resolve(format!(
                        "'{name}' expects {} args, got {}",
                        para.params.len(),
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
                for (pd, arg) in para.params.iter().zip(args.iter()) {
                    for pn in &pd.names {
                        body = replace_var_expr(&body, pn, arg);
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
        for d in decls {
            let (dom, _da) = self.lower_expr(arena, &d.expr, env)?;
            for n in &d.names {
                let v = arena.variable(n);
                let da = arena.decl(v, Multiplicity::One, dom).unwrap();
                list.push(da);
                env.push((n.clone(), v, arena.variable_arity(v)));
                pushed += 1;
            }
        }
        Ok((arena.add_decls(list), pushed))
    }

    fn lower_int(&self, arena: &mut kk::AstArena, ie: &IntExpr, env: &mut Env) -> LResult<IntId> {
        Ok(match ie {
            IntExpr::Lit(v, _) => arena.int_constant(*v),
            IntExpr::Card(e, _) => {
                let (ee, _) = self.lower_expr(arena, e, env)?;
                arena.cast_to_int(CastToIntOp::Cardinality, ee).unwrap()
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
                };
                arena.binary_int(kop, ia, ib)
            }
        })
    }

    fn lower_formula(
        &self,
        arena: &mut kk::AstArena,
        f: &Formula,
        env: &mut Env,
    ) -> LResult<FormulaId> {
        Ok(match f {
            Formula::Const(v) => arena.bool_formula(*v),
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
                // Check ordering builtins first
                if let Some(f) = self.try_ordering_pred(arena, name, args, env)? {
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
                if para.params.len() != args.len() {
                    return Err(FrontError::Resolve(format!(
                        "'{name}' expects {} args, got {}",
                        para.params.len(),
                        args.len()
                    )));
                }
                let d = self.depth.get();
                if d > 64 {
                    return Err(FrontError::Resolve("call recursion too deep".into()));
                }
                self.depth.set(d + 1);
                let mut body = para.body.clone();
                for (pd, arg) in para.params.iter().zip(args.iter()) {
                    for pn in &pd.names {
                        body = replace_var_formula(&body, pn, arg);
                    }
                }
                let out = self.lower_formula(arena, &body, env)?;
                self.depth.set(d);
                out
            }
            Formula::LetBind(binds, body) => {
                let mut added = 0usize;
                for (name, e) in binds {
                    let (_ee, ea) = self.lower_expr(arena, e, env)?;
                    let v = arena.variable(name);
                    env.push((name.clone(), v, ea));
                    added += 1;
                    let _ = v;
                }
                let bf = self.lower_formula(arena, body, env)?;
                for _ in 0..added {
                    env.pop();
                }
                bf
            }
            Formula::Cmp(kind, l, r, _) => {
                let (el, al) = self.lower_expr(arena, l, env)?;
                let (er, ar) = self.lower_expr(arena, r, env)?;
                if al != ar {
                    return Err(FrontError::Resolve(format!(
                        "comparison arity mismatch: {al} vs {ar}"
                    )));
                }
                let base = match kind {
                    CmpKind::Eq | CmpKind::Neq => {
                        arena.comparison(ExprCompOp::Equals, el, er).unwrap()
                    }
                    CmpKind::In | CmpKind::NotIn => {
                        arena.comparison(ExprCompOp::Subset, el, er).unwrap()
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
                let f = self.lower_formula(arena, inner, env)?;
                arena.temporal_unary(kk::TemporalFormulaOp::Goal, f)
            }
            Formula::Restore(inner) => {
                let f = self.lower_formula(arena, inner, env)?;
                arena.temporal_unary(kk::TemporalFormulaOp::Restore, f)
            }
            Formula::Initially(inner) => {
                let f = self.lower_formula(arena, inner, env)?;
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

/// Textual variable renaming used by lone/one desugaring; stops at
/// shadowing redeclarations of `from`.
fn subst_formula(f: &Formula, from: &str, to: &str) -> Formula {
    match f {
        Formula::Const(v) => Formula::Const(*v),
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
        Expr::Name(..) | Expr::Univ | Expr::None_ | Expr::Iden | Expr::IntAtom => e.clone(),
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
    }
}

/// Generates the multiplicity constraint formula for one field declaration,
/// or None when it carries no markers. Exact helper relations give every
/// quantified variable its true domain.
#[allow(clippy::too_many_arguments)]
fn field_mult_constraint(
    arena: &mut kk::AstArena,
    res: &Resolved,
    b: &mut Bounds,
    frel: RelationId,
    d: &Decl,
    owner: &str,
    tuples: &[Vec<String>],
) -> LResult<Option<FormulaId>> {
    // markers: (column index, mult)
    fn walk(
        e: &Expr,
        offset: usize,
        markers: &mut Vec<(usize, crate::ast::Mult3)>,
        total_cols: &mut usize,
    ) -> LResult<()> {
        match e {
            Expr::LeadMult(m, inner) => {
                walk(inner, offset, markers, total_cols)?;
                markers.push((0, *m));
                Ok(())
            }
            Expr::ArrowMult(m, inner) => {
                walk(inner, offset, markers, total_cols)?;
                markers.push((offset, *m));
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
            Expr::Name(..) | Expr::Univ | Expr::IntAtom => {
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
    let _ = res;
    fn res_static() {}

    let mut markers: Vec<(usize, crate::ast::Mult3)> = Vec::new();
    let mut ncols = 0usize;
    walk(&d.expr, 0, &mut markers, &mut ncols)?;
    if markers.is_empty() {
        return Ok(None);
    }
    let n = ncols + 1; // owner column included

    // per-column atom domains from actual upper-bound tuples
    let mut col_atoms: Vec<Vec<String>> = vec![Vec::new(); n];
    col_atoms[0] = res.atoms_of(owner);
    for row in tuples {
        for (k, a) in row.iter().enumerate().take(n) {
            if !col_atoms[k].contains(a) {
                col_atoms[k].push(a.clone());
            }
        }
    }

    // exact helper domain relations
    let mut dom_rel: Vec<RelationId> = Vec::with_capacity(n);
    for (k, atoms) in col_atoms.iter().enumerate() {
        let name = format!("%dom%{}.{}", std::ptr::from_ref(d) as usize, k);
        let r = arena.relation(&name, 1);
        let mut lo = alloy_kodkod_rs::tupleset::TupleSet::new(&res.universe, 1)
            .map_err(|e| FrontError::Resolve(e.to_string()))?;
        let up = bounds::ts_of(res, atoms).map_err(FrontError::Resolve)?;
        b.bound(r, &lo, &up)
            .map_err(|e| FrontError::Resolve(e.to_string()))?;
        let _ = &mut lo;
        dom_rel.push(r);
    }

    let mut out: Vec<FormulaId> = Vec::new();
    for (col, m) in markers {
        let mult = match m {
            crate::ast::Mult3::Some => Multiplicity::Some,
            crate::ast::Mult3::Lone => Multiplicity::Lone,
            crate::ast::Mult3::One => Multiplicity::One,
        };
        let frec = arena.expr_relation(frel);
        if col == n - 1 {
            // all c0: D0, ..., c_{n-2}: D_{n-2} | ((c0.f).c1...). M D_{n-1}
            let mut ds: Vec<kk::Decl> = Vec::new();
            let mut vars: Vec<kk::VarId> = Vec::new();
            for (j, dr) in dom_rel.iter().enumerate().take(n - 1) {
                let v = arena.variable(&format!("%mc{j}%{}", std::ptr::from_ref(d) as usize));
                let dv = arena.expr_relation(*dr);
                let dd = arena.decl(v, Multiplicity::One, dv).unwrap();
                ds.push(dd);
                vars.push(v);
            }
            let v0e = arena.expr_variable(vars[0]);
            let mut g = arena
                .binary_expr(kk::BinaryOp::Join, v0e, frec)
                .map_err(|e| FrontError::Resolve(e.to_string()))?;
            for vj_expr in vars.iter().take(n - 1).skip(1) {
                let vj = arena.expr_variable(*vj_expr);
                g = arena
                    .binary_expr(kk::BinaryOp::Join, g, vj)
                    .map_err(|e| FrontError::Resolve(e.to_string()))?;
            }
            let mf = arena.multiplicity_formula(mult, g).unwrap();
            let dsid = arena.add_decls(ds);
            out.push(arena.quantified(Quantifier::All, dsid, mf));
        } else if col == 0 && n == 2 {
            // all c1: D1 | c1.~f M D0
            let v = arena.variable(&format!("%mlead%{}", std::ptr::from_ref(d) as usize));
            let dv = arena.expr_relation(dom_rel[1]);
            let dd = arena.decl(v, Multiplicity::One, dv).unwrap();
            let tr = arena.unary_expr(kk::UnaryExprOp::Transpose, frec).unwrap();
            let ve = arena.expr_variable(v);
            let g = arena
                .binary_expr(kk::BinaryOp::Join, ve, tr)
                .map_err(|e| FrontError::Resolve(e.to_string()))?;
            let mf = arena.multiplicity_formula(mult, g).unwrap();
            let dsid = arena.add_decls(vec![dd]);
            out.push(arena.quantified(Quantifier::All, dsid, mf));
        } else {
            return Err(FrontError::Unsupported(format!(
                "multiplicity on internal column {col} of arity-{n} field"
            )));
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
        Expr::Name(..) | Expr::Univ | Expr::None_ | Expr::Iden | Expr::IntAtom => e.clone(),
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
        Formula::Not(x) => Formula::Not(Box::new(replace_var_formula(x, from, to))),
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
