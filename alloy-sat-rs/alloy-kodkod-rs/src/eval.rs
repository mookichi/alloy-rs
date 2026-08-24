use std::collections::BTreeSet;

use crate::ast::{
    AstArena, BinaryOp, ConstantExpr, ExprId, FormulaId, IntBinOp, IntCompOp, IntId, IntNode,
    Multiplicity, Quantifier, VarId,
};
use crate::instance::Instance;
use crate::intset::{Int, IntSet};
use crate::tupleset::TupleSet;

#[derive(Debug, thiserror::Error)]
pub enum EvalError {
    #[error("relation {0} not present in instance")]
    UnboundRelation(u32),
    #[error("no instance bound for integer {0}")]
    UnboundInteger(i64),
    #[error("variable is unbound in the environment")]
    UnboundVariable,
    #[error("integer division by zero")]
    DivideByZero,
    #[error("matrix op failed: {0}")]
    Matrix(#[from] crate::bmatrix::MatrixError),
}

type Env = Vec<(VarId, Vec<u32>)>;

pub struct Evaluator<'a> {
    pub instance: &'a Instance,
}

impl<'a> Evaluator<'a> {
    pub fn new(instance: &'a Instance) -> Evaluator<'a> {
        Evaluator { instance }
    }

    fn univ(&self) -> u32 {
        self.instance.universe().size() as u32
    }

    fn dims(&self, arity: u32) -> Result<TupleSet, EvalError> {
        TupleSet::new(self.instance.universe(), arity).map_err(|_| EvalError::UnboundVariable)
    }

    pub fn expr_set(&self, arena: &AstArena, e: ExprId, env: &Env) -> Result<TupleSet, EvalError> {
        match arena.expr(e).clone() {
            crate::ast::ExprNode::Relation(r) => self
                .instance
                .tuples(r)
                .cloned()
                .ok_or(EvalError::UnboundRelation(r.0)),
            crate::ast::ExprNode::Variable(v) => {
                let (_, vec) = env
                    .iter()
                    .rev()
                    .find(|(id, _)| *id == v)
                    .ok_or(EvalError::UnboundVariable)?;
                let mut ts = self.dims(vec.len() as u32)?;
                let flat = flat_of(&ts, vec)?;
                ts.insert_index(flat);
                Ok(ts)
            }
            crate::ast::ExprNode::Constant(c) => match c {
                ConstantExpr::Univ => {
                    let mut out = IntSet::new();
                    let n = self.univ() as usize;
                    for i in 0..n {
                        out.insert(i as Int);
                    }
                    TupleSet::from_indices(self.instance.universe(), 1, out)
                        .map_err(|_| EvalError::UnboundVariable)
                }
                ConstantExpr::Empty => Ok(self.dims(1)?),
                ConstantExpr::Ints => Err(EvalError::UnboundInteger(i64::MIN)),
                ConstantExpr::Iden => {
                    let mut ts = self.dims(2)?;
                    let n = self.univ() as usize;
                    for i in 0..n {
                        ts.insert_index((i * n + i) as Int);
                    }
                    Ok(ts)
                }
            },
            crate::ast::ExprNode::Unary { op, child } => {
                let m = self.expr_set(arena, child, env)?;
                match op {
                    crate::ast::UnaryExprOp::Transpose => transpose(&m),
                    crate::ast::UnaryExprOp::Closure => closure(&m, false),
                    crate::ast::UnaryExprOp::ReflexiveClosure => closure(&m, true),
                }
            }
            crate::ast::ExprNode::Temporal { .. } => Err(EvalError::UnboundInteger(-1)),
            crate::ast::ExprNode::Binary { op, left, right } => {
                let a = self.expr_set(arena, left, env)?;
                let b = self.expr_set(arena, right, env)?;
                match op {
                    BinaryOp::Union => union(&a, &b),
                    BinaryOp::Intersection => intersection(&a, &b),
                    BinaryOp::Difference => difference(&a, &b),
                    BinaryOp::Override => override_sets(&a, &b),
                    BinaryOp::Product => cross(&a, &b),
                    BinaryOp::Join => join(&a, &b),
                }
            }
            crate::ast::ExprNode::Nary { op, children } => {
                let mut acc = self.expr_set(arena, children[0], env)?;
                for &c in &children[1..] {
                    let m = self.expr_set(arena, c, env)?;
                    acc = match op {
                        BinaryOp::Union => union(&acc, &m)?,
                        BinaryOp::Intersection => intersection(&acc, &m)?,
                        BinaryOp::Difference => difference(&acc, &m)?,
                        BinaryOp::Override => override_sets(&acc, &m)?,
                        BinaryOp::Product => cross(&acc, &m)?,
                        BinaryOp::Join => join(&acc, &m)?,
                    };
                }
                Ok(acc)
            }
            crate::ast::ExprNode::If { cond, then, els } => {
                let c = self.formula_bool(arena, cond, env)?;
                if c {
                    self.expr_set(arena, then, env)
                } else {
                    self.expr_set(arena, els, env)
                }
            }
            crate::ast::ExprNode::Project { .. } => Err(EvalError::UnboundInteger(-2)),
            crate::ast::ExprNode::Comprehension { decls, body } => {
                let decl_list = arena.decls(decls).to_vec();
                let mut collected: BTreeSet<Vec<u32>> = BTreeSet::new();
                self.iter_decls(arena, &decl_list, env, &mut |ev, binding| {
                    if ev.formula_bool(arena, body, &binding)? {
                        let vec: Vec<u32> = binding
                            .iter()
                            .flat_map(|(_, v)| v.iter().copied())
                            .collect();
                        collected.insert(vec);
                    }
                    Ok(())
                })?;
                let arity = collected.iter().next().map(|v| v.len()).unwrap_or_else(|| {
                    decl_list
                        .iter()
                        .map(|d| arena.variable_arity(d.variable) as usize)
                        .sum()
                });
                let mut ts = self.dims(arity as u32)?;
                for vec in collected {
                    let flat = flat_of(&ts, &vec)?;
                    ts.insert_index(flat);
                }
                Ok(ts)
            }
            crate::ast::ExprNode::FromInt(i) => {
                let v = int_const_of(arena, i)?;
                self.instance
                    .int_tuple(v)
                    .cloned()
                    .ok_or(EvalError::UnboundInteger(v))
            }
        }
    }

    #[allow(clippy::too_many_lines)]
    pub fn formula_bool(
        &self,
        arena: &AstArena,
        f: FormulaId,
        env: &Env,
    ) -> Result<bool, EvalError> {
        match arena.formula(f).clone() {
            crate::ast::FormulaNode::Constant(v) => Ok(v),
            crate::ast::FormulaNode::Not(child) => Ok(!self.formula_bool(arena, child, env)?),
            crate::ast::FormulaNode::Nary { op, children } => {
                let mut vals = Vec::with_capacity(children.len());
                for &c in &children {
                    vals.push(self.formula_bool(arena, c, env)?);
                }
                Ok(match op {
                    crate::ast::FormulaBinOp::And => vals.iter().all(|&v| v),
                    crate::ast::FormulaBinOp::Or => vals.iter().any(|&v| v),
                })
            }
            crate::ast::FormulaNode::Comparison { op, left, right } => {
                let a = self.expr_set(arena, left, env)?;
                let b = self.expr_set(arena, right, env)?;
                Ok(match op {
                    crate::ast::ExprCompOp::Equals => a == b,
                    crate::ast::ExprCompOp::Subset => a.covers(&b),
                })
            }
            crate::ast::FormulaNode::IntComparison { op, left, right } => {
                let l = self.int_value(arena, left, env)?;
                let r = self.int_value(arena, right, env)?;
                Ok(match op {
                    IntCompOp::Eq => l == r,
                    IntCompOp::Neq => l != r,
                    IntCompOp::Lt => l < r,
                    IntCompOp::Lte => l <= r,
                    IntCompOp::Gt => l > r,
                    IntCompOp::Gte => l >= r,
                })
            }
            crate::ast::FormulaNode::Quantified { quant, decls, body } => {
                let decl_list = arena.decls(decls).to_vec();
                let mut results = Vec::new();
                self.iter_decls(arena, &decl_list, env, &mut |ev, binding| {
                    results.push(ev.formula_bool(arena, body, &binding)?);
                    Ok(())
                })?;
                Ok(match quant {
                    Quantifier::All => results.iter().all(|&v| v),
                    Quantifier::Some => results.iter().any(|&v| v),
                })
            }
            crate::ast::FormulaNode::Multiplicity { mult, expr } => {
                let m = self.expr_set(arena, expr, env)?;
                Ok(match mult {
                    Multiplicity::Some => !m.is_empty(),
                    Multiplicity::One => m.len() == 1,
                    Multiplicity::Lone => m.len() <= 1,
                    Multiplicity::Set => true,
                })
            }
            crate::ast::FormulaNode::TemporalUnary { .. }
            | crate::ast::FormulaNode::TemporalBinary { .. } => Err(EvalError::UnboundInteger(-1)),
        }
    }

    pub fn int_value(&self, arena: &AstArena, i: IntId, env: &Env) -> Result<i64, EvalError> {
        use crate::ast::CastToIntOp;
        let node = arena.int(i).clone();
        match node {
            IntNode::Constant(v) => Ok(v),
            IntNode::OfExpr { op, expr } => {
                let m = self.expr_set(arena, expr, env)?;
                match op {
                    CastToIntOp::Cardinality => Ok(m.len() as i64),
                    CastToIntOp::Sum => {
                        let mut total = 0i64;
                        for (val, ts) in self.instance.int_tuples() {
                            for idx in ts.index_view().iter() {
                                if m.contains_index(idx) {
                                    total += val;
                                }
                            }
                        }
                        Ok(total)
                    }
                }
            }
            IntNode::Binary { op, left, right } => {
                let l = self.int_value(arena, left, env)?;
                let r = self.int_value(arena, right, env)?;
                Ok(match op {
                    IntBinOp::Plus => l.wrapping_add(r),
                    IntBinOp::Minus => l.wrapping_sub(r),
                    IntBinOp::Times => l.wrapping_mul(r),
                    IntBinOp::Divide => {
                        if r == 0 {
                            return Err(EvalError::DivideByZero);
                        }
                        l.wrapping_div(r)
                    }
                    IntBinOp::Modulo => {
                        if r == 0 {
                            return Err(EvalError::DivideByZero);
                        }
                        l.wrapping_rem(r)
                    }
                    IntBinOp::And => l & r,
                    IntBinOp::Or => l | r,
                    IntBinOp::Xor => l ^ r,
                    IntBinOp::Shl => l << (r as u32 % 64),
                    IntBinOp::Shr => ((l as u64) >> (r as u32 % 64)) as i64,
                })
            }
            IntNode::If { cond, then, els } => {
                if self.formula_bool(arena, cond, env)? {
                    self.int_value(arena, then, env)
                } else {
                    self.int_value(arena, els, env)
                }
            }
            IntNode::Sum { decls, body } => {
                let decl_list = arena.decls(decls).to_vec();
                let mut total = 0i64;
                self.iter_decls(arena, &decl_list, env, &mut |ev, binding| {
                    total += ev.int_value(arena, body, &binding)?;
                    Ok(())
                })?;
                Ok(total)
            }
        }
    }

    fn iter_decls(
        &self,
        arena: &AstArena,
        decls: &[crate::ast::Decl],
        env: &Env,
        visit: &mut dyn FnMut(&Evaluator<'a>, Env) -> Result<(), EvalError>,
    ) -> Result<(), EvalError> {
        fn rec<'b>(
            ev: &Evaluator<'b>,
            domains: &[TupleSet],
            vars: &[VarId],
            env: &mut Env,
            visit: &mut dyn FnMut(&Evaluator<'b>, Env) -> Result<(), EvalError>,
            depth: usize,
        ) -> Result<(), EvalError> {
            if depth == domains.len() {
                return visit(ev, env.clone());
            }
            for idx in domains[depth].index_view().iter() {
                let vec = domains[depth]
                    .dims_vector(idx as usize)
                    .ok_or(EvalError::UnboundVariable)?;
                env.push((vars[depth], vec));
                let res = rec(ev, domains, vars, env, visit, depth + 1);
                env.pop();
                res?;
            }
            Ok(())
        }

        let mut domains = Vec::with_capacity(decls.len());
        let mut vars = Vec::with_capacity(decls.len());
        for d in decls {
            let var_arity = arena.variable_arity(d.variable);
            let m = self.expr_set(arena, d.expr, env)?;
            if m.arity() != var_arity {
                return Err(EvalError::UnboundVariable);
            }
            domains.push(m);
            vars.push(d.variable);
        }
        let mut env2: Env = env.to_vec();
        rec(self, &domains, &vars, &mut env2, visit, 0)
    }
}

fn int_const_of(arena: &AstArena, i: IntId) -> Result<i64, EvalError> {
    match arena.int(i) {
        IntNode::Constant(v) => Ok(*v),
        _ => Err(EvalError::UnboundInteger(i64::MIN)),
    }
}

fn flat_of(ts: &TupleSet, vec: &[u32]) -> Result<Int, EvalError> {
    let dims = crate::dimensions::Dimensions::square(ts.universe().size() as u32, ts.arity())
        .map_err(|_| EvalError::UnboundVariable)?;
    dims.flat_of(vec)
        .map(|v| v as Int)
        .ok_or(EvalError::UnboundVariable)
}

fn union(a: &TupleSet, b: &TupleSet) -> Result<TupleSet, EvalError> {
    TupleSet::from_indices(
        a.universe(),
        a.arity(),
        a.index_view().union(b.index_view()),
    )
    .map_err(|_| EvalError::UnboundVariable)
}

fn intersection(a: &TupleSet, b: &TupleSet) -> Result<TupleSet, EvalError> {
    TupleSet::from_indices(
        a.universe(),
        a.arity(),
        a.index_view().intersection(b.index_view()),
    )
    .map_err(|_| EvalError::UnboundVariable)
}

fn difference(a: &TupleSet, b: &TupleSet) -> Result<TupleSet, EvalError> {
    TupleSet::from_indices(
        a.universe(),
        a.arity(),
        a.index_view().difference(b.index_view()),
    )
    .map_err(|_| EvalError::UnboundVariable)
}

fn transpose(a: &TupleSet) -> Result<TupleSet, EvalError> {
    let rows = a.universe().size();
    let mut out = IntSet::new();
    for i in a.index_view().iter() {
        let i = i as usize;
        out.insert(((i % rows) * rows + (i / rows)) as Int);
    }
    TupleSet::from_indices(a.universe(), 2, out).map_err(|_| EvalError::UnboundVariable)
}

fn cross(a: &TupleSet, b: &TupleSet) -> Result<TupleSet, EvalError> {
    let bcap = b.capacity().map_err(|_| EvalError::UnboundVariable)? as usize;
    let mut out = IntSet::new();
    for i in a.index_view().iter() {
        for j in b.index_view().iter() {
            out.insert(i * bcap as Int + j);
        }
    }
    TupleSet::from_indices(a.universe(), a.arity() + b.arity(), out)
        .map_err(|_| EvalError::UnboundVariable)
}

fn join(a: &TupleSet, b: &TupleSet) -> Result<TupleSet, EvalError> {
    let l = a.universe().size();
    let b_rest = b.capacity().unwrap_or(0) as usize / l;
    let mut out = IntSet::new();
    for i in a.index_view().iter() {
        let i = i as usize;
        for j in b.index_view().iter() {
            let j = j as usize;
            if i % l == j / b_rest {
                out.insert((i / l * b_rest + j % b_rest) as Int);
            }
        }
    }
    TupleSet::from_indices(a.universe(), a.arity() + b.arity() - 2, out)
        .map_err(|_| EvalError::UnboundVariable)
}

fn override_sets(a: &TupleSet, b: &TupleSet) -> Result<TupleSet, EvalError> {
    let rest = a.capacity().unwrap_or(0) as usize / a.universe().size().max(1);
    let b_prefixes: IntSet = b
        .index_view()
        .iter()
        .map(|j| (j as usize / rest) as Int)
        .collect();
    let mut out = b.index_view().clone();
    for i in a.index_view().iter() {
        if !b_prefixes.contains((i as usize / rest) as Int) {
            out.insert(i);
        }
    }
    TupleSet::from_indices(a.universe(), a.arity(), out).map_err(|_| EvalError::UnboundVariable)
}

fn closure(a: &TupleSet, reflexive: bool) -> Result<TupleSet, EvalError> {
    let n = a.universe().size();
    let mut adj: Vec<IntSet> = (0..n).map(|_| IntSet::new()).collect();
    for i in a.index_view().iter() {
        let i = i as usize;
        adj[i / n].insert((i % n) as Int);
    }
    for k in 0..n {
        let through = adj[k].clone();
        for row in adj.iter_mut() {
            if row.contains(k as Int) {
                for y in through.iter() {
                    row.insert(y);
                }
            }
        }
    }
    let mut out = IntSet::new();
    for (x, row) in adj.iter().enumerate() {
        for yy in row.iter() {
            out.insert((x * n + yy as usize) as Int);
        }
    }
    if reflexive {
        for i in 0..n {
            out.insert((i * n + i) as Int);
        }
    }
    TupleSet::from_indices(a.universe(), 2, out).map_err(|_| EvalError::UnboundVariable)
}
