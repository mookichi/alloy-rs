use std::collections::HashMap;
use std::rc::Rc;

use crate::ast::{AstArena, ConstantExpr, ExprNode, FormulaNode, Multiplicity, Quantifier, VarId};
use crate::bmatrix::{BoolCtx, BooleanMatrix};
use crate::bool::{const_false, const_true, BoolRef};
use crate::bounds::Bounds;
use crate::dimensions::Dimensions;
use crate::int::IntCircuit;
use crate::relation::RelationId;
#[derive(Clone, Copy, Debug)]
pub struct VarOrigin {
    pub slot: u32,
    pub relation: RelationId,
    pub tuple_index: i64,
}

pub struct FolTranslator<'a> {
    pub ctx: BoolCtx,
    pub bounds: &'a Bounds,
    leaves: HashMap<RelationId, Rc<BooleanMatrix>>,
    bitwidth: u32,
    origins: Vec<VarOrigin>,
}

#[derive(Debug, thiserror::Error)]
pub enum TranslateError {
    #[error("relation {0} has no bounds")]
    UnboundRelation(u32),
    #[error("integer layer is not supported in this iteration")]
    UnsupportedInt,
    #[error("no bound for integer {0}")]
    UnboundInteger(i64),
    #[error("temporal layer is not supported in this iteration")]
    UnsupportedTemporal,
    #[error("{op} arity mismatch: expected {expected} got {got}")]
    Arity {
        op: &'static str,
        expected: u32,
        got: u32,
    },
    #[error("matrix op failed: {0}")]
    Matrix(#[from] crate::bmatrix::MatrixError),
    #[error("cnf translation failed: {0}")]
    Cnf(#[from] crate::cnf::CnfError),
    #[error("evaluation failed: {0}")]
    Eval(#[from] crate::eval::EvalError),
    #[error("quantifier domain must be unary or match variable arity")]
    BadDomain,
}

type Env = Vec<(VarId, Vec<u32>)>;
type DeclVisitor<'a, 'b> =
    dyn FnMut(&mut FolTranslator<'a>, Env, &[BoolRef]) -> Result<(), TranslateError> + 'b;

fn arena_int_constant(arena: &AstArena, i: crate::ast::IntId) -> Result<i64, TranslateError> {
    match arena.int(i) {
        crate::ast::IntNode::Constant(v) => Ok(*v),
        _ => Err(TranslateError::UnsupportedInt),
    }
}

impl<'a> FolTranslator<'a> {
    pub fn new(ctx: BoolCtx, bounds: &'a Bounds) -> FolTranslator<'a> {
        FolTranslator {
            ctx,
            bounds,
            leaves: HashMap::new(),
            bitwidth: 4,
            origins: Vec::new(),
        }
    }

    pub fn var_origins(&self) -> &[VarOrigin] {
        &self.origins
    }

    pub fn materialize(&self, truth: impl Fn(u32) -> bool) -> crate::instance::Instance {
        use crate::instance::Instance;
        use crate::tupleset::TupleSet;
        let mut inst = Instance::new(self.bounds.universe(), self.bounds.pool());
        let mut extras: HashMap<RelationId, Vec<i64>> = HashMap::new();
        for o in &self.origins {
            if truth(o.slot) {
                extras.entry(o.relation).or_default().push(o.tuple_index);
            }
        }
        for r in self.bounds.relations() {
            let arity = self.bounds.pool().arity(r);
            let mut ts = TupleSet::new(self.bounds.universe(), arity).unwrap();
            if let Some(lower) = self.bounds.lower_bound(r) {
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
        inst
    }

    pub fn set_bitwidth(&mut self, w: u32) {
        assert!((1..=30).contains(&w), "bitwidth must be 1..=30");
        self.bitwidth = w;
    }

    pub fn bitwidth(&self) -> u32 {
        self.bitwidth
    }

    fn univ(&self) -> usize {
        self.bounds.universe().size()
    }

    fn dims(&self, arity: u32) -> Result<Dimensions, TranslateError> {
        Dimensions::square(self.univ() as u32, arity).map_err(|_| TranslateError::UnsupportedInt)
    }

    fn const_matrix(&self, dims: &Dimensions, filled: impl Fn(usize) -> bool) -> BooleanMatrix {
        let mut m = BooleanMatrix::new(dims.clone(), &self.ctx);
        for i in 0..dims.capacity() {
            if filled(i) {
                let _ = m.set(i, const_true());
            }
        }
        m
    }

    fn single_cell(&self, arity: u32, index: usize) -> Result<BooleanMatrix, TranslateError> {
        let mut m = BooleanMatrix::new(self.dims(arity)?, &self.ctx);
        m.set(index, const_true())?;
        Ok(m)
    }

    fn leaf_relation(&mut self, r: RelationId) -> Result<Rc<BooleanMatrix>, TranslateError> {
        if let Some(m) = self.leaves.get(&r) {
            return Ok(Rc::clone(m));
        }
        let lower = self
            .bounds
            .lower_bound(r)
            .ok_or(TranslateError::UnboundRelation(r.0))?;
        let upper = self.bounds.upper_bound(r).unwrap_or(lower);
        let mut m = BooleanMatrix::new(self.dims(upper.arity())?, &self.ctx);
        for idx in upper.index_view().iter() {
            let value = if lower.contains_index(idx) {
                const_true()
            } else {
                let var = self.ctx.variable();
                self.origins.push(VarOrigin {
                    slot: var.slot(),
                    relation: r,
                    tuple_index: idx,
                });
                var
            };
            let _ = m.set(idx as usize, value);
        }
        let m = Rc::new(m);
        self.leaves.insert(r, Rc::clone(&m));
        Ok(m)
    }

    fn leaf_constant(&self, c: ConstantExpr) -> Result<Rc<BooleanMatrix>, TranslateError> {
        let u = self.univ() as u32;
        let m = match c {
            ConstantExpr::Univ => {
                let d = self.dims(1)?;
                Rc::new(self.const_matrix(&d, |_| true))
            }
            ConstantExpr::Empty => Rc::new(BooleanMatrix::new(self.dims(1)?, &self.ctx)),
            ConstantExpr::Iden => {
                let d = self.dims(2)?;
                Rc::new(self.const_matrix(&d, |i| (i / u as usize) == (i % u as usize)))
            }
            ConstantExpr::Ints => return Err(TranslateError::UnsupportedInt),
        };
        Ok(m)
    }

    pub fn expr_matrix(
        &mut self,
        arena: &AstArena,
        e: crate::ast::ExprId,
        env: &[(VarId, Vec<u32>)],
    ) -> Result<Rc<BooleanMatrix>, TranslateError> {
        match arena.expr(e).clone() {
            ExprNode::Relation(r) => self.leaf_relation(r),
            ExprNode::Variable(v) => {
                let (_, vec) = env
                    .iter()
                    .rev()
                    .find(|(id, _)| *id == v)
                    .ok_or(TranslateError::BadDomain)?;
                let idx = self.flat(vec)?;
                Ok(Rc::new(
                    self.single_cell(self.univ_var_arity(vec.len()), idx)?,
                ))
            }
            ExprNode::Constant(c) => self.leaf_constant(c),
            ExprNode::Unary { op, child } => {
                let m = self.expr_matrix(arena, child, env)?;
                let out = match op {
                    crate::ast::UnaryExprOp::Transpose => m.transpose()?,
                    crate::ast::UnaryExprOp::Closure => m.closure_transitive()?,
                    crate::ast::UnaryExprOp::ReflexiveClosure => {
                        let iden = self.leaf_constant(ConstantExpr::Iden)?;
                        m.or(&iden)?
                    }
                };
                Ok(Rc::new(out))
            }
            ExprNode::Temporal { .. } => Err(TranslateError::UnsupportedTemporal),
            ExprNode::Binary { op, left, right } => {
                use crate::ast::BinaryOp::*;
                let a = self.expr_matrix(arena, left, env)?;
                let b = self.expr_matrix(arena, right, env)?;
                let out = match op {
                    Union => a.or(&b)?,
                    Intersection => a.and(&b)?,
                    Difference => self.pointwise(a.as_ref(), b.as_ref(), |ctx, x, y| {
                        ctx.and(&[x, ctx.not(y)])
                    }),
                    Override => a.override_values(&b)?,
                    Product => a.cross(&b)?,
                    Join => a.join(&b)?,
                };
                Ok(Rc::new(out))
            }
            ExprNode::Nary { op, children } => {
                use crate::ast::BinaryOp::*;
                let mut acc = (*self.expr_matrix(arena, children[0], env)?).clone();
                for &c in &children[1..] {
                    let m = self.expr_matrix(arena, c, env)?;
                    acc = match op {
                        Union => acc.or(&m)?,
                        Intersection => acc.and(&m)?,
                        Difference => {
                            self.pointwise(&acc, &m, |ctx, x, y| ctx.and(&[x, ctx.not(y)]))
                        }
                        Override => self.pointwise(&acc, &m, |ctx, x, y| ctx.ite(y, y, x)),
                        Product => acc.cross(&m)?,
                        Join => acc.join(&m)?,
                    };
                }
                Ok(Rc::new(acc))
            }
            ExprNode::If { cond, then, els } => {
                let c = self.formula_ref(arena, cond, env)?;
                let t = self.expr_matrix(arena, then, env)?;
                let e = self.expr_matrix(arena, els, env)?;
                Ok(Rc::new(t.choice(c, &e)?))
            }
            ExprNode::Project { .. } => Err(TranslateError::UnsupportedInt),
            ExprNode::Comprehension { decls, body } => {
                let decl_list = arena.decls(decls).to_vec();
                let mut result: HashMap<usize, Vec<BoolRef>> = HashMap::new();
                self.iter_decls(arena, &decl_list, env, &mut |this, binding, lits| {
                    let idx_vec: Vec<u32> = binding
                        .iter()
                        .flat_map(|(_, v)| v.iter().copied())
                        .collect();
                    let idx = this.flat(&idx_vec)?;
                    let f = this.formula_ref(arena, body, &binding)?;
                    let entry = if lits.is_empty() {
                        f
                    } else {
                        this.ctx.and(&[this.ctx.and(lits), f])
                    };
                    result.entry(idx).or_default().push(entry);
                    Ok(())
                })?;
                let total_arity: u32 = decl_list
                    .iter()
                    .map(|d| arena.variable_arity(d.variable))
                    .sum();
                let mut m = BooleanMatrix::new(self.dims(total_arity)?, &self.ctx);
                for (idx, terms) in result {
                    m.set(idx, self.ctx.or(&terms))?;
                }
                Ok(Rc::new(m))
            }
            ExprNode::FromInt(i) => {
                let v = arena_int_constant(arena, i)?;
                let ts = self
                    .bounds
                    .exact_int_bound(v)
                    .ok_or(TranslateError::UnboundInteger(v))?;
                let mut m = BooleanMatrix::new(self.dims(1)?, &self.ctx);
                for idx in ts.index_view().iter() {
                    let _ = m.set(idx as usize, const_true());
                }
                Ok(Rc::new(m))
            }
        }
    }

    fn pointwise(
        &self,
        a: &BooleanMatrix,
        b: &BooleanMatrix,
        f: impl Fn(&BoolCtx, BoolRef, BoolRef) -> BoolRef,
    ) -> BooleanMatrix {
        let mut ret = BooleanMatrix::new(a.dims().clone(), &self.ctx);
        let keys: std::collections::BTreeSet<usize> = a
            .iter()
            .map(|(i, _)| i)
            .chain(b.iter().map(|(i, _)| i))
            .collect();
        for i in keys {
            let x = a.get(i).unwrap_or(const_false());
            let y = b.get(i).unwrap_or(const_false());
            let v = f(&self.ctx, x, y);
            let _ = ret.set(i, v);
        }
        ret
    }

    fn flat(&self, vec: &[u32]) -> Result<usize, TranslateError> {
        let dims = Dimensions::square(self.univ() as u32, vec.len() as u32)
            .map_err(|_| TranslateError::BadDomain)?;
        dims.flat_of(vec).ok_or(TranslateError::BadDomain)
    }

    fn univ_var_arity(&self, len: usize) -> u32 {
        len as u32
    }

    fn decl_domain(
        &mut self,
        arena: &AstArena,
        d: &crate::ast::Decl,
        env: &[(VarId, Vec<u32>)],
    ) -> Result<(Rc<BooleanMatrix>, VarId), TranslateError> {
        let var_arity = arena.variable_arity(d.variable);
        let m = self.expr_matrix(arena, d.expr, env)?;
        if m.dims().num_dimensions() as u32 != var_arity {
            return Err(TranslateError::Arity {
                op: "decl",
                expected: var_arity,
                got: m.dims().num_dimensions() as u32,
            });
        }
        Ok((m, d.variable))
    }

    fn iter_decls(
        &mut self,
        arena: &AstArena,
        decls: &[crate::ast::Decl],
        env: &[(VarId, Vec<u32>)],
        visit: &mut DeclVisitor<'a, '_>,
    ) -> Result<(), TranslateError> {
        fn rec<'b>(
            this: &mut FolTranslator<'b>,
            domains: &[Rc<BooleanMatrix>],
            vars: &[VarId],
            env: &mut Env,
            lits: &mut Vec<BoolRef>,
            visit: &mut DeclVisitor<'b, '_>,
            depth: usize,
        ) -> Result<(), TranslateError> {
            if depth == domains.len() {
                return visit(this, env.clone(), lits);
            }
            let cells: Vec<usize> = domains[depth].iter().map(|(i, _)| i).collect();
            for idx in cells {
                let vec = domains[depth]
                    .dims()
                    .vector_of(idx)
                    .ok_or(TranslateError::BadDomain)?;
                let lit = domains[depth].get(idx).unwrap_or_else(const_true);
                env.push((vars[depth], vec));
                lits.push(lit);
                let res = rec(this, domains, vars, env, lits, visit, depth + 1);
                lits.pop();
                env.pop();
                res?;
            }
            Ok(())
        }

        let mut domains = Vec::with_capacity(decls.len());
        let mut vars = Vec::with_capacity(decls.len());
        for d in decls {
            let (m, v) = self.decl_domain(arena, d, env)?;
            domains.push(m);
            vars.push(v);
        }
        let mut env2: Env = env.to_vec();
        let mut lits: Vec<BoolRef> = Vec::with_capacity(decls.len());
        rec(self, &domains, &vars, &mut env2, &mut lits, visit, 0)
    }

    pub fn int_expr(
        &mut self,
        arena: &AstArena,
        i: crate::ast::IntId,
        env: &[(VarId, Vec<u32>)],
    ) -> Result<Rc<IntCircuit>, TranslateError> {
        use crate::ast::{CastToIntOp, IntBinOp, IntNode};
        let bw = self.bitwidth;
        let node = arena.int(i).clone();
        let out = match node {
            IntNode::Constant(v) => IntCircuit::constant(v, bw, &self.ctx),
            IntNode::OfExpr { op, expr } => {
                let m = self.expr_matrix(arena, expr, env)?;
                match op {
                    CastToIntOp::Cardinality => {
                        let mut acc = IntCircuit::constant(0, bw, &self.ctx);
                        let one = IntCircuit::constant(1, bw, &self.ctx);
                        for (_, cell) in m.iter() {
                            let term_bits = vec![cell];
                            let mut term = IntCircuit::from_bits(term_bits, &self.ctx);
                            while term.width() < bw as usize {
                                term.bits.push(const_false());
                            }
                            acc = acc.add(&term, bw);
                        }
                        let _ = &one;
                        acc
                    }
                    CastToIntOp::Sum => {
                        let mut positions: Vec<(i64, usize)> = Vec::new();
                        for (val, ts) in self.bounds.int_bounds() {
                            for idx in ts.index_view().iter() {
                                positions.push((val, idx as usize));
                            }
                        }
                        positions.sort_by_key(|p| p.1);
                        let mut acc = IntCircuit::constant(0, bw, &self.ctx);
                        for &(val, pos) in &positions {
                            if let Some(cell) = m.get(pos) {
                                let c = IntCircuit::constant(val, bw, &self.ctx);
                                acc = acc.add(&c.choice(cell, &IntCircuit::zero(&self.ctx)), bw);
                            }
                        }
                        acc
                    }
                }
            }
            IntNode::Binary { op, left, right } => {
                let l = self.int_expr(arena, left, env)?;
                let r = self.int_expr(arena, right, env)?;
                match op {
                    IntBinOp::Plus => l.add(&r, bw),
                    IntBinOp::Minus => l.sub(&r, bw),
                    IntBinOp::Times => l.mul(&r, bw),
                    IntBinOp::Divide => l.div(&r, bw),
                    IntBinOp::Modulo => l.rem(&r, bw),
                    IntBinOp::And => l.bit_and(&r),
                    IntBinOp::Or => l.bit_or(&r),
                    IntBinOp::Xor => l.bit_xor(&r),
                    IntBinOp::Shl => l.shl(&r, bw),
                    IntBinOp::Shr => l.shr(&r, bw),
                }
            }
            IntNode::If { cond, then, els } => {
                let c = self.formula_ref(arena, cond, env)?;
                let t = self.int_expr(arena, then, env)?;
                let e = self.int_expr(arena, els, env)?;
                t.choice(c, &e)
            }
            IntNode::Sum { decls, body } => {
                let decl_list = arena.decls(decls).to_vec();
                let mut acc = IntCircuit::constant(0, bw, &self.ctx);
                self.iter_decls(arena, &decl_list, env, &mut |this, binding, lits| {
                    let t = this.int_expr(arena, body, &binding)?;
                    let t = if lits.is_empty() {
                        t
                    } else {
                        let m = this.ctx.and(lits);
                        let mask = IntCircuit::from_bits(vec![m; bw as usize], &this.ctx);
                        Rc::new(t.bit_and(&mask))
                    };
                    acc = acc.add(&t, bw);
                    Ok(())
                })?;
                acc
            }
        };
        Ok(Rc::new(out))
    }

    pub fn formula_ref(
        &mut self,
        arena: &AstArena,
        f: crate::ast::FormulaId,
        env: &[(VarId, Vec<u32>)],
    ) -> Result<BoolRef, TranslateError> {
        match arena.formula(f).clone() {
            FormulaNode::Constant(v) => Ok(if v { const_true() } else { const_false() }),
            FormulaNode::Not(child) => {
                let inner = self.formula_ref(arena, child, env)?;
                Ok(self.ctx.not(inner))
            }
            FormulaNode::Nary { op, children } => {
                let refs: Vec<BoolRef> = children
                    .iter()
                    .map(|&c| self.formula_ref(arena, c, env))
                    .collect::<Result<_, _>>()?;
                Ok(match op {
                    crate::ast::FormulaBinOp::And => self.ctx.and(&refs),
                    crate::ast::FormulaBinOp::Or => self.ctx.or(&refs),
                })
            }
            FormulaNode::Comparison { op, left, right } => {
                let l = self.expr_matrix(arena, left, env)?;
                let r = self.expr_matrix(arena, right, env)?;
                if l.dims() != r.dims() {
                    return Err(TranslateError::Arity {
                        op: "comparison",
                        expected: l.dims().capacity() as u32,
                        got: r.dims().capacity() as u32,
                    });
                }
                let mut acc = const_true();
                for i in 0..l.dims().capacity() {
                    let a = l.get(i).unwrap_or(const_false());
                    let b = r.get(i).unwrap_or(const_false());
                    let term = match op {
                        crate::ast::ExprCompOp::Equals => self.ctx.or(&[
                            self.ctx.and(&[a, b]),
                            self.ctx.and(&[self.ctx.not(a), self.ctx.not(b)]),
                        ]),
                        crate::ast::ExprCompOp::Subset => self.ctx.or(&[self.ctx.not(a), b]),
                    };
                    acc = self.ctx.and(&[acc, term]);
                }
                Ok(acc)
            }
            FormulaNode::IntComparison { op, left, right } => {
                let l = self.int_expr(arena, left, env)?;
                let r = self.int_expr(arena, right, env)?;
                let cmp = match op {
                    crate::ast::IntCompOp::Eq => l.eq(&r),
                    crate::ast::IntCompOp::Neq => l.neq(&r),
                    crate::ast::IntCompOp::Lt => l.lt(&r),
                    crate::ast::IntCompOp::Lte => l.lte(&r),
                    crate::ast::IntCompOp::Gt => l.gt(&r),
                    crate::ast::IntCompOp::Gte => l.gte(&r),
                };
                Ok(cmp)
            }
            FormulaNode::Quantified { quant, decls, body } => {
                let decl_list = arena.decls(decls).to_vec();
                let mut refs: Vec<BoolRef> = Vec::new();
                self.iter_decls(arena, &decl_list, env, &mut |this, binding, lits| {
                    let body = this.formula_ref(arena, body, &binding)?;
                    let ref_ = if lits.is_empty() {
                        body
                    } else {
                        let m = this.ctx.and(lits);
                        match quant {
                            Quantifier::All => this.ctx.or(&[this.ctx.not(m), body]),
                            Quantifier::Some => this.ctx.and(&[m, body]),
                        }
                    };
                    refs.push(ref_);
                    Ok(())
                })?;
                Ok(match quant {
                    Quantifier::All => self.ctx.and(&refs),
                    Quantifier::Some => self.ctx.or(&refs),
                })
            }
            FormulaNode::Multiplicity { mult, expr } => {
                let m = self.expr_matrix(arena, expr, env)?;
                let cells: Vec<BoolRef> = m
                    .iter()
                    .filter(|&(_, v)| v != const_false())
                    .map(|(_, v)| v)
                    .collect();
                match mult {
                    Multiplicity::Some => Ok(self.ctx.or(&cells)),
                    Multiplicity::One | Multiplicity::Lone => {
                        let mut pairwise = const_true();
                        for i in 0..cells.len() {
                            for j in i + 1..cells.len() {
                                let both = self.ctx.and(&[cells[i], cells[j]]);
                                pairwise = self.ctx.and(&[pairwise, self.ctx.not(both)]);
                            }
                        }
                        if mult == Multiplicity::One {
                            Ok(self.ctx.and(&[self.ctx.or(&cells), pairwise]))
                        } else {
                            Ok(pairwise)
                        }
                    }
                    Multiplicity::Set => Err(TranslateError::Arity {
                        op: "mult",
                        expected: 0,
                        got: 0,
                    }),
                }
            }
            FormulaNode::TemporalUnary { .. } => Err(TranslateError::UnsupportedTemporal),
            FormulaNode::TemporalBinary { .. } => Err(TranslateError::UnsupportedTemporal),
        }
    }
}
