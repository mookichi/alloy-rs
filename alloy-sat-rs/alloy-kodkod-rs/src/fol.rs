use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher};
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
    /// Java `noOverflow` equivalent (default ON): integer comparisons are
    /// gated by `AND(cmp, NOT accum_overflow)`. Division-by-zero is always
    /// UNSAT (folded into `accum_overflow` at the circuit level).
    /// NOTE: full `DefCond.ensureDef` polarity handling (ALL vs SOME under
    /// negation) is backlog; the current gate is exact for positive
    /// (existential/top-level) contexts.
    no_overflow: bool,
    origins: Vec<VarOrigin>,
    /// Translation counters (reported under `ALLOY_TIMING`).
    pub stats: FolStats,
    /// (Expression, bound-variable-values) → matrix memo. Quantifier
    /// bodies rebuild identical join/union subcircuits per binding
    /// (e.g. `c1.lectures` is rebuilt per enclosing binding although it
    /// only depends on `c1`); memoizing collapses them. Sound: the matrix
    /// is a pure function of the inputs. Keys project the environment
    /// onto the expression's free variables.
    matrix_memo: HashMap<MemoKey, Rc<BooleanMatrix>, BuildHasherDefault<Fnv>>,
    /// Free-variable sets per ExprId (memoized). `None` = conservative
    /// (all env entries participate in the key).
    free_memo: HashMap<u32, Option<Vec<u32>>>,
    /// (Formula, free-env-values) → BoolRef memo. Nested quantifiers
    /// whose free variables are a strict subset of the enclosing
    /// bindings (e.g. `some l1,l2: Lecture` inside `all stu,c1,c2`
    /// depending only on `(c1,c2)`) are translated once per distinct
    /// value combination instead of once per enclosing iteration.
    formula_memo: HashMap<MemoKey, BoolRef, BuildHasherDefault<Fnv>>,
    /// Free-variable sets per FormulaId (memoized).
    ffree_memo: HashMap<u32, Option<Vec<u32>>>,
    /// Matrix/formula memo hit/miss counters.
    pub memo_hits: u64,
    pub memo_miss: u64,
    /// Translation-collected soft unit sources (AlloyMax `maxsome` /
    /// `minsome` / `soft fact`). Each entry is maximized by the
    /// core-guided loop; the hard translation contributes `true`.
    pub softs: Vec<SoftEntry>,
}

/// One collected soft: circuit root plus maximize-direction weight.
#[derive(Clone, Copy, Debug)]
pub struct SoftEntry {
    pub root: BoolRef,
    pub weight: i64,
    /// True for `minsome` cells: the loop maximizes the negation, and
    /// cost accounting complements the model value back.
    pub minimize: bool,
}

/// Zero-dependency FNV-1a hasher for the translation memos (std
/// `HashMap` uses SipHash, measurably slower at millions of lookups).
#[derive(Default)]
struct Fnv(u64);

impl Hasher for Fnv {
    fn write(&mut self, bytes: &[u8]) {
        const PRIME: u64 = 0x100000001b3;
        let mut h = if self.0 == 0 {
            0xcbf29ce484222325
        } else {
            self.0
        };
        for &b in bytes {
            h ^= b as u64;
            h = h.wrapping_mul(PRIME);
        }
        self.0 = h;
    }

    fn finish(&self) -> u64 {
        if self.0 == 0 {
            0xcbf29ce484222325
        } else {
            self.0
        }
    }
}

/// Memo key: expression id + FREE bound-variable values.
#[derive(Clone, PartialEq, Eq, Hash)]
struct MemoKey {
    expr: u32,
    env: Vec<(u32, Vec<u32>)>,
}

impl MemoKey {
    /// `free`: sorted free-var ids of the expression (`None` = all).
    fn new(e: crate::ast::ExprId, env: &[(VarId, Vec<u32>)], free: Option<&[u32]>) -> MemoKey {
        let env = match free {
            Some(set) => env
                .iter()
                .filter(|(v, _)| set.binary_search(&v.0).is_ok())
                .map(|(v, x)| (v.0, x.clone()))
                .collect(),
            None => env.iter().map(|(v, x)| (v.0, x.clone())).collect(),
        };
        MemoKey { expr: e.0, env }
    }

    /// Formula variant (separate id namespace, separate map).
    fn new_formula(
        f: crate::ast::FormulaId,
        env: &[(VarId, Vec<u32>)],
        free: Option<&[u32]>,
    ) -> MemoKey {
        let env = match free {
            Some(set) => env
                .iter()
                .filter(|(v, _)| set.binary_search(&v.0).is_ok())
                .map(|(v, x)| (v.0, x.clone()))
                .collect(),
            None => env.iter().map(|(v, x)| (v.0, x.clone())).collect(),
        };
        MemoKey { expr: f.0, env }
    }
}

/// Translation counters (reported under `ALLOY_TIMING`).
#[derive(Default, Debug, Clone, Copy)]
pub struct FolStats {
    pub matrix_join: u64,
    pub quant_bodies: u64,
    pub formula_refs: u64,
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
    #[error("sat solver error: {0}")]
    Solver(String),
    #[error(transparent)]
    Temporal(#[from] crate::temporal::TemporalError),
    #[error(transparent)]
    Skolem(#[from] crate::skolem::SkolemError),
    #[error(transparent)]
    Pardinus(#[from] crate::pardinus::PardinusError),
    #[error("ast error: {0}")]
    Ast(#[from] crate::ast::AstError),
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
            no_overflow: true,
            origins: Vec::new(),
            stats: FolStats::default(),
            matrix_memo: HashMap::default(),
            free_memo: HashMap::new(),
            formula_memo: HashMap::default(),
            ffree_memo: HashMap::new(),
            memo_hits: 0,
            memo_miss: 0,
            softs: Vec::new(),
        }
    }

    /// Standard translator setup shared by every translation entry point
    /// (`Solver`, `ucore`, `opt`, and the front `Cnf` builders): applies
    /// `bitwidth`/`no_overflow` in one place so new options cannot be
    /// missed at individual call sites.
    pub fn with_options(
        ctx: BoolCtx,
        bounds: &'a Bounds,
        bitwidth: u32,
        no_overflow: bool,
    ) -> FolTranslator<'a> {
        let mut t = FolTranslator::new(ctx, bounds);
        t.set_bitwidth(bitwidth);
        t.set_no_overflow(no_overflow);
        t
    }

    /// Sorted free-variable ids of an expression. `None` = conservative
    /// fallback (anything beyond plain relation/variable/constant/atom
    /// nodes and boolean-algebra connectives).
    fn free_vars_of(&mut self, arena: &AstArena, e: crate::ast::ExprId) -> Option<Vec<u32>> {
        if let Some(v) = self.free_memo.get(&e.0) {
            return v.clone();
        }
        let out: Option<Vec<u32>> = match arena.expr(e) {
            ExprNode::Variable(v) => Some(vec![v.0]),
            ExprNode::Relation(_) | ExprNode::Constant(_) | ExprNode::Atoms(_) => Some(Vec::new()),
            ExprNode::Unary { child, .. } => self.free_vars_of(arena, *child),
            ExprNode::Binary { left, right, .. } => {
                let mut l = self.free_vars_of(arena, *left)?;
                let r = self.free_vars_of(arena, *right)?;
                l.extend(r);
                l.sort_unstable();
                l.dedup();
                Some(l)
            }
            ExprNode::Nary { children, .. } => {
                let mut acc = Vec::new();
                for &c in children {
                    acc.extend(self.free_vars_of(arena, c)?);
                }
                acc.sort_unstable();
                acc.dedup();
                Some(acc)
            }
            _ => None,
        };
        self.free_memo.insert(e.0, out.clone());
        out
    }

    pub fn var_origins(&self) -> &[VarOrigin] {
        &self.origins
    }

    /// Materializes the leaf circuit for `r` if absent. Used by the
    /// optimizer to give weighted relations primary slots even when the
    /// formula never mentions them (origins are otherwise only recorded
    /// for relations visited during translation).
    pub fn ensure_relation(&mut self, r: RelationId) -> Result<(), TranslateError> {
        self.leaf_relation(r).map(|_| ())
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

    /// Opt-out for the overflow prohibition (`false` restores pure wrapping).
    pub fn set_no_overflow(&mut self, v: bool) {
        self.no_overflow = v;
    }

    pub fn no_overflow(&self) -> bool {
        self.no_overflow
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
        // Memoize composite nodes by (expression, free env values).
        // Leaves (Relation/Variable/Constant/Atoms) are cheap or cached.
        // `ALLOY_NOMATRIXMEMO=1` disables the matrix memo (diagnostics).
        let no_mmemo = std::env::var_os("ALLOY_NOMATRIXMEMO").is_some();
        let memoize = !no_mmemo
            && matches!(
                arena.expr(e),
                ExprNode::Binary { .. }
                    | ExprNode::Nary { .. }
                    | ExprNode::Unary { .. }
                    | ExprNode::If { .. }
                    | ExprNode::Comprehension { .. }
            );
        if memoize {
            let free = self.free_vars_of(arena, e);
            let key = MemoKey::new(e, env, free.as_deref());
            if let Some(m) = self.matrix_memo.get(&key) {
                self.memo_hits += 1;
                return Ok(Rc::clone(m));
            }
            self.memo_miss += 1;
            let m = self.expr_matrix_uncached(arena, e, env)?;
            self.matrix_memo.insert(key, Rc::clone(&m));
            return Ok(m);
        }
        self.expr_matrix_uncached(arena, e, env)
    }

    fn expr_matrix_uncached(
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
            ExprNode::Atoms(atoms) => {
                let set: std::collections::HashSet<usize> =
                    atoms.into_iter().map(|a| a as usize).collect();
                Ok(Rc::new(
                    self.const_matrix(&self.dims(1)?, |i| set.contains(&i)),
                ))
            }
            ExprNode::Unary { op, child } => {
                let m = self.expr_matrix(arena, child, env)?;
                let out = match op {
                    crate::ast::UnaryExprOp::Transpose => m.transpose()?,
                    crate::ast::UnaryExprOp::Closure => m.closure_transitive()?,
                    crate::ast::UnaryExprOp::ReflexiveClosure => {
                        let tc = m.closure_transitive()?;
                        let iden = self.leaf_constant(ConstantExpr::Iden)?;
                        tc.or(&iden)?
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
                    Join => {
                        self.stats.matrix_join += 1;
                        a.join(&b)?
                    }
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
                        Join => {
                            self.stats.matrix_join += 1;
                            acc.join(&m)?
                        }
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

    fn iter_decls(
        &mut self,
        arena: &AstArena,
        decls: &[crate::ast::Decl],
        env: &[(VarId, Vec<u32>)],
        visit: &mut DeclVisitor<'a, '_>,
    ) -> Result<(), TranslateError> {
        fn rec<'b>(
            this: &mut FolTranslator<'b>,
            arena: &AstArena,
            decls: &[crate::ast::Decl],
            env: &mut Env,
            lits: &mut Vec<BoolRef>,
            visit: &mut DeclVisitor<'b, '_>,
            depth: usize,
        ) -> Result<(), TranslateError> {
            if depth == decls.len() {
                return visit(this, env.clone(), lits);
            }
            let d = &decls[depth];
            let var_arity = arena.variable_arity(d.variable);
            let m = this.expr_matrix(arena, d.expr, env)?;
            if m.dims().num_dimensions() as u32 != var_arity {
                return Err(TranslateError::Arity {
                    op: "decl",
                    expected: var_arity,
                    got: m.dims().num_dimensions() as u32,
                });
            }
            let cells: Vec<usize> = m.iter().map(|(i, _)| i).collect();
            for idx in cells {
                let vec = match m.dims().vector_of(idx) {
                    Some(v) => v,
                    None => {
                        return Err(TranslateError::BadDomain);
                    }
                };
                let lit = m.get(idx).unwrap_or_else(const_true);
                env.push((d.variable, vec));
                lits.push(lit);
                let res = rec(this, arena, decls, env, lits, visit, depth + 1);
                lits.pop();
                env.pop();
                res?;
            }
            Ok(())
        }

        let mut env2: Env = env.to_vec();
        let mut lits: Vec<BoolRef> = Vec::with_capacity(decls.len());
        rec(self, arena, decls, &mut env2, &mut lits, visit, 0)
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
                            // Cell-dependent: tainted, so accumulation
                            // overflow (e.g. count exceeding range) is
                            // detected like any other relation-derived op.
                            acc = acc.add(&term.with_taint(true), bw);
                        }
                        let _ = &one;
                        // Relation-derived: tainted (overflow-prohibited).
                        acc.with_taint(true)
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
                                let term =
                                    c.choice(cell, &IntCircuit::zero(&self.ctx)).with_taint(true);
                                acc = acc.add(&term, bw);
                            }
                        }
                        // Relation-derived: tainted (overflow-prohibited).
                        acc.with_taint(true)
                    }
                    CastToIntOp::Bits => {
                        // Bit-vector value with signed MSB weight:
                        // Σ weight(v) where weight(v) = -2^(W-1) for the
                        // top atom (v = W-1, the MSB) and +2^v otherwise.
                        // W = the top atom + 1 is derived from the bound
                        // set itself; atoms are named by value.
                        let mut positions: Vec<(i64, usize)> = Vec::new();
                        let mut max_val: i64 = -1;
                        for (val, ts) in self.bounds.int_bounds() {
                            max_val = max_val.max(val);
                            for idx in ts.index_view().iter() {
                                positions.push((val, idx as usize));
                            }
                        }
                        positions.sort_by_key(|p| p.1);
                        let top = max_val; // W - 1
                        let mut acc = IntCircuit::constant(0, bw, &self.ctx);
                        for &(val, pos) in &positions {
                            let Some(weight) = crate::int::bit_weight(val, top) else {
                                continue;
                            };
                            if let Some(cell) = m.get(pos) {
                                let c = IntCircuit::constant(weight, bw, &self.ctx);
                                let term =
                                    c.choice(cell, &IntCircuit::zero(&self.ctx)).with_taint(true);
                                acc = acc.add(&term, bw);
                            }
                        }
                        // Relation-derived: tainted (overflow-prohibited).
                        acc.with_taint(true)
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
                        // Membership-masked: cell-dependent, hence tainted
                        // (accumulation overflow must be detected).
                        Rc::new(t.bit_and(&mask).with_taint(true))
                    };
                    acc = acc.add(&t, bw);
                    Ok(())
                })?;
                // Relation-quantified sum: tainted (overflow-prohibited).
                acc.with_taint(true)
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
        self.stats.formula_refs += 1;
        // Memoize composite formulas by (formula, free env values):
        // repeated nested expansions under different outer bindings
        // collapse to one translation each.
        // `ALLOY_NOFORMULAMEMO=1` disables the formula memo (diagnostics).
        let no_fmemo = std::env::var_os("ALLOY_NOFORMULAMEMO").is_some();
        let memoize = !no_fmemo && !matches!(arena.formula(f), FormulaNode::Constant(_));
        if memoize {
            let free = self.ffree_vars_of(arena, f);
            let key = MemoKey::new_formula(f, env, free.as_deref());
            if let Some(&b) = self.formula_memo.get(&key) {
                self.memo_hits += 1;
                return Ok(b);
            }
            self.memo_miss += 1;
            let b = self.formula_ref_uncached(arena, f, env)?;
            self.formula_memo.insert(key, b);
            return Ok(b);
        }
        self.formula_ref_uncached(arena, f, env)
    }

    /// Sorted free-variable ids of a formula. `None` = conservative
    /// fallback (quantifier domains included: omitting them collapses
    /// distinct instantiations — see `fol_memo` regression test).
    fn ffree_vars_of(&mut self, arena: &AstArena, f: crate::ast::FormulaId) -> Option<Vec<u32>> {
        if let Some(v) = self.ffree_memo.get(&f.0) {
            return v.clone();
        }
        let out: Option<Vec<u32>> = match arena.formula(f) {
            FormulaNode::Constant(_) => Some(Vec::new()),
            FormulaNode::Not(c) => self.ffree_vars_of(arena, *c),
            FormulaNode::Nary { children, .. } => {
                let mut acc = Vec::new();
                for &c in children {
                    acc.extend(self.ffree_vars_of(arena, c)?);
                }
                acc.sort_unstable();
                acc.dedup();
                Some(acc)
            }
            FormulaNode::Comparison { left, right, .. } => {
                let mut l = self.free_vars_of(arena, *left)?;
                let r = self.free_vars_of(arena, *right)?;
                l.extend(r);
                l.sort_unstable();
                l.dedup();
                Some(l)
            }
            FormulaNode::Multiplicity { expr, .. } => self.free_vars_of(arena, *expr),
            // Soft nodes are transparent for free variables.
            FormulaNode::MaxSome(e) | FormulaNode::MinSome(e) => self.free_vars_of(arena, *e),
            FormulaNode::SoftFact(inner) => self.ffree_vars_of(arena, *inner),
            FormulaNode::Quantified { decls, body, .. } => {
                // Free vars = body frees + DOMAIN frees, minus bound vars.
                // Dropping the domain part (e.g. `stu` in
                // `all c1: stu.courses | ...`) collapses distinct
                // instantiations: unsound sharing. A domain with
                // uncomputable frees poisons the whole set (full env).
                let mut acc = self.ffree_vars_of(arena, *body)?;
                let mut bound = Vec::new();
                for d in arena.decls(*decls) {
                    bound.push(d.variable.0);
                    acc.extend(self.free_vars_of(arena, d.expr)?);
                }
                acc.sort_unstable();
                acc.dedup();
                acc.retain(|v| !bound.contains(v));
                self.ffree_memo.insert(f.0, Some(acc.clone()));
                return Some(acc);
            }
            _ => None,
        };
        self.ffree_memo.insert(f.0, out.clone());
        out
    }

    fn formula_ref_uncached(
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
                // Cells absent from BOTH matrices contribute TRUE, so only the
                // union of present keys needs a term. For sparse relations this
                // avoids iterating the full (potentially huge) capacity; for
                // tiny matrices the direct sweep is cheaper than the sort.
                const UNION_THRESHOLD: usize = 64;
                let cap = l.dims().capacity();
                let use_union = cap > UNION_THRESHOLD;
                let mut acc = const_true();
                let term = |a: BoolRef, b: BoolRef| match op {
                    crate::ast::ExprCompOp::Equals => self.ctx.or(&[
                        self.ctx.and(&[a, b]),
                        self.ctx.and(&[self.ctx.not(a), self.ctx.not(b)]),
                    ]),
                    crate::ast::ExprCompOp::Subset => self.ctx.or(&[self.ctx.not(a), b]),
                };
                if use_union {
                    let mut keys: Vec<usize> = l
                        .iter()
                        .map(|(i, _)| i)
                        .chain(r.iter().map(|(i, _)| i))
                        .collect();
                    keys.sort_unstable();
                    keys.dedup();
                    for i in keys {
                        let a = l.get(i).unwrap_or_else(const_false);
                        let b = r.get(i).unwrap_or_else(const_false);
                        acc = self.ctx.and(&[acc, term(a, b)]);
                    }
                } else {
                    for i in 0..cap {
                        let a = l.get(i).unwrap_or_else(const_false);
                        let b = r.get(i).unwrap_or_else(const_false);
                        acc = self.ctx.and(&[acc, term(a, b)]);
                    }
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
                if !self.no_overflow {
                    return Ok(cmp);
                }
                // Gate: overflowing (or dividing-by-zero) assignments make
                // the comparison false, hence UNSAT when asserted.
                let bad = self.ctx.or(&[l.accum_overflow(), r.accum_overflow()]);
                if bad.is_const() && !bad.const_value() {
                    return Ok(cmp);
                }
                Ok(self.ctx.and(&[cmp, self.ctx.not(bad)]))
            }
            FormulaNode::Quantified { quant, decls, body } => {
                let decl_list = arena.decls(decls).to_vec();
                let mut refs: Vec<BoolRef> = Vec::new();
                self.iter_decls(arena, &decl_list, env, &mut |this, binding, lits| {
                    this.stats.quant_bodies += 1;
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
            // Soft sources (AlloyMax): record unit softs, yield true.
            // Constant cells fold (always-earned / never-earned need no
            // soft); MinSome records negated lits so the loop uniformly
            // maximizes.
            FormulaNode::MaxSome(e) => {
                let m = self.expr_matrix(arena, e, env)?;
                for (_, cell) in m.iter() {
                    if cell == const_false() || cell == const_true() {
                        continue;
                    }
                    self.softs.push(SoftEntry {
                        root: cell,
                        weight: 1,
                        minimize: false,
                    });
                }
                Ok(const_true())
            }
            FormulaNode::MinSome(e) => {
                let m = self.expr_matrix(arena, e, env)?;
                for (_, cell) in m.iter() {
                    if cell == const_false() || cell == const_true() {
                        continue;
                    }
                    self.softs.push(SoftEntry {
                        root: self.ctx.not(cell),
                        weight: 1,
                        minimize: true,
                    });
                }
                Ok(const_true())
            }
            FormulaNode::SoftFact(inner) => {
                let g = self.formula_ref(arena, inner, env)?;
                if !g.is_const() {
                    self.softs.push(SoftEntry {
                        root: g,
                        weight: 1,
                        minimize: false,
                    });
                }
                Ok(const_true())
            }
            FormulaNode::TemporalUnary { .. } => Err(TranslateError::UnsupportedTemporal),
            FormulaNode::TemporalBinary { .. } => Err(TranslateError::UnsupportedTemporal),
        }
    }
}
