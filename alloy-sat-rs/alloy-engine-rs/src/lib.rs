//! alloy-engine-rs: the Rust Alloy engine behind `--engine rust`.
//!
//! Wire format v1 ("ARE1" problem / "ASAT"/"AUNSAT"/"AERR" answer), a
//! topologically ordered node DAG mirroring [`alloy_kodkod_rs::ast`] enums:
//!
//! ```text
//! problem := "ARE1" bitwidth:u8 atoms rels vars nodes root:u32
//!   atoms  := n:u32 (len:u16 utf8)*
//!   rels   := n:u32 (len:u16 utf8 arity:u8 nLo:u32 lo* nUp:u32 up*)*
//!             // tuple indices as zigzag i64 varints; lower==upper => exact
//!   vars   := n:u32 (len:u16 utf8 arity:u8)*        // VarId = index
//!   nodes  := n:u32 node*                           // children precede parents
//!   node   := tag:varint payload...
//! ```
//!
//! Tags (varint), payload shapes — ids are u32 varints, ops are u8:
//! - formula 0..: 0 Const{v} | 1 Not{f} | 2 Nary{op f*} | 3 Comp{op e e}
//!   | 4 IntComp{op i i} | 5 Quant{q decls f} | 6 Mult{mult e}
//! - expr 32..: 32 Rel{r} | 33 Var{v} | 34 Const{c} | 35 Unary{op e}
//!   | 36 Nary{op e*} | 37 If{f e e} | 38 Project{e i*} | 39 Compr{decls f}
//!   | 40 FromInt{i}
//! - int 64..: 64 Const{zz} | 65 Cast{op e} | 66 Bin{op i i} | 67 If{f i i}
//!   | 68 Sum{decls i}
//! - decls 96..: 96 List{n (mult var e)*}
//!
//! Answer: `"ASAT"` + per-relation tuples in request order (`n:u32 zz*`)
//! | `"AUNSAT"` | `"AERR"` len:u16 msg.

#[cfg(feature = "jni")]
mod ffi;

use std::sync::Arc;

use alloy_kodkod_rs::ast::*;
use alloy_kodkod_rs::bounds::Bounds;
use alloy_kodkod_rs::relation::RelationPool;
use alloy_kodkod_rs::solver::{Solver, SolverOptions};
use alloy_kodkod_rs::tuple::Tuple;
use alloy_kodkod_rs::tupleset::TupleSet;
use alloy_kodkod_rs::universe::Universe;

// ---------------------------------------------------------------------------
// C ABI (always available)
// ---------------------------------------------------------------------------

/// Solve a wire-format problem; returns an allocated answer buffer
/// (8-byte LE length prefix + payload). Release with
/// `alloy_engine_free_buffer`.
///
/// # Safety
/// `problem` must point to `len` readable bytes.
#[no_mangle]
pub unsafe extern "C" fn alloy_engine_solve(problem: *const u8, len: usize) -> *mut u8 {
    let answer = if problem.is_null() {
        error_answer_public("null problem buffer")
    } else {
        let input = std::slice::from_raw_parts(problem, len);
        solve_wire(input)
    };
    to_length_prefixed(answer)
}

/// # Safety
/// `buf` must be a pointer handed out by [`alloy_engine_solve`] (or null).
#[no_mangle]
pub unsafe extern "C" fn alloy_engine_free_buffer(buf: *mut u8) {
    if buf.is_null() {
        return;
    }
    let len = usize::from_le_bytes(std::slice::from_raw_parts(buf, 8).try_into().unwrap());
    let slice = std::slice::from_raw_parts_mut(buf, len + 8);
    drop(Box::from_raw(slice as *mut [u8]));
}

unsafe fn to_length_prefixed(payload: Vec<u8>) -> *mut u8 {
    let mut out = Vec::with_capacity(payload.len() + 8);
    out.extend_from_slice(&(payload.len() as u64).to_le_bytes());
    out.extend_from_slice(&payload);
    let boxed = out.into_boxed_slice();
    let ptr = boxed.as_ptr();
    std::mem::forget(boxed);
    ptr as *mut u8
}

pub const PROBLEM_MAGIC: &[u8; 4] = b"ARE1";
/// v2: adds a solver-options byte (+threads) and, for dynamic
/// decomposition, partial-relation marks + symbolic bound entries.
pub const PROBLEM_MAGIC_V2: &[u8; 4] = b"ARE2";
pub const ANSWER_SAT: &[u8; 4] = b"ASAT";
pub const ANSWER_UNSAT: &[u8; 4] = b"AUNS";
pub const ANSWER_ERR: &[u8; 4] = b"AERR";

/// Decomposition mode carried by ARE2 options (bits 1..2).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Decompose {
    None,
    Static,
    Parallel,
    Dynamic,
}

impl Decompose {
    fn from_u8(v: u8) -> Result<Decompose, String> {
        match v {
            0 => Ok(Decompose::None),
            1 => Ok(Decompose::Static),
            2 => Ok(Decompose::Parallel),
            3 => Ok(Decompose::Dynamic),
            x => Err(format!("unknown decompose mode {x}")),
        }
    }
}

/// Solver options transported by ARE2 (Java A4Options mirror).
#[derive(Clone, Copy, Debug)]
pub struct WireOptions {
    pub skolemize: bool,
    pub decompose: Decompose,
    pub max_threads: usize,
}

impl Default for WireOptions {
    fn default() -> Self {
        WireOptions {
            skolemize: false,
            decompose: Decompose::None,
            max_threads: 1,
        }
    }
}

// ---------------------------------------------------------------------------
// Minimal cursor codec (no external deps)
// ---------------------------------------------------------------------------

#[derive(Default)]
struct Writer(Vec<u8>);

impl Writer {
    fn bytes(&mut self, b: &[u8]) {
        self.0.extend_from_slice(b);
    }
    #[allow(dead_code)]
    fn u8(&mut self, v: u8) {
        self.0.push(v);
    }
    fn str16(&mut self, s: &str) {
        let b = s.as_bytes();
        assert!(b.len() <= u16::MAX as usize, "string too long");
        self.0.extend_from_slice(&(b.len() as u16).to_le_bytes());
        self.0.extend_from_slice(b);
    }
    fn var(&mut self, mut v: u64) {
        loop {
            let byte = (v & 0x7f) as u8;
            v >>= 7;
            if v == 0 {
                self.0.push(byte);
                break;
            }
            self.0.push(byte | 0x80);
        }
    }
    /// Zigzag-encoded signed varint.
    fn svar(&mut self, v: i64) {
        let z = ((v << 1) ^ (v >> 63)) as u64;
        self.var(z);
    }
}

struct Reader<'a> {
    buf: &'a [u8],
    pos: usize,
}

impl<'a> Reader<'a> {
    fn new(buf: &'a [u8]) -> Reader<'a> {
        Reader { buf, pos: 0 }
    }
    fn take(&mut self, n: usize) -> Result<&'a [u8], String> {
        if self.buf.len() < self.pos + n {
            return Err("truncated wire input".into());
        }
        let s = &self.buf[self.pos..self.pos + n];
        self.pos += n;
        Ok(s)
    }
    fn u8(&mut self) -> Result<u8, String> {
        Ok(self.take(1)?[0])
    }
    fn bytes(&mut self, n: usize) -> Result<&'a [u8], String> {
        self.take(n)
    }
    fn str16(&mut self) -> Result<String, String> {
        let len = u16::from_le_bytes(self.take(2)?.try_into().unwrap()) as usize;
        let raw = self.take(len)?;
        String::from_utf8(raw.to_vec()).map_err(|_| "invalid utf-8 in wire input".to_string())
    }
    fn var(&mut self) -> Result<u64, String> {
        let mut out = 0u64;
        let mut shift = 0;
        loop {
            let b = self.u8()?;
            out |= u64::from(b & 0x7f) << shift;
            if b & 0x80 == 0 {
                return Ok(out);
            }
            shift += 7;
            if shift > 63 {
                return Err("varint overflow".into());
            }
        }
    }
    fn u32v(&mut self) -> Result<u32, String> {
        let v = self.var()?;
        u32::try_from(v).map_err(|_| "u32 overflow".to_string())
    }
    fn svar(&mut self) -> Result<i64, String> {
        let z = self.var()?;
        Ok(((z >> 1) as i64) ^ -((z & 1) as i64))
    }
}

// ---------------------------------------------------------------------------
// Problem decoding into AstArena/Bounds
// ---------------------------------------------------------------------------

/// A decoded problem ready for the solver facade.
pub struct Problem {
    pub arena: AstArena,
    pub bounds: Bounds,
    pub bitwidth: u32,
    pub formula: FormulaId,
    pub relation_names: Vec<String>,
    pub relation_ids: Vec<alloy_kodkod_rs::RelationId>,
    /// ARE2 options (defaults for ARE1 inputs).
    pub options: WireOptions,
    /// Dynamic decomposition: stage-1 relations (indices into
    /// `relation_ids`).
    pub partials: Vec<u32>,
    /// Dynamic decomposition: symbolic bounds as
    /// `(relation index, is_upper, expr node id)`. Node ids refer to the
    /// decoded DAG positions.
    pub symbounds: Vec<(u32, bool, u32)>,
    /// Node position -> arena [`alloy_kodkod_rs::ast::ExprId`] for every
    /// expression node of the DAG (used to resolve symbolic bounds).
    pub expr_by_node: std::collections::HashMap<u32, alloy_kodkod_rs::ast::ExprId>,
}

fn op_err(tag: &'static str, got: u8) -> String {
    format!("unsupported {tag} operator code {got}")
}

/// Decode a wire-format problem buffer (ARE1 or ARE2).
pub fn decode_problem(input: &[u8]) -> Result<Problem, String> {
    let mut r = Reader::new(input);
    let magic_bytes = r.bytes(4)?;
    let is_v2 = match magic_bytes {
        m if m == PROBLEM_MAGIC => false,
        m if m == PROBLEM_MAGIC_V2 => true,
        _ => return Err("bad magic (expected ARE1/ARE2)".into()),
    };
    let bitwidth = r.u8()? as u32;
    if !(1..=30).contains(&bitwidth) {
        return Err(format!("bitwidth {bitwidth} out of range 1..=30"));
    }
    let mut options = WireOptions::default();
    if is_v2 {
        let flags = r.u8()?;
        options.skolemize = flags & 1 != 0;
        options.decompose = Decompose::from_u8((flags >> 1) & 0b11)?;
        options.max_threads = r.var()? as usize;
    }

    // Universe atoms (order defines tuple indices).
    let n_atoms = r.u32v()? as usize;
    let mut atoms: Vec<String> = Vec::with_capacity(n_atoms);
    for _ in 0..n_atoms {
        atoms.push(r.str16()?);
    }
    let refs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
    let universe = Universe::new(refs).map_err(|e| format!("universe: {e}"))?;
    let pool = Arc::new(RelationPool::new());
    let mut arena = AstArena::with_pool(Arc::clone(&pool));
    let mut bounds = Bounds::new(&universe, &pool);

    // Relations with bounds. Relation ids follow request order.
    let n_rels = r.u32v()? as usize;
    let mut relation_names: Vec<String> = Vec::with_capacity(n_rels);
    let mut relation_ids: Vec<alloy_kodkod_rs::RelationId> = Vec::with_capacity(n_rels);
    for _ in 0..n_rels {
        let name = r.str16()?;
        let arity = r.u8()? as u32;
        let read_ts = |r: &mut Reader| -> Result<TupleSet, String> {
            let n = r.u32v()? as usize;
            let mut ts = TupleSet::new(&universe, arity).map_err(|e| format!("tupleset: {e}"))?;
            for _ in 0..n {
                let idx = r.svar()?;
                ts.insert_index(idx);
            }
            Ok(ts)
        };
        let lower = read_ts(&mut r)?;
        let upper = read_ts(&mut r)?;
        let rid = arena.relation(&name, arity);
        if lower.len() == upper.len() && lower.index_view() == upper.index_view() {
            bounds
                .bound_exactly(rid, &upper)
                .map_err(|e| format!("bound {name}: {e}"))?;
        } else {
            // A relation whose value may vary: required by the temporal
            // expansion / decomposition pipelines.
            arena.set_variable(rid, true);
            bounds
                .bound(rid, &lower, &upper)
                .map_err(|e| format!("bound {name}: {e}"))?;
        }
        relation_names.push(name);
        relation_ids.push(rid);
    }

    // Variables (interned by name+arity; VarId = table index).
    let n_vars = r.u32v()? as usize;
    let mut var_ids: Vec<VarId> = Vec::with_capacity(n_vars);
    for _ in 0..n_vars {
        let name = r.str16()?;
        let arity = r.u8()? as u32;
        var_ids.push(arena.variable_nary(&name, arity));
    }

    // Node DAG (children before parents).
    let n_nodes = r.u32v()? as usize;
    let mut formulas: Vec<Option<FormulaId>> = Vec::with_capacity(n_nodes);
    let mut exprs: Vec<Option<ExprId>> = Vec::with_capacity(n_nodes);
    let mut ints: Vec<Option<IntId>> = Vec::with_capacity(n_nodes);
    let mut decls_list: Vec<Option<DeclsId>> = Vec::with_capacity(n_nodes);
    macro_rules! id {
        ($vec:expr, $idx:expr) => {
            match $vec.get($idx as usize).copied().flatten() {
                Some(x) => x,
                None => return Err(format!("node #{} missing/forward", $idx)),
            }
        };
    }
    macro_rules! ok {
        ($e:expr) => {
            $e.map_err(|e| format!("ast build: {e}"))?
        };
    }
    for _ in 0..n_nodes {
        let tag = r.var()?;
        match tag {
            0 => {
                let v = r.u8()? != 0;
                formulas.push(Some(arena.bool_formula(v)));
                exprs.push(None);
                ints.push(None);
                decls_list.push(None);
            }
            1 => {
                let c = r.u32v()?;
                let inner = id!(formulas, c);
                formulas.push(Some(arena.not(inner)));
                exprs.push(None);
                ints.push(None);
                decls_list.push(None);
            }
            2 => {
                let op = match r.u8()? {
                    0 => FormulaBinOp::And,
                    1 => FormulaBinOp::Or,
                    x => return Err(op_err("formula-nary", x)),
                };
                let n = r.u32v()? as usize;
                let mut kids = Vec::with_capacity(n);
                for _ in 0..n {
                    let c = r.u32v()?;
                    kids.push(id!(formulas, c));
                }
                formulas.push(Some(arena.compose_formula(op, &kids)));
                exprs.push(None);
                ints.push(None);
                decls_list.push(None);
            }
            3 => {
                let op = match r.u8()? {
                    0 => ExprCompOp::Subset,
                    1 => ExprCompOp::Equals,
                    x => return Err(op_err("expr-comparison", x)),
                };
                let l = r.u32v()?;
                let rt = r.u32v()?;
                let le = id!(exprs, l);
                let re = id!(exprs, rt);
                formulas.push(Some(ok!(arena.comparison(op, le, re))));
                exprs.push(None);
                ints.push(None);
                decls_list.push(None);
            }
            4 => {
                let op = match r.u8()? {
                    0 => IntCompOp::Eq,
                    1 => IntCompOp::Neq,
                    2 => IntCompOp::Lt,
                    3 => IntCompOp::Lte,
                    4 => IntCompOp::Gt,
                    5 => IntCompOp::Gte,
                    x => return Err(op_err("int-comparison", x)),
                };
                let l = r.u32v()?;
                let rt = r.u32v()?;
                let li = id!(ints, l);
                let ri = id!(ints, rt);
                formulas.push(Some(arena.int_comparison(op, li, ri)));
                exprs.push(None);
                ints.push(None);
                decls_list.push(None);
            }
            5 => {
                let q = match r.u8()? { 0 => Quantifier::All, 1 => Quantifier::Some, x => return Err(format!("unsupported quantifier kind {x} (lone/no/one not supported by the Rust engine yet)")) };
                let d = r.u32v()?;
                let b = r.u32v()?;
                let dd = id!(decls_list, d);
                let bb = id!(formulas, b);
                formulas.push(Some(arena.quantified(q, dd, bb)));
                exprs.push(None);
                ints.push(None);
                decls_list.push(None);
            }
            6 => {
                let m = match r.u8()? {
                    0 => Multiplicity::Some,
                    1 => Multiplicity::Lone,
                    2 => Multiplicity::One,
                    x => return Err(op_err("multiplicity", x)),
                };
                let e = r.u32v()?;
                let ee = id!(exprs, e);
                formulas.push(Some(ok!(arena.multiplicity_formula(m, ee))));
                exprs.push(None);
                ints.push(None);
                decls_list.push(None);
            }
            32 => {
                let rel = r.u32v()?;
                let rid = *relation_ids
                    .get(rel as usize)
                    .ok_or_else(|| format!("relation index {rel} out of range"))?;
                exprs.push(Some(arena.expr_relation(rid)));
                formulas.push(None);
                ints.push(None);
                decls_list.push(None);
            }
            33 => {
                let v = r.u32v()?;
                let vid = *var_ids
                    .get(v as usize)
                    .ok_or_else(|| format!("variable index {v} out of range"))?;
                exprs.push(Some(arena.expr_variable(vid)));
                formulas.push(None);
                ints.push(None);
                decls_list.push(None);
            }
            34 => {
                let c = match r.u8()? {
                    0 => ConstantExpr::Univ,
                    1 => ConstantExpr::Iden,
                    2 => ConstantExpr::Empty,
                    3 => ConstantExpr::Ints,
                    x => return Err(op_err("const-expr", x)),
                };
                exprs.push(Some(arena.constant(c)));
                formulas.push(None);
                ints.push(None);
                decls_list.push(None);
            }
            35 => {
                let op = match r.u8()? {
                    0 => UnaryExprOp::Transpose,
                    1 => UnaryExprOp::Closure,
                    2 => UnaryExprOp::ReflexiveClosure,
                    x => return Err(op_err("unary-expr", x)),
                };
                let c = r.u32v()?;
                let ce = id!(exprs, c);
                exprs.push(Some(ok!(arena.unary_expr(op, ce))));
                formulas.push(None);
                ints.push(None);
                decls_list.push(None);
            }
            36 => {
                let op = match r.u8()? {
                    0 => BinaryOp::Union,
                    1 => BinaryOp::Intersection,
                    2 => BinaryOp::Override,
                    3 => BinaryOp::Difference,
                    4 => BinaryOp::Product,
                    5 => BinaryOp::Join,
                    x => return Err(op_err("expr-nary", x)),
                };
                let n = r.u32v()? as usize;
                let mut kids = Vec::with_capacity(n);
                for _ in 0..n {
                    let c = r.u32v()?;
                    kids.push(id!(exprs, c));
                }
                exprs.push(Some(ok!(arena.compose_expr(op, &kids))));
                formulas.push(None);
                ints.push(None);
                decls_list.push(None);
            }
            37 => {
                let cf = r.u32v()?;
                let te = r.u32v()?;
                let ee = r.u32v()?;
                let c = id!(formulas, cf);
                let t = id!(exprs, te);
                let e = id!(exprs, ee);
                exprs.push(Some(ok!(arena.if_expr(c, t, e))));
                formulas.push(None);
                ints.push(None);
                decls_list.push(None);
            }
            38 => {
                let src = r.u32v()?;
                let se = id!(exprs, src);
                let n = r.u32v()? as usize;
                let mut cols = Vec::with_capacity(n);
                for _ in 0..n {
                    let c = r.u32v()?;
                    cols.push(id!(ints, c));
                }
                exprs.push(Some(ok!(arena.project(se, &cols))));
                formulas.push(None);
                ints.push(None);
                decls_list.push(None);
            }
            39 => {
                let d = r.u32v()?;
                let b = r.u32v()?;
                let dd = id!(decls_list, d);
                let bb = id!(formulas, b);
                exprs.push(Some(ok!(arena.comprehension(dd, bb))));
                formulas.push(None);
                ints.push(None);
                decls_list.push(None);
            }
            40 => {
                let c = r.u32v()?;
                let ci = id!(ints, c);
                exprs.push(Some(arena.from_int(ci)));
                formulas.push(None);
                ints.push(None);
                decls_list.push(None);
            }
            64 => {
                let v = r.svar()?;
                ints.push(Some(arena.int_constant(v)));
                formulas.push(None);
                exprs.push(None);
                decls_list.push(None);
            }
            65 => {
                let op = match r.u8()? {
                    0 => CastToIntOp::Cardinality,
                    1 => CastToIntOp::Sum,
                    x => return Err(op_err("cast-to-int", x)),
                };
                let c = r.u32v()?;
                let ce = id!(exprs, c);
                ints.push(Some(ok!(arena.cast_to_int(op, ce))));
                formulas.push(None);
                exprs.push(None);
                decls_list.push(None);
            }
            66 => {
                let op = match r.u8()? {
                    0 => IntBinOp::Plus,
                    1 => IntBinOp::Minus,
                    2 => IntBinOp::Times,
                    3 => IntBinOp::Divide,
                    4 => IntBinOp::Modulo,
                    5 => IntBinOp::And,
                    6 => IntBinOp::Or,
                    7 => IntBinOp::Xor,
                    8 => IntBinOp::Shl,
                    9 => IntBinOp::Shr,
                    x => return Err(op_err("int-binop", x)),
                };
                let l = r.u32v()?;
                let rt = r.u32v()?;
                let li = id!(ints, l);
                let ri = id!(ints, rt);
                ints.push(Some(arena.binary_int(op, li, ri)));
                formulas.push(None);
                exprs.push(None);
                decls_list.push(None);
            }
            67 => {
                let cf = r.u32v()?;
                let te = r.u32v()?;
                let ee = r.u32v()?;
                let c = id!(formulas, cf);
                let t = id!(ints, te);
                let e = id!(ints, ee);
                ints.push(Some(arena.if_int(c, t, e)));
                formulas.push(None);
                exprs.push(None);
                decls_list.push(None);
            }
            68 => {
                let d = r.u32v()?;
                let b = r.u32v()?;
                let dd = id!(decls_list, d);
                let bb = id!(ints, b);
                ints.push(Some(arena.sum_int(dd, bb)));
                formulas.push(None);
                exprs.push(None);
                decls_list.push(None);
            }
            96 => {
                let n = r.u32v()? as usize;
                let mut list: Vec<Decl> = Vec::with_capacity(n);
                for _ in 0..n {
                    let mult = match r.u8()? {
                        0 => Multiplicity::Some,
                        1 => Multiplicity::Lone,
                        2 => Multiplicity::One,
                        3 => Multiplicity::Set,
                        x => return Err(op_err("decl-multiplicity", x)),
                    };
                    let v = r.u32v()?;
                    let e = r.u32v()?;
                    let vid = *var_ids
                        .get(v as usize)
                        .ok_or_else(|| format!("variable index {v} out of range"))?;
                    let ee = id!(exprs, e);
                    list.push(Decl {
                        mult,
                        variable: vid,
                        expr: ee,
                    });
                }
                decls_list.push(Some(arena.add_decls(list)));
                formulas.push(None);
                exprs.push(None);
                ints.push(None);
            }
            other => return Err(format!("unknown node tag {other}")),
        }
    }
    let root = r.u32v()?;
    let formula = id!(formulas, root);

    // ARE2 trailer: partial marks + symbolic bounds for dynamic decomposition.
    let mut partials = Vec::new();
    let mut symbounds = Vec::new();
    if is_v2 && options.decompose == Decompose::Dynamic {
        let n_partials = r.u32v()? as usize;
        for _ in 0..n_partials {
            let rel = r.u32v()?;
            if rel as usize >= relation_ids.len() {
                return Err(format!("partial relation index {rel} out of range"));
            }
            partials.push(rel);
        }
        let n_symb = r.u32v()? as usize;
        for _ in 0..n_symb {
            let rel = r.u32v()?;
            if rel as usize >= relation_ids.len() {
                return Err(format!("symbolic-bound relation index {rel} out of range"));
            }
            let side = match r.u8()? {
                0 => false,
                1 => true,
                x => return Err(format!("unknown symbolic-bound side {x}")),
            };
            let node = r.u32v()?;
            if node as usize >= n_nodes || exprs.get(node as usize).copied().flatten().is_none() {
                return Err(format!(
                    "symbolic bound references non-expression node #{node}"
                ));
            }
            symbounds.push((rel, side, node));
        }
    }

    if r.pos != input.len() {
        return Err("trailing bytes after problem".into());
    }

    let expr_by_node = exprs
        .iter()
        .enumerate()
        .filter_map(|(i, e)| e.map(|eid| (i as u32, eid)))
        .collect();

    Ok(Problem {
        arena,
        bounds,
        bitwidth,
        formula,
        relation_names,
        relation_ids,
        options,
        partials,
        symbounds,
        expr_by_node,
    })
}

/// Solve a decoded problem; returns the wire-format answer buffer.
pub fn solve_problem(problem: &mut Problem) -> Vec<u8> {
    match solve_problem_inner(problem) {
        Ok(Some(per_rel)) => {
            let mut w = Writer::default();
            w.bytes(ANSWER_SAT);
            for ts in per_rel {
                w.var(ts.len() as u64);
                for idx in ts.index_view().iter() {
                    w.svar(idx);
                }
            }
            w.0
        }
        Ok(None) => ANSWER_UNSAT.to_vec(),
        Err(msg) => {
            let mut w = Writer::default();
            w.bytes(ANSWER_ERR);
            w.str16(&msg);
            w.0
        }
    }
}

fn solve_problem_inner(problem: &mut Problem) -> Result<Option<Vec<TupleSet>>, String> {
    let options = SolverOptions {
        bitwidth: problem.bitwidth,
        skolemize: problem.options.skolemize,
        ..SolverOptions::default()
    };
    let solver = Solver::with_options(options);

    let solution = match problem.options.decompose {
        Decompose::None => solver
            .solve(&mut problem.arena, problem.formula, &problem.bounds)
            .map_err(|e| format!("translate/solve: {e}"))?,
        Decompose::Static => solver
            .solve_decomposed(&mut problem.arena, problem.formula, &problem.bounds)
            .map_err(|e| format!("decomposed solve: {e}"))?,
        Decompose::Parallel => {
            let threads = problem.options.max_threads.max(1);
            solver
                .solve_decomposed_parallel(
                    &mut problem.arena,
                    problem.formula,
                    &problem.bounds,
                    threads,
                )
                .map_err(|e| format!("parallel solve: {e}"))?
        }
        Decompose::Dynamic => solve_dynamic_problem(&solver, problem)?,
    };

    extract_answer_instances(problem, solution)
}

/// Dynamic two-stage decomposition over a wire problem (Iter 11): the ARE2
/// trailer supplies stage-1 partial marks and optional symbolic bounds.
fn solve_dynamic_problem(
    solver: &alloy_kodkod_rs::Solver,
    problem: &mut Problem,
) -> Result<alloy_kodkod_rs::solver::Solution, String> {
    use alloy_kodkod_rs::pardinus::PardinusBounds;

    if problem.partials.is_empty() {
        // Nothing sliceable: fall back to the plain pipeline.
        return solver
            .solve(&mut problem.arena, problem.formula, &problem.bounds)
            .map_err(|e| format!("translate/solve: {e}"));
    }
    // Re-map node ids to ExprIds for symbolic bounds.
    let expr_by_node = problem.expr_by_node.clone();
    let mut pb = PardinusBounds::new(problem.bounds.clone());
    for &rel in &problem.partials {
        pb = pb.with_partial(problem.relation_ids[rel as usize]);
    }
    for &(rel, upper, node) in &problem.symbounds {
        let eid = *expr_by_node
            .get(&node)
            .ok_or_else(|| format!("symbolic bound node #{node} not found in expression table"))?;
        pb = if upper {
            pb.with_symb_upper(problem.relation_ids[rel as usize], eid)
        } else {
            pb.with_symb_lower(problem.relation_ids[rel as usize], eid)
        };
    }
    solver
        .solve_dynamic(&mut problem.arena, problem.formula, &pb, 1)
        .map_err(|e| format!("dynamic solve: {e}"))
}

fn extract_answer_instances(
    problem: &Problem,
    solution: alloy_kodkod_rs::solver::Solution,
) -> Result<Option<Vec<TupleSet>>, String> {
    if !solution.satisfiable {
        return Ok(None);
    }
    let inst = solution.instance.as_ref().ok_or("SAT without instance")?;
    let mut out = Vec::with_capacity(problem.relation_names.len());
    for (i, name) in problem.relation_names.iter().enumerate() {
        match inst.find_relation_by_name(name) {
            Some(rid) => out.push(inst.tuples(rid).cloned().unwrap_or_else(|| {
                TupleSet::new(
                    inst.universe(),
                    problem.arena.relation_arity(problem.relation_ids[i]),
                )
                .expect("valid arity")
            })),
            None => out.push(TupleSet::new(inst.universe(), 1).expect("valid arity")),
        }
    }
    Ok(Some(out))
}

/// Solve a wire-format problem buffer; returns the wire-format answer.
pub fn solve_wire(input: &[u8]) -> Vec<u8> {
    match decode_problem(input) {
        Ok(mut p) => solve_problem(&mut p),
        Err(msg) => err_answer(&msg),
    }
}

fn err_answer(msg: &str) -> Vec<u8> {
    let mut w = Writer::default();
    w.bytes(ANSWER_ERR);
    w.str16(msg);
    w.0
}

/// Public alias used by the FFI layer for error answers.
pub fn error_answer_public(msg: &str) -> Vec<u8> {
    err_answer(msg)
}

#[allow(dead_code)]
fn unused(_: &Tuple) {}
