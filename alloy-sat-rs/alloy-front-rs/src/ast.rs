//! Frontend AST: a faithful-but-small representation of the supported
//! Alloy subset, positioned for error reporting.

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum SigMult {
    None,
    Abstract,
    Lone,
    One,
    Some,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum SigRel {
    None,
    Extends,
    In,
}

#[derive(Debug, Clone)]
pub struct SigDecl {
    pub mult: SigMult,
    pub names: Vec<String>,
    pub extends: Option<String>,
    pub rel: SigRel,
    pub fields: Vec<Decl>,     // parsed as decls over implicit `this`
    pub fact: Option<Formula>, // sig-scoped fact block
    pub is_var: bool,          // `var sig` — atoms may change between states
}

#[derive(Debug, Clone, PartialEq)]
pub struct Decl {
    pub disj: bool,
    pub names: Vec<String>,
    pub expr: Expr,
    /// Byte position of the declaration for diagnostics.
    pub pos: usize,
    pub is_var: bool, // `var f: A -> B` — field may change between states
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BinOp {
    Union,
    Intersect,
    Difference,
    Override,
    Product,
    Join,
    DomainRestrict,
    RangeRestrict,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Name(String, usize),
    Univ,
    None_,
    Iden,
    /// The `int`/`Int` type used in declarations. Bit-vector model: `run
    /// ... for W Int` gives W atoms `{0, .., W-1}` (default W = 4) and
    /// W-bit circuits capped at 30 (`E = min(W, 30)`); `Int[w]` widths are
    /// no longer supported (parsed as a join, i.e. an arity error).
    IntAtom,
    /// Bitset of an integer literal: `Bits(n)` denotes `{i < W : bit i of
    /// the E-bit wrap of n is set}`, so `Bits(7)` is `{0, 1, 2}`. Built by
    /// the parser for `=`/`!=` with a numeric-literal side.
    Bits(i64, usize),
    Bin(BinOp, Box<Expr>, Box<Expr>),
    Transpose(Box<Expr>),
    TClosure(Box<Expr>),
    RClosure(Box<Expr>),
    Comprehension(Vec<Decl>, Box<Formula>),
    If(Box<Formula>, Box<Expr>, Box<Expr>),
    Bracket(Box<Expr>, Vec<Box<Expr>>), // e[a, b] == join chain
    /// Predicate/function call parsed positionally; resolved at lowering.
    Call(String, Vec<Expr>, usize),
    /// Multiplicity marker on the RIGHT operand of an arrow in a field
    /// declaration: `X -> some Y` constrains each X-row to have some Y.
    ArrowMult(Mult3, Box<Expr>),
    /// Leading multiplicity of a field declaration: `f: one X`.
    LeadMult(Mult3, Box<Expr>),
    /// Prime (next-state): `e'` or `after e`
    Prime(Box<Expr>),
    /// Static field access: `@field` or `^@field`
    AtExpr(Box<Expr>),
    /// Let binding in expression position: `let x = expr in expr`
    LetBind(Vec<(String, Expr)>, Box<Expr>),
}

/// Three-valued multiplicities used in declarations.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Mult3 {
    Some,
    Lone,
    One,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum QuantKind {
    All,
    Some,
    No,
    Lone,
    One,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum CmpKind {
    Eq,
    Neq,
    In,
    NotIn,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum IntBinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum IntCmpOp {
    Eq,
    Neq,
    Lt,
    Gt,
    Lte,
    Gte,
}

#[derive(Debug, Clone, PartialEq)]
pub enum IntExpr {
    Lit(i64, usize),
    Card(Box<Expr>, usize),
    Sum(Vec<Decl>, Box<IntExpr>, usize),
    Bin(IntBinOp, Box<IntExpr>, Box<IntExpr>),
    /// A set-typed expression used in integer position (variable, join,
    /// ...). Lowers via the SUM cast, mirroring Java's `typecheck_as_int`
    /// (Kodkod `ExprToIntCast` with `SUM`): a singleton's value, else the
    /// sum of the contained int atoms.
    Val(Box<Expr>, usize),
    /// Bit-vector value of a set in integer position (`{0, 1} * 2` reads
    /// `{0, 1}` as 3 = Σ 2^i). Lowers via the BITS cast: non-Int atoms
    /// contribute 0, bits at/above the circuit width are truncated.
    /// Unlike `sum e` (Σ atom values), this is Σ 2^value.
    BitsVal(Box<Expr>, usize),
    /// Explicit `sum e` over a unary set expression (Java: `sum A`,
    /// `sum A.f`, `sum {x: A | ...}`). Lowers identically to [`IntExpr::Val`];
    /// kept distinct so query routing treats it as integer-shaped.
    SumOf(Box<Expr>, usize),
}

impl IntExpr {
    /// True when this tree is int-typed without any set-to-int cast:
    /// literals, cardinalities, sums, and combinations thereof. `Val`
    /// (a set-typed operand) makes it false. `Card`/`Sum` are opaque int
    /// producers: their inner set expressions do not affect the outcome.
    pub fn int_typed(&self) -> bool {
        match self {
            IntExpr::Lit(..) => true,
            IntExpr::Card(..) => true,
            IntExpr::Sum(..) => true,
            IntExpr::Bin(_, a, b) => a.int_typed() && b.int_typed(),
            IntExpr::Val(..) => false,
            IntExpr::SumOf(..) => true,
            IntExpr::BitsVal(..) => true,
        }
    }

    /// True when the tree contains a `{...}` bit-value node.
    fn has_bitsval(&self) -> bool {
        match self {
            IntExpr::BitsVal(..) => true,
            IntExpr::Bin(_, a, b) => a.has_bitsval() || b.has_bitsval(),
            IntExpr::Sum(_, body, _) => body.has_bitsval(),
            _ => false,
        }
    }

    /// True when the tree has `+`/`-` with a bit-value descendant. A bare
    /// `{...}` nested under `*`/`/`/`%` does not count (integer-only shape).
    fn plusminus_bitsval(&self) -> bool {
        match self {
            IntExpr::Bin(op, a, b) => {
                if matches!(op, IntBinOp::Add | IntBinOp::Sub) {
                    a.has_bitsval()
                        || b.has_bitsval()
                        || a.plusminus_bitsval()
                        || b.plusminus_bitsval()
                } else {
                    a.plusminus_bitsval() || b.plusminus_bitsval()
                }
            }
            IntExpr::Sum(_, body, _) => body.plusminus_bitsval(),
            _ => false,
        }
    }

    /// Rewind-to-relational test for `=`/`!=` (and `:query` routing): a
    /// bare `{...}` side, or `+`/`-` combining a bit-value, keeps the
    /// legacy relational set reading. Pure `*`/`/`/`%` trees commit.
    pub(crate) fn rewind_bitsval_eq(&self) -> bool {
        matches!(self, IntExpr::BitsVal(..)) || self.plusminus_bitsval()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Formula {
    Const(bool),
    Cmp(CmpKind, Expr, Expr, usize),
    IntCmp(IntCmpOp, IntExpr, IntExpr, usize),
    Quant(QuantKind, Vec<Decl>, Box<Formula>),
    Multi(QuantKind, Expr, usize), // some/lone/one/no expr
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    Implies(Box<Formula>, Box<Formula>),
    Iff(Box<Formula>, Box<Formula>),
    Not(Box<Formula>),
    LetBind(Vec<(String, Expr)>, Box<Formula>),
    Call(String, Vec<Expr>, usize),
    /// AlloyMax `maxsome e`: maximize the set `e` (unit soft per cell).
    /// Hard meaning is true; declaration form (`maxsome x: T | F`) and
    /// priorities (`maxsome[n]`) are rejected at parse time.
    MaxSome(Box<Expr>),
    /// AlloyMax `minsome e`: minimize the set `e`.
    MinSome(Box<Expr>),
    /// AlloyMax `maxsome x: T | F` declaration form. Parsed (so sibling
    /// commands in the same file still run) but rejected at lowering:
    /// free set-valued witnesses are not supported yet.
    MaxSomeDecl(Vec<Decl>, Box<Formula>),
    /// `pin P`: the partial instance `P` embeds (existentially) here.
    /// `avoid P` parses as `Not(Pin)`. Lowered by desugaring to an
    /// existential over gensym label variables; never temporal.
    Pin(String, usize),
    // temporal operators (LTL)
    Always(Box<Formula>),
    Eventually(Box<Formula>),
    Until(Box<Formula>, Box<Formula>),
    Releases(Box<Formula>, Box<Formula>),
    Before(Box<Formula>),
    Historically(Box<Formula>),
    Once(Box<Formula>),
    Since(Box<Formula>, Box<Formula>),
    Triggered(Box<Formula>, Box<Formula>),
    Keeping(Box<Formula>),
    Goal(Box<Formula>),
    Restore(Box<Formula>),
    Initially(Box<Formula>),
    Regularly(Box<Formula>),
    Consistently(Box<Formula>),
}

impl Formula {
    /// Returns true if this formula or any subformula contains temporal operators.
    pub fn has_temporal(&self) -> bool {        match self {
            Formula::Always(_) | Formula::Eventually(_) => true,
            Formula::Until(_, _) | Formula::Releases(_, _) => true,
            Formula::Before(_) | Formula::Historically(_) | Formula::Once(_) => true,
            Formula::Since(_, _) | Formula::Triggered(_, _) => true,
            Formula::Keeping(_) | Formula::Goal(_) | Formula::Restore(_) => true,
            Formula::Initially(_) | Formula::Regularly(_) | Formula::Consistently(_) => true,
            Formula::Not(f) => f.has_temporal(),
            Formula::And(a, b)
            | Formula::Or(a, b)
            | Formula::Implies(a, b)
            | Formula::Iff(a, b) => a.has_temporal() || b.has_temporal(),
            Formula::Quant(_, decls, body) => {
                body.has_temporal() || decls.iter().any(|d| d.expr.has_temporal())
            }
            Formula::LetBind(binds, body) => {
                body.has_temporal() || binds.iter().any(|(_, e)| e.has_temporal())
            }
            Formula::Cmp(_, a, b, _) => a.has_temporal() || b.has_temporal(),
            Formula::IntCmp(_, a, b, _) => a.has_temporal() || b.has_temporal(),
            Formula::Multi(_, e, _) => e.has_temporal(),
            Formula::Call(_, args, _) => args.iter().any(|a| a.has_temporal()),
            Formula::MaxSomeDecl(ds, body) => {
                body.has_temporal() || ds.iter().any(|d| d.expr.has_temporal())
            }
            Formula::MaxSome(e) | Formula::MinSome(e) => e.has_temporal(),
            Formula::Pin(..) => false,
            Formula::Const(_) => false,
        }
    }

    /// Returns true if this formula or any subformula contains AlloyMax
    /// soft nodes (`maxsome` / `minsome`). Such commands must run through
    /// the optimizer, never the plain SAT path.
    pub fn has_soft(&self) -> bool {
        match self {
            Formula::MaxSome(_) | Formula::MinSome(_) => true,
            Formula::Not(f) => f.has_soft(),
            Formula::And(a, b)
            | Formula::Or(a, b)
            | Formula::Implies(a, b)
            | Formula::Iff(a, b) => a.has_soft() || b.has_soft(),
            Formula::Quant(_, decls, body) => {
                body.has_soft() || decls.iter().any(|d| d.expr.has_soft())
            }
            Formula::LetBind(binds, body) => {
                body.has_soft() || binds.iter().any(|(_, e)| e.has_soft())
            }
            Formula::Cmp(_, a, b, _) => a.has_soft() || b.has_soft(),
            Formula::IntCmp(_, a, b, _) => a.has_soft() || b.has_soft(),
            Formula::Multi(_, e, _) => e.has_soft(),
            Formula::Call(_, args, _) => args.iter().any(|a| a.has_soft()),
            // Declaration form is soft-bearing (it errors at lowering,
            // but must still route to the optimizer for the message).
            Formula::MaxSomeDecl(..) => true,
            Formula::Always(f)
            | Formula::Eventually(f)
            | Formula::Before(f)
            | Formula::Historically(f)
            | Formula::Once(f)
            | Formula::Keeping(f)
            | Formula::Goal(f)
            | Formula::Restore(f)
            | Formula::Initially(f)
            | Formula::Regularly(f)
            | Formula::Consistently(f) => f.has_soft(),
            Formula::Until(a, b)
            | Formula::Releases(a, b)
            | Formula::Since(a, b)
            | Formula::Triggered(a, b) => a.has_soft() || b.has_soft(),
            Formula::Pin(..) | Formula::Const(_) => false,
        }
    }
}

impl Expr {
    pub fn has_temporal(&self) -> bool {
        match self {
            Expr::Prime(_) => true,
            Expr::AtExpr(x) => x.has_temporal(),
            Expr::Bin(_, a, b) => a.has_temporal() || b.has_temporal(),
            Expr::Transpose(x) | Expr::TClosure(x) | Expr::RClosure(x) => x.has_temporal(),
            Expr::Comprehension(decls, body) => {
                body.has_temporal() || decls.iter().any(|d| d.expr.has_temporal())
            }
            Expr::If(c, t, e) => c.has_temporal() || t.has_temporal() || e.has_temporal(),
            Expr::Bracket(b, args) => b.has_temporal() || args.iter().any(|a| a.has_temporal()),
            Expr::Call(_, args, _) => args.iter().any(|a| a.has_temporal()),
            Expr::ArrowMult(_, x) | Expr::LeadMult(_, x) => x.has_temporal(),
            Expr::Name(..) | Expr::Univ | Expr::None_ | Expr::Iden | Expr::IntAtom | Expr::Bits(..) => false,
            Expr::LetBind(binds, body) => {
                body.has_temporal() || binds.iter().any(|(_, e)| e.has_temporal())
            }
        }
    }

    /// Expression-level soft scan (soft nodes live in formulas, but
    /// comprehensions and `if` conditions can nest them).
    pub fn has_soft(&self) -> bool {
        match self {
            Expr::Comprehension(decls, body) => {
                body.has_soft() || decls.iter().any(|d| d.expr.has_soft())
            }
            Expr::If(c, t, e) => c.has_soft() || t.has_soft() || e.has_soft(),
            Expr::Bin(_, a, b) => a.has_soft() || b.has_soft(),
            Expr::Transpose(x)
            | Expr::TClosure(x)
            | Expr::RClosure(x)
            | Expr::ArrowMult(_, x)
            | Expr::LeadMult(_, x)
            | Expr::AtExpr(x)
            | Expr::Prime(x) => x.has_soft(),
            Expr::Bracket(b, args) => b.has_soft() || args.iter().any(|a| a.has_soft()),
            Expr::Call(_, args, _) => args.iter().any(|a| a.has_soft()),
            Expr::LetBind(binds, body) => {
                body.has_soft() || binds.iter().any(|(_, e)| e.has_soft())
            }
            Expr::Name(..)
            | Expr::Univ
            | Expr::None_
            | Expr::Iden
            | Expr::IntAtom
            | Expr::Bits(..) => false,
        }
    }
}

impl IntExpr {
    pub fn has_temporal(&self) -> bool {
        match self {
            IntExpr::Card(e, _) => e.has_temporal(),
            IntExpr::Sum(decls, body, _) => {
                body.has_temporal() || decls.iter().any(|d| d.expr.has_temporal())
            }
            IntExpr::Bin(_, a, b) => a.has_temporal() || b.has_temporal(),
            IntExpr::Val(e, _) | IntExpr::SumOf(e, _) | IntExpr::BitsVal(e, _) => {
                e.has_temporal()
            }
            IntExpr::Lit(..) => false,
        }
    }

    /// Soft scan (soft nodes are formula-level; `IntExpr` can only nest
    /// them through comprehension bodies in decl domains).
    pub fn has_soft(&self) -> bool {
        match self {
            IntExpr::Card(e, _) => e.has_soft(),
            IntExpr::Sum(decls, body, _) => {
                body.has_soft() || decls.iter().any(|d| d.expr.has_soft())
            }
            IntExpr::Bin(_, a, b) => a.has_soft() || b.has_soft(),
            IntExpr::Val(e, _) | IntExpr::SumOf(e, _) | IntExpr::BitsVal(e, _) => e.has_soft(),
            IntExpr::Lit(..) => false,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Para {
    pub name: String,
    pub params: Vec<Decl>,
    pub body: Formula,
    /// Function bodies are expressions (`fun f[..]: T { e }`).
    pub body_expr: Option<Expr>,
    pub is_fun: bool,
    pub ret: Option<Expr>,
}

#[derive(Debug, Clone)]
pub enum CommandKind {
    Run(Option<String>),
    Check(Option<String>),
    Maximize {
        name: Option<String>,
        objective: OptSpec,
    },
    Minimize {
        name: Option<String>,
        objective: OptSpec,
    },
}

/// Optimization target of a `maximize`/`minimize` command (Rust-frontend
/// extension; Java Alloy has no such command).
#[derive(Debug, Clone, PartialEq)]
pub enum OptSpec {
    /// `: <intexpr>` — maximize/minimize an integer expression value.
    Int(IntExpr),
    /// `weights { rel: w, ... }` — maximize/minimize Σ w·#rel.
    Weights(Vec<(String, i64)>),
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ScopeEntry {
    Num(u32),
    Exactly(u32),
}

#[derive(Debug, Clone, Default)]
pub struct Scope {
    pub overall: Option<u32>,
    pub overall_exact: bool,
    pub entries: Vec<(String, ScopeEntry)>,
    pub int_scope: Option<u32>,
    pub steps: Option<u32>, // `for N steps` — temporal step count
}

#[derive(Debug, Clone)]
pub struct Command {
    pub kind: CommandKind,
    pub scope: Scope,
    pub pos: usize,
}

/// A parameter to an open declaration, e.g. `exactly T` in `open util/ordering[exactly T]`.
#[derive(Debug, Clone)]
pub enum OpenParam {
    Exactly(String),
    Set(String),
}

/// A parsed `open` declaration.
#[derive(Debug, Clone)]
pub struct Open {
    pub path: String,
    pub alias: String,
    pub params: Vec<OpenParam>,
}

/// Comparison shape of one `partial` block entry.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum PartialOp {
    /// `R = S`: exact (the relation equals the label set).
    Eq,
    /// `L in R` (lower) or `R in S` (upper), decided by which side is
    /// the bare relation reference.
    In,
}

/// One `partial` block entry: a comparison between a relation and a
/// label-set expression over the same columns.
#[derive(Debug, Clone)]
pub struct PartialEntry {
    pub op: PartialOp,
    pub left: Expr,
    pub right: Expr,
    pub pos: usize,
}

/// A parsed `partial name { ... }` block: a named partial instance
/// (diagram) usable via `pin name` / `avoid name` in formulas.
#[derive(Debug, Clone)]
pub struct PartialDef {
    pub name: String,
    pub entries: Vec<PartialEntry>,
    pub pos: usize,
}

pub struct Module {
    pub header: String,
    pub sigs: Vec<SigDecl>,
    pub facts: Vec<(Option<String>, Formula)>,
    /// AlloyMax `soft fact` entries: solved as soft constraints
    /// (unit soft on the lowered root), not hard facts.
    pub soft_facts: Vec<(Option<String>, Formula)>,
    pub paras: Vec<Para>,
    pub commands: Vec<Command>,
    pub opens: Vec<Open>,
    pub partials: Vec<PartialDef>,
}

impl Module {
    pub fn find_command(&self, name: &str) -> Option<usize> {
        self.commands.iter().position(|c| match &c.kind {
            CommandKind::Run(Some(n)) | CommandKind::Check(Some(n)) => n == name,
            CommandKind::Maximize { name: n, .. } | CommandKind::Minimize { name: n, .. } => {
                n.as_deref() == Some(name)
            }
            _ => false,
        })
    }

    /// Returns true if the command at `index` is a temporal model (has temporal
    /// operators in the formula).
    pub fn is_temporal_command(&self, index: usize) -> bool {
        let cmd = match self.commands.get(index) {
            Some(c) => c,
            None => return false,
        };
        // Check facts for temporal operators
        if self.facts.iter().any(|(_, f)| f.has_temporal()) {
            return true;
        }
        if self.soft_facts.iter().any(|(_, f)| f.has_temporal()) {
            return true;
        }
        // Check the command's referenced predicate body
        match &cmd.kind {
            CommandKind::Run(Some(name)) | CommandKind::Check(Some(name)) => {
                if let Some(para) = self.paras.iter().find(|p| p.name == *name) {
                    if para.body.has_temporal() {
                        return true;
                    }
                }
            }
            CommandKind::Maximize { name, .. } | CommandKind::Minimize { name, .. } => {
                if let Some(n) = name {
                    if let Some(para) = self.paras.iter().find(|p| p.name == *n) {
                        if para.body.has_temporal() {
                            return true;
                        }
                    }
                }
            }
            _ => {}
        }
        // Check command scope for 'steps' keyword
        if cmd.scope.steps.is_some() {
            return true;
        }
        false
    }

    /// Returns the step count for a temporal command, defaulting to 4.
    pub fn temporal_steps(&self, index: usize) -> usize {
        let cmd = match self.commands.get(index) {
            Some(c) => c,
            None => return 4,
        };
        cmd.scope.steps.map(|s| s as usize).unwrap_or(4)
    }
}

/// Default Int atom count for a bare `Int` (no `for N Int`).
pub const DEFAULT_INT_BITWIDTH: u32 = 4;

/// Effective problem bitwidth (bit-vector model): the circuit width `E =
/// min(W, 30)` where `W` is the Int atom count below. `Int[w]`
/// per-occurrence widths are no longer supported.
pub fn effective_bitwidth(_module: &Module, scope: &Scope) -> u32 {
    effective_int_count(scope).clamp(1, 30)
}

/// Effective Int atom count (bit-vector model): `W` from `for W Int`
/// (default 4), giving atoms `{0, .., W-1}`.
pub fn effective_int_count(scope: &Scope) -> u32 {
    scope.int_scope.unwrap_or(DEFAULT_INT_BITWIDTH).max(1)
}

/// True when the module needs int atoms materialized in the universe
/// (lazy allocation). Int-as-a-*set* requires atoms: `Int` in any
/// relational position, `int`/`Int`/`Signed` names, `MSB`, bitsets,
/// set-position integer literals (`x = 5`), `sig X in Int` (or `in
/// Signed`), or an explicit `for N Int` scope.
/// Pure integer-position use (`#A`, `sum`, `+ - * / %`, `IntCmp` over
/// non-Int sets) lowers to BV circuits only and needs no atoms.
pub fn module_needs_int_atoms(module: &Module, scope: &Scope) -> bool {
    // An explicit bitwidth request always materializes the range
    // (preserves `for 8 Int` + `#Int`/`Int`-query behavior).
    if scope.int_scope.is_some() {
        return true;
    }
    let mut needs = false;
    for sd in &module.sigs {
        if sd.extends.as_deref() == Some("Int") || sd.extends.as_deref() == Some("Signed") {
            return true;
        }
        for d in &sd.fields {
            scan_expr_int_set(&d.expr, &mut needs);
            if needs {
                return true;
            }
        }
        if let Some(f) = &sd.fact {
            scan_formula_int_set(f, &mut needs);
            if needs {
                return true;
            }
        }
    }
    for (_, f) in &module.facts {
        scan_formula_int_set(f, &mut needs);
        if needs {
            return true;
        }
    }
    for p in &module.paras {
        scan_formula_int_set(&p.body, &mut needs);
        if needs {
            return true;
        }
        if let Some(e) = &p.body_expr {
            scan_expr_int_set(e, &mut needs);
            if needs {
                return true;
            }
        }
        for d in &p.params {
            scan_expr_int_set(&d.expr, &mut needs);
            if needs {
                return true;
            }
        }
    }
    for pd in &module.partials {
        for e in &pd.entries {
            scan_expr_int_set(&e.left, &mut needs);
            if needs {
                return true;
            }
            scan_expr_int_set(&e.right, &mut needs);
            if needs {
                return true;
            }
        }
    }
    needs
}

/// Marks `needs` when `e` references Int as a set (atoms required).
pub(crate) fn scan_expr_int_set(e: &Expr, needs: &mut bool) {
    if *needs {
        return;
    }
    match e {
        Expr::IntAtom => *needs = true,
        // A bitset denotes Int atoms by construction.
        Expr::Bits(..) => *needs = true,
        Expr::Name(n, _) if n == "int" || n == "Int" || n == "Signed" || n == "MSB" || n.parse::<i64>().is_ok() => {
            *needs = true;
        }
        Expr::Name(..) | Expr::Univ | Expr::None_ | Expr::Iden => {}
        Expr::Bin(_, a, b) => {
            scan_expr_int_set(a, needs);
            scan_expr_int_set(b, needs);
        }
        Expr::Transpose(x) | Expr::TClosure(x) | Expr::RClosure(x) => {
            scan_expr_int_set(x, needs);
        }
        Expr::Comprehension(ds, body) => {
            for d in ds {
                scan_expr_int_set(&d.expr, needs);
            }
            scan_formula_int_set(body, needs);
        }
        Expr::If(c, t, el) => {
            scan_formula_int_set(c, needs);
            scan_expr_int_set(t, needs);
            scan_expr_int_set(el, needs);
        }
        Expr::Bracket(base, args) => {
            scan_expr_int_set(base, needs);
            for a in args {
                scan_expr_int_set(a, needs);
            }
        }
        Expr::Call(_, args, _) => {
            for a in args {
                scan_expr_int_set(a, needs);
            }
        }
        Expr::ArrowMult(_, x) | Expr::LeadMult(_, x) => scan_expr_int_set(x, needs),
        Expr::Prime(x) | Expr::AtExpr(x) => scan_expr_int_set(x, needs),
        Expr::LetBind(binds, body) => {
            for (_, ex) in binds {
                scan_expr_int_set(ex, needs);
            }
            scan_expr_int_set(body, needs);
        }
    }
}

pub(crate) fn scan_formula_int_set(f: &Formula, needs: &mut bool) {
    if *needs {
        return;
    }
    match f {
        Formula::Const(_) => {}
        // `pin` bodies live in `Module::partials`, walked at module level.
        Formula::Pin(..) => {}
        Formula::Cmp(_, a, b, _) => {
            scan_expr_int_set(a, needs);
            scan_expr_int_set(b, needs);
        }
        // Pure BV comparisons need no atoms; only a set-typed Int
        // operand (SUM-cast over Int atoms) does.
        Formula::IntCmp(_, a, b, _) => {
            scan_intexpr_int_set(a, needs);
            scan_intexpr_int_set(b, needs);
        }
        Formula::Quant(_, ds, body) => {
            for d in ds {
                scan_expr_int_set(&d.expr, needs);
            }
            scan_formula_int_set(body, needs);
        }
        Formula::Multi(_, e, _) => scan_expr_int_set(e, needs),
        Formula::And(a, b)
        | Formula::Or(a, b)
        | Formula::Implies(a, b)
        | Formula::Iff(a, b)
        | Formula::Until(a, b)
        | Formula::Releases(a, b)
        | Formula::Since(a, b)
        | Formula::Triggered(a, b) => {
            scan_formula_int_set(a, needs);
            scan_formula_int_set(b, needs);
        }
        Formula::Not(x)
        | Formula::Always(x)
        | Formula::Eventually(x)
        | Formula::Before(x)
        | Formula::Historically(x)
        | Formula::Once(x)
        | Formula::Keeping(x)
        | Formula::Goal(x)
        | Formula::Restore(x)
        | Formula::Initially(x)
        | Formula::Regularly(x)
        | Formula::Consistently(x) => scan_formula_int_set(x, needs),
        Formula::LetBind(binds, body) => {
            for (_, ex) in binds {
                scan_expr_int_set(ex, needs);
            }
            scan_formula_int_set(body, needs);
        }
        Formula::Call(_, args, _) => {
            for a in args {
                scan_expr_int_set(a, needs);
            }
        }
        Formula::MaxSome(e) | Formula::MinSome(e) => scan_expr_int_set(e, needs),
        Formula::MaxSomeDecl(ds, body) => {
            for d in ds {
                scan_expr_int_set(&d.expr, needs);
            }
            scan_formula_int_set(body, needs);
        }
    }
}

/// Marks `needs` when an integer expression draws on Int atoms
/// (only `Val`/`SumOf`/`Card` over Int-denoting sets do; literals,
/// plain cardinalities and arithmetic are pure circuits).
pub(crate) fn scan_intexpr_int_set(ie: &IntExpr, needs: &mut bool) {
    if *needs {
        return;
    }
    match ie {
        IntExpr::Lit(..) => {}
        IntExpr::Card(e, _) | IntExpr::Val(e, _) | IntExpr::SumOf(e, _) | IntExpr::BitsVal(e, _) => {
            scan_expr_int_set(e, needs);
        }
        IntExpr::Sum(ds, body, _) => {
            for d in ds {
                scan_expr_int_set(&d.expr, needs);
            }
            scan_intexpr_int_set(body, needs);
        }
        IntExpr::Bin(_, a, b) => {
            scan_intexpr_int_set(a, needs);
            scan_intexpr_int_set(b, needs);
        }
    }
}
