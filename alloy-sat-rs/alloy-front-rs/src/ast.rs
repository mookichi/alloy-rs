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
    /// The `int`/`Int` type used in declarations, with an optional
    /// per-occurrence bitwidth (`Int[8]`). `None` means the command's
    /// effective bitwidth (global `for N Int` scope, default 4).
    /// The effective problem bitwidth is the max of the default and
    /// every `Some(w)` in the module (A-plan: declaration-side widths).
    IntAtom(Option<u32>),
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
        }
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
    pub fn has_temporal(&self) -> bool {
        match self {
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
            Formula::Const(_) => false,
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
            Expr::Name(..) | Expr::Univ | Expr::None_ | Expr::Iden | Expr::IntAtom(_) => false,
            Expr::LetBind(binds, body) => {
                body.has_temporal() || binds.iter().any(|(_, e)| e.has_temporal())
            }
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
            IntExpr::Val(e, _) | IntExpr::SumOf(e, _) => e.has_temporal(),
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

pub struct Module {
    pub header: String,
    pub sigs: Vec<SigDecl>,
    pub facts: Vec<(Option<String>, Formula)>,
    pub paras: Vec<Para>,
    pub commands: Vec<Command>,
    pub opens: Vec<Open>,
}

impl Module {
    pub fn find_command(&self, name: &str) -> Option<usize> {
        self.commands.iter().position(|c| match &c.kind {
            CommandKind::Run(Some(n)) | CommandKind::Check(Some(n)) => n == name,
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
        // Check the command's referenced predicate body
        match &cmd.kind {
            CommandKind::Run(Some(name)) | CommandKind::Check(Some(name)) => {
                if let Some(para) = self.paras.iter().find(|p| p.name == *name) {
                    if para.body.has_temporal() {
                        return true;
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

/// Default bitwidth for a bare `Int` (no `for N Int`, no `Int[w]`).
pub const DEFAULT_INT_BITWIDTH: u32 = 4;

/// Effective problem bitwidth (A-plan, transitional global-max semantics):
/// the max of the command's default (`for N Int`, else 4) and every
/// per-occurrence `Int[w]` width in the module. Bare `Int` atoms and all
/// integer circuits observe this width.
pub fn effective_bitwidth(module: &Module, scope: &Scope) -> u32 {
    let base = scope.int_scope.unwrap_or(DEFAULT_INT_BITWIDTH).max(1);
    let mut acc = base;
    let mut visit_expr = Vec::new();
    for sd in &module.sigs {
        for d in &sd.fields {
            visit_expr.push(&d.expr);
        }
        if let Some(f) = &sd.fact {
            collect_int_widths_formula(f, &mut acc);
        }
    }
    for (_, f) in &module.facts {
        collect_int_widths_formula(f, &mut acc);
    }
    for p in &module.paras {
        collect_int_widths_formula(&p.body, &mut acc);
        if let Some(e) = &p.body_expr {
            visit_expr.push(e);
        }
        for d in &p.params {
            visit_expr.push(&d.expr);
        }
    }
    for e in visit_expr {
        collect_int_widths_expr(e, &mut acc);
    }
    acc
}

/// True when the module needs int atoms materialized in the universe
/// (A-plan lazy allocation). Int-as-a-*set* requires atoms: `Int`/`Int[w]`
/// in any relational position, `int`/`Int` names, set-position integer
/// literals (`x = 5`), `sig X in Int`, or an explicit `for N Int` scope.
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
        if sd.extends.as_deref() == Some("Int") {
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
    needs
}

fn collect_int_widths_expr(e: &Expr, acc: &mut u32) {
    match e {
        Expr::IntAtom(Some(w)) => *acc = (*acc).max(*w),
        Expr::IntAtom(None) => {}
        Expr::Name(..) | Expr::Univ | Expr::None_ | Expr::Iden => {}
        Expr::Bin(_, a, b) => {
            collect_int_widths_expr(a, acc);
            collect_int_widths_expr(b, acc);
        }
        Expr::Transpose(x) | Expr::TClosure(x) | Expr::RClosure(x) => {
            collect_int_widths_expr(x, acc);
        }
        Expr::Comprehension(ds, body) => {
            for d in ds {
                collect_int_widths_expr(&d.expr, acc);
            }
            collect_int_widths_formula(body, acc);
        }
        Expr::If(c, t, el) => {
            collect_int_widths_formula(c, acc);
            collect_int_widths_expr(t, acc);
            collect_int_widths_expr(el, acc);
        }
        Expr::Bracket(base, args) => {
            collect_int_widths_expr(base, acc);
            for a in args {
                collect_int_widths_expr(a, acc);
            }
        }
        Expr::Call(_, args, _) => {
            for a in args {
                collect_int_widths_expr(a, acc);
            }
        }
        Expr::ArrowMult(_, x) | Expr::LeadMult(_, x) => collect_int_widths_expr(x, acc),
        Expr::Prime(x) | Expr::AtExpr(x) => collect_int_widths_expr(x, acc),
        Expr::LetBind(binds, body) => {
            for (_, ex) in binds {
                collect_int_widths_expr(ex, acc);
            }
            collect_int_widths_expr(body, acc);
        }
    }
}

fn collect_int_widths_formula(f: &Formula, acc: &mut u32) {
    match f {
        Formula::Const(_) => {}
        Formula::Cmp(_, a, b, _) => {
            collect_int_widths_expr(a, acc);
            collect_int_widths_expr(b, acc);
        }
        Formula::IntCmp(_, a, b, _) => {
            collect_int_widths_intexpr(a, acc);
            collect_int_widths_intexpr(b, acc);
        }
        Formula::Quant(_, ds, body) => {
            for d in ds {
                collect_int_widths_expr(&d.expr, acc);
            }
            collect_int_widths_formula(body, acc);
        }
        Formula::Multi(_, e, _) => collect_int_widths_expr(e, acc),
        Formula::And(a, b)
        | Formula::Or(a, b)
        | Formula::Implies(a, b)
        | Formula::Iff(a, b)
        | Formula::Until(a, b)
        | Formula::Releases(a, b)
        | Formula::Since(a, b)
        | Formula::Triggered(a, b) => {
            collect_int_widths_formula(a, acc);
            collect_int_widths_formula(b, acc);
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
        | Formula::Consistently(x) => collect_int_widths_formula(x, acc),
        Formula::LetBind(binds, body) => {
            for (_, ex) in binds {
                collect_int_widths_expr(ex, acc);
            }
            collect_int_widths_formula(body, acc);
        }
        Formula::Call(_, args, _) => {
            for a in args {
                collect_int_widths_expr(a, acc);
            }
        }
    }
}

fn collect_int_widths_intexpr(ie: &IntExpr, acc: &mut u32) {
    match ie {
        IntExpr::Lit(..) => {}
        IntExpr::Card(e, _) | IntExpr::Val(e, _) | IntExpr::SumOf(e, _) => {
            collect_int_widths_expr(e, acc);
        }
        IntExpr::Sum(ds, body, _) => {
            for d in ds {
                collect_int_widths_expr(&d.expr, acc);
            }
            collect_int_widths_intexpr(body, acc);
        }
        IntExpr::Bin(_, a, b) => {
            collect_int_widths_intexpr(a, acc);
            collect_int_widths_intexpr(b, acc);
        }
    }
}

/// Marks `needs` when `e` references Int as a set (atoms required).
fn scan_expr_int_set(e: &Expr, needs: &mut bool) {
    if *needs {
        return;
    }
    match e {
        Expr::IntAtom(_) => *needs = true,
        Expr::Name(n, _) if n == "int" || n == "Int" || n.parse::<i64>().is_ok() => {
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

fn scan_formula_int_set(f: &Formula, needs: &mut bool) {
    if *needs {
        return;
    }
    match f {
        Formula::Const(_) => {}
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
    }
}

/// Marks `needs` when an integer expression draws on Int atoms
/// (only `Val`/`SumOf`/`Card` over Int-denoting sets do; literals,
/// plain cardinalities and arithmetic are pure circuits).
fn scan_intexpr_int_set(ie: &IntExpr, needs: &mut bool) {
    if *needs {
        return;
    }
    match ie {
        IntExpr::Lit(..) => {}
        IntExpr::Card(e, _) | IntExpr::Val(e, _) | IntExpr::SumOf(e, _) => {
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
