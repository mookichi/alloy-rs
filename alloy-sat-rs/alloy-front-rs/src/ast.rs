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
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Name(String, usize),
    Univ,
    None_,
    Iden,
    IntAtom, // the `int` type used in declarations
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
            Expr::Bin(_, a, b) => a.has_temporal() || b.has_temporal(),
            Expr::Transpose(x) | Expr::TClosure(x) | Expr::RClosure(x) => x.has_temporal(),
            Expr::Comprehension(decls, body) => {
                body.has_temporal() || decls.iter().any(|d| d.expr.has_temporal())
            }
            Expr::If(c, t, e) => c.has_temporal() || t.has_temporal() || e.has_temporal(),
            Expr::Bracket(b, args) => b.has_temporal() || args.iter().any(|a| a.has_temporal()),
            Expr::Call(_, args, _) => args.iter().any(|a| a.has_temporal()),
            Expr::ArrowMult(_, x) | Expr::LeadMult(_, x) => x.has_temporal(),
            Expr::Name(..) | Expr::Univ | Expr::None_ | Expr::Iden | Expr::IntAtom => false,
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
