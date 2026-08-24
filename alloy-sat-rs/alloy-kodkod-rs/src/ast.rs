use std::collections::HashMap;
use std::sync::{Arc, OnceLock};

use crate::intset::Int;
use crate::relation::{RelationId, RelationPool};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct VarId(pub u32);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct ExprId(pub u32);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct IntId(pub u32);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct FormulaId(pub u32);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct DeclsId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinaryOp {
    Union,
    Intersection,
    Override,
    Difference,
    Product,
    Join,
}

impl BinaryOp {
    pub fn nary_allowed(self) -> bool {
        !matches!(self, BinaryOp::Join)
    }

    pub fn symbol(self) -> &'static str {
        match self {
            BinaryOp::Union => "+",
            BinaryOp::Intersection => "&",
            BinaryOp::Override => "++",
            BinaryOp::Difference => "-",
            BinaryOp::Product => "->",
            BinaryOp::Join => ".",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnaryExprOp {
    Transpose,
    Closure,
    ReflexiveClosure,
}

impl UnaryExprOp {
    pub fn symbol(self) -> &'static str {
        match self {
            UnaryExprOp::Transpose => "~",
            UnaryExprOp::Closure => "^",
            UnaryExprOp::ReflexiveClosure => "*",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConstantExpr {
    Univ,
    Iden,
    Empty,
    Ints,
}

impl ConstantExpr {
    pub fn arity(self) -> u32 {
        match self {
            ConstantExpr::Univ | ConstantExpr::Empty | ConstantExpr::Ints => 1,
            ConstantExpr::Iden => 2,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TemporalExprOp {
    Prime,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CastToIntOp {
    Cardinality,
    Sum,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IntBinOp {
    Plus,
    Minus,
    Times,
    Divide,
    Modulo,
    And,
    Or,
    Xor,
    Shl,
    Shr,
}

impl IntBinOp {
    pub fn symbol(self) -> &'static str {
        match self {
            IntBinOp::Plus => "+",
            IntBinOp::Minus => "-",
            IntBinOp::Times => "*",
            IntBinOp::Divide => "/",
            IntBinOp::Modulo => "%",
            IntBinOp::And => "&",
            IntBinOp::Or => "|",
            IntBinOp::Xor => "^",
            IntBinOp::Shl => "<<",
            IntBinOp::Shr => ">>>",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IntCompOp {
    Eq,
    Neq,
    Lt,
    Lte,
    Gt,
    Gte,
}

impl IntCompOp {
    pub fn symbol(self) -> &'static str {
        match self {
            IntCompOp::Eq => "=",
            IntCompOp::Neq => "!=",
            IntCompOp::Lt => "<",
            IntCompOp::Lte => "<=",
            IntCompOp::Gt => ">",
            IntCompOp::Gte => ">=",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExprCompOp {
    Subset,
    Equals,
}

impl ExprCompOp {
    pub fn symbol(self) -> &'static str {
        match self {
            ExprCompOp::Subset => "in",
            ExprCompOp::Equals => "=",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Quantifier {
    All,
    Some,
}

impl Quantifier {
    pub fn symbol(self) -> &'static str {
        match self {
            Quantifier::All => "all",
            Quantifier::Some => "some",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Multiplicity {
    Lone,
    One,
    Some,
    Set,
}

impl Multiplicity {
    pub fn symbol(self) -> &'static str {
        match self {
            Multiplicity::Lone => "lone",
            Multiplicity::One => "one",
            Multiplicity::Some => "some",
            Multiplicity::Set => "set",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FormulaBinOp {
    And,
    Or,
}

impl FormulaBinOp {
    pub fn symbol(self) -> &'static str {
        match self {
            FormulaBinOp::And => "and",
            FormulaBinOp::Or => "or",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TemporalFormulaOp {
    After,
    Always,
    Eventually,
    Before,
    Historically,
    Once,
}

impl TemporalFormulaOp {
    pub fn symbol(self) -> &'static str {
        match self {
            TemporalFormulaOp::After => "after",
            TemporalFormulaOp::Always => "always",
            TemporalFormulaOp::Eventually => "eventually",
            TemporalFormulaOp::Before => "before",
            TemporalFormulaOp::Historically => "historically",
            TemporalFormulaOp::Once => "once",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TemporalBinaryOp {
    Until,
    Releases,
    Since,
    Triggered,
}

impl TemporalBinaryOp {
    pub fn symbol(self) -> &'static str {
        match self {
            TemporalBinaryOp::Until => "until",
            TemporalBinaryOp::Releases => "releases",
            TemporalBinaryOp::Since => "since",
            TemporalBinaryOp::Triggered => "triggered",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Decl {
    pub mult: Multiplicity,
    pub variable: VarId,
    pub expr: ExprId,
}

#[derive(Debug)]
pub(crate) struct VariableData {
    pub name: Arc<str>,
    pub arity: u32,
}

#[derive(Clone, Debug)]
pub enum ExprNode {
    Relation(RelationId),
    Variable(VarId),
    Constant(ConstantExpr),
    Unary {
        op: UnaryExprOp,
        child: ExprId,
    },
    Temporal {
        op: TemporalExprOp,
        child: ExprId,
    },
    Binary {
        op: BinaryOp,
        left: ExprId,
        right: ExprId,
    },
    Nary {
        op: BinaryOp,
        children: Vec<ExprId>,
    },
    If {
        cond: FormulaId,
        then: ExprId,
        els: ExprId,
    },
    Project {
        expr: ExprId,
        columns: Vec<IntId>,
    },
    Comprehension {
        decls: DeclsId,
        body: FormulaId,
    },
    FromInt(IntId),
}

#[derive(Clone, Debug)]
pub enum IntNode {
    Constant(Int),
    OfExpr {
        op: CastToIntOp,
        expr: ExprId,
    },
    Binary {
        op: IntBinOp,
        left: IntId,
        right: IntId,
    },
    If {
        cond: FormulaId,
        then: IntId,
        els: IntId,
    },
    Sum {
        decls: DeclsId,
        body: IntId,
    },
}

#[derive(Clone, Debug)]
pub enum FormulaNode {
    Constant(bool),
    Not(FormulaId),
    Nary {
        op: FormulaBinOp,
        children: Vec<FormulaId>,
    },
    Comparison {
        op: ExprCompOp,
        left: ExprId,
        right: ExprId,
    },
    IntComparison {
        op: IntCompOp,
        left: IntId,
        right: IntId,
    },
    Quantified {
        quant: Quantifier,
        decls: DeclsId,
        body: FormulaId,
    },
    Multiplicity {
        mult: Multiplicity,
        expr: ExprId,
    },
    TemporalUnary {
        op: TemporalFormulaOp,
        child: FormulaId,
    },
    TemporalBinary {
        op: TemporalBinaryOp,
        left: FormulaId,
        right: FormulaId,
    },
}

#[derive(Debug)]
struct ExprSlot {
    node: ExprNode,
    arity: u32,
}

#[derive(Default, Debug)]
pub struct AstArena {
    pool: OnceLock<Arc<RelationPool>>,
    variables: Vec<VariableData>,
    variable_index: HashMap<(String, u32), VarId>,
    exprs: Vec<ExprSlot>,
    ints: Vec<IntNode>,
    formulas: Vec<FormulaNode>,
    decls_list: Vec<Vec<Decl>>,
}

#[derive(Debug, thiserror::Error)]
pub enum AstError {
    #[error("arity mismatch for {op}: {left} vs {right}")]
    ArityMismatch2 {
        op: &'static str,
        left: u32,
        right: u32,
    },
    #[error("join arity too low: {0} + {1} - 2 < 1")]
    JoinArityTooLow(u32, u32),
    #[error("{op} requires arity 2 but got {got}")]
    RequiresArity2 { op: &'static str, got: u32 },
    #[error("compose expects at least one argument")]
    ComposeEmpty,
    #[error("{op} is not n-ary")]
    NotNary { op: &'static str },
    #[error("projection needs at least one column")]
    ProjectEmpty,
    #[error("sum cast requires unary expression but got arity {0}")]
    SumRequiresUnary(u32),
    #[error("declaration arity mismatch: variable {var} vs expression {expr}")]
    DeclArityMismatch { var: u32, expr: u32 },
    #[error("multiplicity {mult} not allowed with arity {arity}")]
    DeclMultiplicity { mult: &'static str, arity: u32 },
    #[error("if-expression branches differ: {then} vs {els}")]
    BranchArityMismatch { then: u32, els: u32 },
    #[error("SET multiplicity is not a formula multiplicity")]
    SetIsNotFormulaMult,
}

impl AstArena {
    pub fn new() -> AstArena {
        AstArena {
            pool: OnceLock::new(),
            ..Default::default()
        }
    }

    pub fn with_pool(pool: Arc<RelationPool>) -> AstArena {
        let arena = AstArena::new();
        let _ = arena.pool.set(pool);
        arena
    }

    fn pool(&self) -> Arc<RelationPool> {
        Arc::clone(self.pool.get_or_init(|| Arc::new(RelationPool::new())))
    }

    pub fn shared_pool(&self) -> Arc<RelationPool> {
        self.pool()
    }

    pub fn relation(&self, name: &str, arity: u32) -> RelationId {
        self.pool().intern(name, arity)
    }

    pub fn relation_arity(&self, id: RelationId) -> u32 {
        self.pool().arity(id)
    }

    pub fn relation_name(&self, id: RelationId) -> String {
        self.pool().name(id).to_string()
    }

    pub fn set_skolem(&self, id: RelationId, value: bool) {
        self.pool().set_skolem(id, value);
    }

    pub fn is_skolem(&self, id: RelationId) -> bool {
        self.pool().is_skolem(id)
    }

    pub fn set_variable(&self, id: RelationId, value: bool) {
        self.pool().set_variable(id, value);
    }

    pub fn is_variable(&self, id: RelationId) -> bool {
        self.pool().is_variable(id)
    }

    pub fn variable(&mut self, name: &str) -> VarId {
        self.variable_nary(name, 1)
    }

    pub fn variable_nary(&mut self, name: &str, arity: u32) -> VarId {
        if let Some(&id) = self.variable_index.get(&(name.to_string(), arity)) {
            return id;
        }
        let id = VarId(self.variables.len() as u32);
        self.variables.push(VariableData {
            name: Arc::from(name),
            arity,
        });
        self.variable_index.insert((name.to_string(), arity), id);
        id
    }

    pub fn variable_arity(&self, id: VarId) -> u32 {
        self.variables[id.0 as usize].arity
    }

    pub fn variable_name(&self, id: VarId) -> &str {
        &self.variables[id.0 as usize].name
    }

    pub fn expr_relation(&mut self, id: RelationId) -> ExprId {
        self.push_expr(ExprNode::Relation(id), self.relation_arity(id))
    }

    pub fn expr_relation_named(&mut self, name: &str, arity: u32) -> ExprId {
        let rel = self.relation(name, arity);
        self.expr_relation(rel)
    }

    pub fn expr_variable(&mut self, id: VarId) -> ExprId {
        self.push_expr(ExprNode::Variable(id), self.variable_arity(id))
    }

    pub fn constant(&mut self, c: ConstantExpr) -> ExprId {
        self.push_expr(ExprNode::Constant(c), c.arity())
    }

    pub fn univ(&mut self) -> ExprId {
        self.constant(ConstantExpr::Univ)
    }

    pub fn iden(&mut self) -> ExprId {
        self.constant(ConstantExpr::Iden)
    }

    fn push_expr(&mut self, node: ExprNode, arity: u32) -> ExprId {
        let id = ExprId(self.exprs.len() as u32);
        self.exprs.push(ExprSlot { node, arity });
        id
    }

    pub fn expr(&self, id: ExprId) -> &ExprNode {
        &self.exprs[id.0 as usize].node
    }

    pub fn arity(&self, id: ExprId) -> u32 {
        self.exprs[id.0 as usize].arity
    }

    pub fn int(&self, id: IntId) -> &IntNode {
        &self.ints[id.0 as usize]
    }

    pub fn formula(&self, id: FormulaId) -> &FormulaNode {
        &self.formulas[id.0 as usize]
    }

    pub fn decls(&self, id: DeclsId) -> &[Decl] {
        &self.decls_list[id.0 as usize]
    }

    fn binary_arity(op: BinaryOp, l: u32, r: u32) -> Result<u32, AstError> {
        match op {
            BinaryOp::Union
            | BinaryOp::Intersection
            | BinaryOp::Override
            | BinaryOp::Difference => {
                if l != r {
                    Err(AstError::ArityMismatch2 {
                        op: op.symbol(),
                        left: l,
                        right: r,
                    })
                } else {
                    Ok(l)
                }
            }
            BinaryOp::Join => {
                if l + r < 3 {
                    Err(AstError::JoinArityTooLow(l, r))
                } else {
                    Ok(l + r - 2)
                }
            }
            BinaryOp::Product => Ok(l.checked_add(r).expect("arity overflow")),
        }
    }

    pub fn binary_expr(
        &mut self,
        op: BinaryOp,
        left: ExprId,
        right: ExprId,
    ) -> Result<ExprId, AstError> {
        let arity = Self::binary_arity(op, self.arity(left), self.arity(right))?;
        Ok(self.push_expr(ExprNode::Binary { op, left, right }, arity))
    }

    pub fn compose_expr(&mut self, op: BinaryOp, exprs: &[ExprId]) -> Result<ExprId, AstError> {
        match exprs.len() {
            0 => Err(AstError::ComposeEmpty),
            1 => Ok(exprs[0]),
            2 => self.binary_expr(op, exprs[0], exprs[1]),
            _ => {
                if !op.nary_allowed() {
                    return Err(AstError::NotNary { op: op.symbol() });
                }
                let first = self.arity(exprs[0]);
                for e in &exprs[1..] {
                    if self.arity(*e) != first {
                        return Err(AstError::ArityMismatch2 {
                            op: op.symbol(),
                            left: first,
                            right: self.arity(*e),
                        });
                    }
                }
                let arity = if op == BinaryOp::Product {
                    first * exprs.len() as u32
                } else {
                    first
                };
                Ok(self.push_expr(
                    ExprNode::Nary {
                        op,
                        children: exprs.to_vec(),
                    },
                    arity,
                ))
            }
        }
    }

    pub fn unary_expr(&mut self, op: UnaryExprOp, child: ExprId) -> Result<ExprId, AstError> {
        let arity = self.arity(child);
        if arity != 2 {
            return Err(AstError::RequiresArity2 {
                op: op.symbol(),
                got: arity,
            });
        }
        Ok(self.push_expr(ExprNode::Unary { op, child }, 2))
    }

    pub fn prime(&mut self, child: ExprId) -> ExprId {
        let arity = self.arity(child);
        self.push_expr(
            ExprNode::Temporal {
                op: TemporalExprOp::Prime,
                child,
            },
            arity,
        )
    }

    pub fn if_expr(
        &mut self,
        cond: FormulaId,
        then: ExprId,
        els: ExprId,
    ) -> Result<ExprId, AstError> {
        let t = self.arity(then);
        let e = self.arity(els);
        if t != e {
            return Err(AstError::BranchArityMismatch { then: t, els: e });
        }
        Ok(self.push_expr(ExprNode::If { cond, then, els }, t))
    }

    pub fn project(&mut self, expr: ExprId, columns: &[IntId]) -> Result<ExprId, AstError> {
        if columns.is_empty() {
            return Err(AstError::ProjectEmpty);
        }
        let arity = columns.len() as u32;
        Ok(self.push_expr(
            ExprNode::Project {
                expr,
                columns: columns.to_vec(),
            },
            arity,
        ))
    }

    pub fn decl(
        &mut self,
        variable: VarId,
        mult: Multiplicity,
        expr: ExprId,
    ) -> Result<Decl, AstError> {
        let var_arity = self.variable_arity(variable);
        let expr_arity = self.arity(expr);
        if var_arity != expr_arity {
            return Err(AstError::DeclArityMismatch {
                var: var_arity,
                expr: expr_arity,
            });
        }
        if mult != Multiplicity::Set && expr_arity > 1 {
            return Err(AstError::DeclMultiplicity {
                mult: mult.symbol(),
                arity: expr_arity,
            });
        }
        Ok(Decl {
            mult,
            variable,
            expr,
        })
    }

    pub fn add_decls(&mut self, list: Vec<Decl>) -> DeclsId {
        let id = DeclsId(self.decls_list.len() as u32);
        self.decls_list.push(list);
        id
    }

    fn decls_total_arity(&self, id: DeclsId) -> u32 {
        self.decls(id)
            .iter()
            .map(|d| self.variable_arity(d.variable))
            .sum()
    }

    pub fn comprehension(&mut self, decls: DeclsId, body: FormulaId) -> Result<ExprId, AstError> {
        let arity = self.decls_total_arity(decls);
        Ok(self.push_expr(ExprNode::Comprehension { decls, body }, arity))
    }

    pub fn from_int(&mut self, int: IntId) -> ExprId {
        self.push_expr(ExprNode::FromInt(int), 1)
    }

    pub fn int_constant(&mut self, value: Int) -> IntId {
        let id = IntId(self.ints.len() as u32);
        self.ints.push(IntNode::Constant(value));
        id
    }

    pub fn cast_to_int(&mut self, op: CastToIntOp, expr: ExprId) -> Result<IntId, AstError> {
        if op == CastToIntOp::Sum && self.arity(expr) > 1 {
            return Err(AstError::SumRequiresUnary(self.arity(expr)));
        }
        let id = IntId(self.ints.len() as u32);
        self.ints.push(IntNode::OfExpr { op, expr });
        Ok(id)
    }

    pub fn binary_int(&mut self, op: IntBinOp, left: IntId, right: IntId) -> IntId {
        let id = IntId(self.ints.len() as u32);
        self.ints.push(IntNode::Binary { op, left, right });
        id
    }

    pub fn if_int(&mut self, cond: FormulaId, then: IntId, els: IntId) -> IntId {
        let id = IntId(self.ints.len() as u32);
        self.ints.push(IntNode::If { cond, then, els });
        id
    }

    pub fn sum_int(&mut self, decls: DeclsId, body: IntId) -> IntId {
        let id = IntId(self.ints.len() as u32);
        self.ints.push(IntNode::Sum { decls, body });
        id
    }

    pub fn bool_formula(&mut self, value: bool) -> FormulaId {
        self.push_formula(FormulaNode::Constant(value))
    }

    pub fn true_formula(&mut self) -> FormulaId {
        self.bool_formula(true)
    }

    pub fn false_formula(&mut self) -> FormulaId {
        self.bool_formula(false)
    }

    fn push_formula(&mut self, node: FormulaNode) -> FormulaId {
        let id = FormulaId(self.formulas.len() as u32);
        self.formulas.push(node);
        id
    }

    pub fn not(&mut self, child: FormulaId) -> FormulaId {
        self.push_formula(FormulaNode::Not(child))
    }

    pub fn compose_formula(&mut self, op: FormulaBinOp, formulas: &[FormulaId]) -> FormulaId {
        match formulas.len() {
            0 => self.bool_formula(op == FormulaBinOp::And),
            1 => formulas[0],
            _ => self.push_formula(FormulaNode::Nary {
                op,
                children: formulas.to_vec(),
            }),
        }
    }

    pub fn and(&mut self, formulas: &[FormulaId]) -> FormulaId {
        self.compose_formula(FormulaBinOp::And, formulas)
    }

    pub fn or(&mut self, formulas: &[FormulaId]) -> FormulaId {
        self.compose_formula(FormulaBinOp::Or, formulas)
    }

    pub fn comparison(
        &mut self,
        op: ExprCompOp,
        left: ExprId,
        right: ExprId,
    ) -> Result<FormulaId, AstError> {
        let l = self.arity(left);
        let r = self.arity(right);
        if l != r {
            return Err(AstError::ArityMismatch2 {
                op: op.symbol(),
                left: l,
                right: r,
            });
        }
        Ok(self.push_formula(FormulaNode::Comparison { op, left, right }))
    }

    pub fn int_comparison(&mut self, op: IntCompOp, left: IntId, right: IntId) -> FormulaId {
        self.push_formula(FormulaNode::IntComparison { op, left, right })
    }

    pub fn quantified(&mut self, quant: Quantifier, decls: DeclsId, body: FormulaId) -> FormulaId {
        self.push_formula(FormulaNode::Quantified { quant, decls, body })
    }

    pub fn multiplicity_formula(
        &mut self,
        mult: Multiplicity,
        expr: ExprId,
    ) -> Result<FormulaId, AstError> {
        if mult == Multiplicity::Set {
            return Err(AstError::SetIsNotFormulaMult);
        }
        Ok(self.push_formula(FormulaNode::Multiplicity { mult, expr }))
    }

    pub fn temporal_unary(&mut self, op: TemporalFormulaOp, child: FormulaId) -> FormulaId {
        self.push_formula(FormulaNode::TemporalUnary { op, child })
    }

    pub fn temporal_binary(
        &mut self,
        op: TemporalBinaryOp,
        left: FormulaId,
        right: FormulaId,
    ) -> FormulaId {
        self.push_formula(FormulaNode::TemporalBinary { op, left, right })
    }
}
