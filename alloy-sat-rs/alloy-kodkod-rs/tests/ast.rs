use alloy_kodkod_rs::ast::*;

#[test]
fn relations_intern_by_name_and_arity() {
    let a = AstArena::new();
    let r1 = a.relation("edge", 2);
    let r2 = a.relation("edge", 2);
    let r3 = a.relation("edge", 3);
    assert_eq!(r1, r2);
    assert_ne!(r1, r3);
    assert_eq!(a.relation_arity(r1), 2);
    assert_eq!(a.relation_name(r1), "edge");
}

#[test]
fn skolem_flag_is_cell_mutated() {
    let a = AstArena::new();
    let r = a.relation("sk", 1);
    assert!(!a.is_skolem(r));
    a.set_skolem(r, true);
    assert!(a.is_skolem(r));
}

#[test]
fn constant_arities_match_java() {
    let mut a = AstArena::new();
    let univ = a.univ();
    let iden = a.iden();
    let none = a.constant(ConstantExpr::Empty);
    let ints = a.constant(ConstantExpr::Ints);
    assert_eq!(a.arity(univ), 1);
    assert_eq!(a.arity(iden), 2);
    assert_eq!(a.arity(none), 1);
    assert_eq!(a.arity(ints), 1);
}

#[test]
fn binary_expr_arity_rules_match_java() {
    let mut a = AstArena::new();
    let u = a.univ();
    let iden = a.iden();
    let r2 = a.expr_relation_named("r2", 2);
    let s2 = a.expr_relation_named("s2", 2);
    let e3 = a.expr_relation_named("e3", 3);

    assert!(matches!(
        a.binary_expr(BinaryOp::Union, u, iden),
        Err(AstError::ArityMismatch2 {
            left: 1,
            right: 2,
            ..
        })
    ));
    assert_eq!(
        a.binary_expr(BinaryOp::Union, r2, e3)
            .unwrap_err()
            .to_string(),
        "arity mismatch for +: 2 vs 3"
    );
    assert!(matches!(
        a.binary_expr(BinaryOp::Join, u, u),
        Err(AstError::JoinArityTooLow(1, 1))
    ));

    let union = a.binary_expr(BinaryOp::Union, r2, s2).unwrap();
    assert_eq!(a.arity(union), 2);
}

#[test]
fn join_and_product_arities() {
    let mut a = AstArena::new();
    let e2 = a.expr_relation_named("e2", 2);
    let e3 = a.expr_relation_named("e3", 3);
    let j32 = a.binary_expr(BinaryOp::Join, e3, e2).unwrap();
    let j22 = a.binary_expr(BinaryOp::Join, e2, e2).unwrap();
    let prod = a.binary_expr(BinaryOp::Product, e2, e3).unwrap();
    assert_eq!(a.arity(j32), 3);
    assert_eq!(a.arity(j22), 2);
    assert_eq!(a.arity(prod), 5);
}

#[test]
fn unary_ops_require_binary_child_prime_preserves() {
    let mut a = AstArena::new();
    let u = a.univ();
    let r2 = a.expr_relation_named("r2", 2);

    assert!(matches!(
        a.unary_expr(UnaryExprOp::Transpose, u),
        Err(AstError::RequiresArity2 { got: 1, .. })
    ));
    let closed = a.unary_expr(UnaryExprOp::Closure, r2).unwrap();
    assert_eq!(a.arity(closed), 2);

    let primed_univ = a.prime(u);
    assert_eq!(a.arity(primed_univ), 1);
    let primed_r2 = a.prime(r2);
    match a.expr(primed_r2) {
        ExprNode::Temporal {
            op: TemporalExprOp::Prime,
            ..
        } => {}
        other => panic!("expected temporal prime node, got {:?}", other),
    }
}

#[test]
fn compose_semantics_mirror_java() {
    let mut a = AstArena::new();
    let r1 = a.expr_relation_named("p", 1);
    let q1 = a.expr_relation_named("q", 1);

    assert!(matches!(
        a.compose_expr(BinaryOp::Union, &[]),
        Err(AstError::ComposeEmpty)
    ));

    let single = [r1];
    assert_eq!(a.compose_expr(BinaryOp::Union, &single).unwrap(), r1);

    let three = [r1, q1, r1];
    let nary = a.compose_expr(BinaryOp::Union, &three).unwrap();
    match a.expr(nary) {
        ExprNode::Nary {
            op: BinaryOp::Union,
            children,
        } => assert_eq!(children.len(), 3),
        other => panic!("expected nary node, got {:?}", other),
    }

    assert!(matches!(
        a.compose_expr(BinaryOp::Join, &three),
        Err(AstError::NotNary { op: "." })
    ));
}

#[test]
fn decl_rules_and_comprehension_arity() {
    let mut a = AstArena::new();
    let v = a.variable("x");
    let w = a.variable_nary("w", 2);
    let p1 = a.expr_relation_named("p", 1);
    let r2 = a.expr_relation_named("r", 2);

    assert!(matches!(
        a.decl(v, Multiplicity::One, r2),
        Err(AstError::DeclArityMismatch { var: 1, expr: 2 })
    ));
    assert!(matches!(
        a.decl(w, Multiplicity::One, r2),
        Err(AstError::DeclMultiplicity {
            mult: "one",
            arity: 2
        })
    ));
    let ok_nary = a.decl(w, Multiplicity::Set, r2).unwrap();
    let ok_unary = a.decl(v, Multiplicity::One, p1).unwrap();

    let ds = a.add_decls(vec![ok_unary, ok_nary]);
    let body = a.true_formula();
    let comp = a.comprehension(ds, body).unwrap();
    assert_eq!(a.arity(comp), 3);
}

#[test]
fn formulas_construct_and_fold_like_java() {
    let mut a = AstArena::new();
    let t = a.true_formula();
    assert!(matches!(a.formula(t), FormulaNode::Constant(true)));

    let empty_or = a.or(&[]);
    assert!(matches!(a.formula(empty_or), FormulaNode::Constant(false)));

    assert_eq!(a.and(&[t]), t);

    let g = a.false_formula();
    let both = a.and(&[t, g]);
    match a.formula(both) {
        FormulaNode::Nary {
            op: FormulaBinOp::And,
            children,
        } => assert_eq!(children.len(), 2),
        other => panic!("expected nary and, got {:?}", other),
    }
    let negated = a.not(g);
    assert!(matches!(a.formula(negated), FormulaNode::Not(_)));
}

#[test]
fn comparisons_quantifiers_multiplicity() {
    let mut a = AstArena::new();
    let p1 = a.expr_relation_named("p", 1);
    let r2 = a.expr_relation_named("r", 2);

    assert!(matches!(
        a.comparison(ExprCompOp::Subset, p1, r2),
        Err(AstError::ArityMismatch2 { op: "in", .. })
    ));
    let cmp = a.comparison(ExprCompOp::Equals, p1, p1).unwrap();

    let v = a.variable("x");
    let d = a.decl(v, Multiplicity::One, p1).unwrap();
    let ds = a.add_decls(vec![d]);
    let q = a.quantified(Quantifier::All, ds, cmp);
    assert!(matches!(
        a.formula(q),
        FormulaNode::Quantified {
            quant: Quantifier::All,
            ..
        }
    ));

    assert!(matches!(
        a.multiplicity_formula(Multiplicity::Set, p1),
        Err(AstError::SetIsNotFormulaMult)
    ));
}

#[test]
fn int_expressions_and_casts() {
    let mut a = AstArena::new();
    let p1 = a.expr_relation_named("p", 1);
    let r2 = a.expr_relation_named("r", 2);

    let c = a.int_constant(-7);
    assert!(matches!(a.int(c), IntNode::Constant(-7)));

    let card = a.cast_to_int(CastToIntOp::Cardinality, r2).unwrap();
    assert!(matches!(
        a.cast_to_int(CastToIntOp::Sum, r2),
        Err(AstError::SumRequiresUnary(2))
    ));
    let sum = a.cast_to_int(CastToIntOp::Sum, p1).unwrap();

    let add = a.binary_int(IntBinOp::Plus, card, sum);
    assert!(matches!(
        a.int(add),
        IntNode::Binary {
            op: IntBinOp::Plus,
            ..
        }
    ));

    let eq_f = a.int_comparison(IntCompOp::Eq, add, c);
    assert!(matches!(
        a.formula(eq_f),
        FormulaNode::IntComparison {
            op: IntCompOp::Eq,
            ..
        }
    ));

    let back = a.from_int(card);
    assert_eq!(a.arity(back), 1);
}
