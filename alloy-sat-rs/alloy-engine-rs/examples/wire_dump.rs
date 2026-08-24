//! Debug helper: decode a wire problem and print its formula DAG.
use alloy_engine::decode_problem;
use alloy_kodkod_rs::ast::{ExprNode, FormulaNode};

fn pp_expr(
    a: &alloy_kodkod_rs::ast::AstArena,
    e: alloy_kodkod_rs::ast::ExprId,
    d: usize,
) -> String {
    let pad = "  ".repeat(d);
    match a.expr(e) {
        ExprNode::Relation(r) => format!("{pad}rel {}", a.relation_name(*r)),
        other => format!("{pad}{other:?} (expr)"),
    }
}

fn dump_expr(
    a: &alloy_kodkod_rs::ast::AstArena,
    e: alloy_kodkod_rs::ast::ExprId,
    out: &mut Vec<String>,
) {
    let desc = match a.expr(e) {
        ExprNode::Relation(r) => format!("rel {}", a.relation_name(*r)),
        ExprNode::Variable(v) => format!("var V{:?}", v),
        other => format!("{other:?}"),
    };
    out.push(format!("{e:?} {desc}"));
}

fn pp_form(a: &alloy_kodkod_rs::ast::AstArena, f: alloy_kodkod_rs::ast::FormulaId, d: usize) {
    let pad = "  ".repeat(d);
    match a.formula(f) {
        FormulaNode::Constant(v) => println!("{pad}const {v}"),
        FormulaNode::Not(c) => {
            println!("{pad}not");
            pp_form(a, *c, d + 1);
        }
        FormulaNode::Nary { op, children } => {
            println!("{pad}nary {op:?}");
            for c in children.clone() {
                pp_form(a, c, d + 1);
            }
        }
        FormulaNode::Comparison { op, left, right } => {
            println!("{pad}cmp {op:?}");
            println!("{}L:", pad);
            print!("{}", pp_expr(a, *left, d + 1));
            println!();
            println!("{}R:", pad);
            print!("{}", pp_expr(a, *right, d + 1));
            println!();
        }
        FormulaNode::IntComparison { op, left, right } => {
            println!("{pad}intcmp {op:?}");
            let l = a.int(*left);
            let r = a.int(*right);
            println!("{pad}L {l:?}");
            println!("{pad}R {r:?}");
        }
        FormulaNode::Quantified { quant, decls, body } => {
            println!("{pad}quant {quant:?}");
            let list = a.decls(*decls);
            println!("{pad}decls {list:?}");
            pp_form(a, *body, d + 1);
        }
        FormulaNode::Multiplicity { mult, expr } => {
            println!("{pad}mult {mult:?}");
            print!("{}", pp_expr(a, *expr, d + 1));
            println!();
        }
        _ => println!("{pad}temporal/other"),
    }
}

fn main() {
    let path = std::env::args().nth(1).expect("usage: wire_dump <file>");
    let bytes = std::fs::read(&path).expect("read");
    let p = decode_problem(&bytes).expect("decode");
    println!("bitwidth={} rels={}", p.bitwidth, p.relation_names.len());
    // Raw expr table (id -> node) for cross-referencing joins.
    let mut out = Vec::new();
    let maxe = p.expr_by_node.values().map(|x| x.0).max().unwrap_or(0);
    for i in 0..=maxe {
        dump_expr(&p.arena, alloy_kodkod_rs::ast::ExprId(i), &mut out);
    }
    for l in out {
        println!("EXPR {l}");
    }
    pp_form(&p.arena, p.formula, 0);
}
