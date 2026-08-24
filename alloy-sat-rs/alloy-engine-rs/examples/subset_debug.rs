//! Debug: solve subsets of the root conjunction to localize mistranslation.
use alloy_engine::decode_problem;
use alloy_kodkod_rs::ast::FormulaNode;
use alloy_kodkod_rs::solver::{Solver, SolverOptions};

fn main() {
    let path = std::env::args().nth(1).expect("usage: subset_debug <file>");
    let bytes = std::fs::read(&path).expect("read");
    let mut p = decode_problem(&bytes).expect("decode");

    let kids: Vec<_> = match p.arena.formula(p.formula) {
        FormulaNode::Nary { children, .. } => children.clone(),
        other => panic!("root not nary: {other:?}"),
    };
    println!("root conjuncts: {}", kids.len());
    for (i, k) in kids.iter().enumerate() {
        let desc = match p.arena.formula(*k) {
            FormulaNode::Constant(v) => format!("const {v}"),
            FormulaNode::Not(_) => "not".to_string(),
            FormulaNode::Comparison { .. } => "cmp".to_string(),
            FormulaNode::Quantified { quant, .. } => format!("quant {quant:?}"),
            FormulaNode::IntComparison { op, .. } => format!("intcmp {op:?}"),
            other => format!("{other:?}"),
        };
        let mut arena2 = p.arena.clone();
        let s = Solver::with_options(SolverOptions {
            bitwidth: p.bitwidth,
            ..Default::default()
        });
        // Solve with ONLY this conjunct (plus constants skipped).
        let r = s.solve(&mut arena2, *k, &p.bounds);
        println!(
            "  [{i}] alone {desc}: {}",
            match &r {
                Ok(sol) => if sol.satisfiable { "SAT" } else { "UNSAT" }.to_string(),
                Err(e) => format!("ERR {e}"),
            }
        );
    }
    // Pairs of interesting conjuncts
    println!("--- pairs (first 20):");
    let mut shown = 0;
    for i in 0..kids.len() {
        for j in i + 1..kids.len() {
            if shown >= 20 {
                break;
            }
            let mut arena2 = p.arena.clone();
            let f = p.arena.and(&[kids[i], kids[j]]);
            let s = Solver::with_options(SolverOptions {
                bitwidth: p.bitwidth,
                ..Default::default()
            });
            let r = s.solve(&mut arena2, f, &p.bounds);
            println!(
                "  [{i},{j}]: {}",
                match &r {
                    Ok(sol) =>
                        if sol.satisfiable {
                            "SAT".to_string()
                        } else {
                            "UNSAT".to_string()
                        },
                    Err(e) => format!("ERR {e}"),
                }
            );
            shown += 1;
        }
    }
}
