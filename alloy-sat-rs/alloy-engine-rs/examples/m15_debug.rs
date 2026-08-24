//! Debug: solve hand-built variants of the m15 assertion pieces.
use alloy_engine::decode_problem;
use alloy_kodkod_rs::ast::{FormulaNode, Multiplicity, Quantifier};
use alloy_kodkod_rs::solver::{Solver, SolverOptions};

fn solve(
    p_arena: &alloy_kodkod_rs::ast::AstArena,
    f: alloy_kodkod_rs::ast::FormulaId,
    bounds: &alloy_kodkod_rs::bounds::Bounds,
    bw: u32,
) -> String {
    let mut arena = p_arena.clone();
    let s = Solver::with_options(SolverOptions {
        bitwidth: bw,
        ..Default::default()
    });
    match s.solve(&mut arena, f, bounds) {
        Ok(sol) => {
            if sol.satisfiable {
                "SAT".into()
            } else {
                "UNSAT".into()
            }
        }
        Err(e) => format!("ERR {e}"),
    }
}

fn main() {
    let bytes = std::fs::read("/tmp/opencode/core/min/m15.bin").expect("read");
    let mut p = decode_problem(&bytes).expect("decode");
    let kids: Vec<_> = match p.arena.formula(p.formula) {
        FormulaNode::Nary { children, .. } => children.clone(),
        other => panic!("root not nary {other:?}"),
    };
    // find check conjunct: Not(Quantified All ...)
    let mut check_q = None;
    for &k in &kids {
        if let FormulaNode::Not(c) = p.arena.formula(k) {
            if let FormulaNode::Quantified { .. } = p.arena.formula(*c) {
                check_q = Some(*c);
            }
        }
    }
    let q = check_q.expect("no quantified assertion");
    let (decls_id, body) = match p.arena.formula(q) {
        FormulaNode::Quantified { decls, body, .. } => (*decls, *body),
        _ => unreachable!(),
    };
    let dlist = p.arena.decls(decls_id).to_vec();
    println!(
        "decl vars: {:?}",
        dlist.iter().map(|d| d.variable).collect::<Vec<_>>()
    );

    // body = Or( Not(A), Conc ); A = And(And(NotMS, EqAdd), EqDel)
    let (not_a, conc) = match p.arena.formula(body) {
        FormulaNode::Nary {
            op: alloy_kodkod_rs::ast::FormulaBinOp::Or,
            children,
        } => (children[0], children[1]),
        o => panic!("body not or: {o:?}"),
    };
    let a = match p.arena.formula(not_a) {
        FormulaNode::Not(c) => *c,
        o => panic!("{o:?}"),
    };
    // A = And-chain; find the mult-some piece by walking
    fn collect_ms(
        a: &alloy_kodkod_rs::ast::AstArena,
        f: alloy_kodkod_rs::ast::FormulaId,
        out: &mut Vec<alloy_kodkod_rs::ast::FormulaId>,
    ) {
        match a.formula(f) {
            FormulaNode::Multiplicity {
                mult: Multiplicity::Some,
                ..
            } => out.push(f),
            FormulaNode::Not(_) | FormulaNode::Nary { .. } => {
                let kidsn: Vec<_> = match a.formula(f) {
                    FormulaNode::Not(c) => vec![*c],
                    FormulaNode::Nary { children, .. } => children.clone(),
                    _ => vec![],
                };
                for k in kidsn {
                    collect_ms(a, k, out);
                }
            }
            _ => {}
        }
    }
    let mut ms = Vec::new();
    collect_ms(&p.arena, a, &mut ms);
    println!("found mult-some nodes in antecedent: {}", ms.len());
    let ms_f = ms[0];

    // S2: all V1..V5 | MS   (every binding has empty image) -> SAT expected
    let s2 = p.arena.quantified(Quantifier::All, decls_id, ms_f);
    println!(
        "S2 all|not some n.(b.addr): {}",
        solve(&p.arena, s2, &p.bounds, p.bitwidth)
    );
    // S3: negation of S2 -> UNSAT expected
    let s3 = p.arena.not(s2);
    println!(
        "S3 not(S2):                 {}",
        solve(&p.arena, s3, &p.bounds, p.bitwidth)
    );
    // S1: exists-style via body alone under All? just body alone (free vars unconstrained -> iterates?) skip.
    // S4: full Q (valid assertion) -> UNSAT expected
    println!(
        "S4 Q(assertion):            {}",
        solve(&p.arena, q, &p.bounds, p.bitwidth)
    );
    // S5: Q with body replaced by CONC only (all b,b",b",n,t | b.addr = b"".addr) -> UNSAT expected
    let q5 = p.arena.quantified(Quantifier::All, decls_id, conc);
    println!(
        "S5 all|b.addr=b\"\".addr:     {}",
        solve(&p.arena, q5, &p.bounds, p.bitwidth)
    );
    // S6: Q with body = Or(Not(EqAdd), CONC): add-eq implies conclusion -> UNSAT expected?
    // extract eq-add / eq-del from And chain of A
    let and_kids: Vec<_> = match p.arena.formula(a) {
        FormulaNode::Nary {
            op: alloy_kodkod_rs::ast::FormulaBinOp::And,
            children,
        } => children.clone(),
        o => panic!("{o:?}"),
    };
    println!("antecedent and-children: {}", and_kids.len());
    for (i, c) in and_kids.iter().enumerate() {
        let desc = match p.arena.formula(*c) {
            FormulaNode::Comparison { op, .. } => format!("cmp {op:?}"),
            FormulaNode::Not(inner) => match p.arena.formula(*inner) {
                FormulaNode::Multiplicity { mult, .. } => format!("not mult {mult:?}"),
                o => format!("not {o:?}"),
            },
            o => format!("{o:?}"),
        };
        println!("  A[{i}] = {desc}");
        let qb = p.arena.quantified(Quantifier::All, decls_id, *c);
        println!(
            "      all|A[{i}]: {}",
            solve(&p.arena, qb, &p.bounds, p.bitwidth)
        );
    }
    // T_B: all V1..V5 | And(NotMS, Not(CONC)) -> SAT expected (sparse addr)
    {
        let not_ms = p.arena.not(ms_f);
        let not_conc = p.arena.not(conc);
        let body_tb = p.arena.and(&[not_ms, not_conc]);
        let qtb = p.arena.quantified(Quantifier::All, decls_id, body_tb);
        println!(
            "T_B all|not-some(n.(b.addr)) & b.addr!=b\"\".addr: {}",
            solve(&p.arena, qtb, &p.bounds, p.bitwidth)
        );
    }
    // T_C: all V1..V5 | MS alone again but as EXISTS-negation pair sanity:
    //   not(all|MS) == SAT iff some instance has a nonempty image somewhere
    {
        let qa = p.arena.quantified(Quantifier::All, decls_id, ms_f);
        let nqa = p.arena.not(qa);
        println!(
            "T_C not(all|some-image-empty): {}",
            solve(&p.arena, nqa, &p.bounds, p.bitwidth)
        );
    }
}
// appended: decisive variant tests
