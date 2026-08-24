//! Iter-7 demo: `cargo run --release --example ringt`
//!
//! A small temporal token-ring in the spirit of Alloy's RingT.als:
//! processes sit on a static ring (`next`), a variable relation `tok`
//! holds the set of token holders, and the LTL spec says
//!
//!   always (one tok)            — exactly one holder in every state
//!   always (tok' ⊆ next.tok)    — the token moves along the ring
//!   eventually (some tok & P0)  — process p0 eventually (re)gains it
//!
//! The trace is unrolled over `--steps N` states (default 4), solved, and
//! the lasso trace is printed together with its loop point.

#[path = "../tests/puzzles.rs"]
mod puzzles;

use alloy_kodkod_rs::ast::*;
use alloy_kodkod_rs::bounds::Bounds;
use alloy_kodkod_rs::relation::{RelationId, RelationPool};
use alloy_kodkod_rs::temporal::TemporalEval;
use alloy_kodkod_rs::tupleset::TupleSet;
use alloy_kodkod_rs::universe::Universe;
use std::sync::Arc;
use std::time::Instant;

#[allow(dead_code)]
struct RingT {
    arena: AstArena,
    bounds: Bounds,
    u: Arc<Universe>,
    next: RelationId,
    tok: RelationId,
}

fn build(n: usize) -> RingT {
    let atoms: Vec<String> = (0..n).map(|i| format!("p{i}")).collect();
    let refs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
    let u = Universe::new(refs).unwrap();
    let pool = Arc::new(RelationPool::new());
    let mut bounds = Bounds::new(&u, &pool);
    let arena = AstArena::with_pool(Arc::clone(&pool));

    // static ring successor: next(p_i) = p_{i+1 mod n}
    let next = {
        let r = arena.relation("next", 2);
        let mut s = TupleSet::new(&u, 2).unwrap();
        for i in 0..n {
            s.insert_index((i * n + (i + 1) % n) as i64);
        }
        bounds.bound_exactly(r, &s).unwrap();
        r
    };
    // variable token holders (free unary over the original atoms)
    let tok = {
        let r = arena.relation("tok", 1);
        arena.set_variable(r, true);
        let mut s = TupleSet::new(&u, 1).unwrap();
        for i in 0..n {
            s.insert_index(i as i64);
        }
        bounds.bound_upper(r, &s).unwrap();
        r
    };
    RingT {
        arena,
        bounds,
        u,
        next,
        tok,
    }
}

fn main() {
    let steps: usize = std::env::args()
        .nth(1)
        .and_then(|a| a.parse().ok())
        .unwrap_or(4);

    let mut m = build(4);
    let tok_e = m.arena.expr_relation(m.tok);

    // always (one tok)
    let one = m
        .arena
        .multiplicity_formula(Multiplicity::One, tok_e)
        .unwrap();
    let always_one = m.arena.temporal_unary(TemporalFormulaOp::Always, one);

    // always (tok' ⊆ next.tok)
    let tok_p = m.arena.prime(tok_e);
    let ne = m.arena.expr_relation(m.next);
    let te2 = m.arena.expr_relation(m.tok);
    let succ = m.arena.binary_expr(BinaryOp::Join, ne, te2).unwrap();
    let mv = m.arena.comparison(ExprCompOp::Subset, tok_p, succ).unwrap();
    let always_moves = m.arena.temporal_unary(TemporalFormulaOp::Always, mv);

    // eventually (some tok ∩ P0), with P0 exactly the first atom
    let pe = m.arena.relation("P0", 1);
    {
        let mut s = TupleSet::new(&m.u, 1).unwrap();
        s.insert_index(0);
        m.bounds.bound_exactly(pe, &s).unwrap();
    }
    let pe_e = m.arena.expr_relation(pe);
    let hit = m
        .arena
        .binary_expr(BinaryOp::Intersection, tok_e, pe_e)
        .unwrap();
    let some_hit = m
        .arena
        .multiplicity_formula(Multiplicity::Some, hit)
        .unwrap();
    let eventually_p0 = m
        .arena
        .temporal_unary(TemporalFormulaOp::Eventually, some_hit);

    let formula = m.arena.and(&[always_one, always_moves, eventually_p0]);

    println!(
        "problem : token-ring (RingT style), {} processes",
        m.u.size()
    );
    println!("steps   : {steps}");
    let solver = alloy_kodkod_rs::Solver::new();
    let t0 = Instant::now();
    let sol = match solver.solve_temporal(&mut m.arena, formula, &m.bounds, steps) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("solve failed: {e}");
            std::process::exit(1);
        }
    };
    let dt = t0.elapsed();

    if !sol.satisfiable {
        println!("result  : UNSAT (no lasso of length {steps} satisfies the spec)");
        return;
    }

    let ti = sol.temporal.expect("SAT implies lasso");
    println!(
        "result  : SAT — lasso of {} states looping back to state {}",
        ti.len(),
        ti.loop_state()
    );
    println!(
        "backend : {} (primary vars={})",
        sol.backend, sol.num_primary_variables
    );
    for (i, st) in ti.states().iter().enumerate() {
        let marker = if i == ti.loop_state() {
            "  <- loop"
        } else {
            ""
        };
        match st.tuples(m.tok) {
            Some(ts) => {
                let who: Vec<String> = ts
                    .index_view()
                    .iter()
                    .map(|idx| format!("p{idx}"))
                    .collect();
                println!("  state{i}: tok = {{{}}}{}", who.join(", "), marker);
            }
            None => println!("  state{i}: tok = <unset>"),
        }
    }

    // verify the extracted trace against the original LTL formula
    let checker = TemporalEval::new(&ti);
    match checker.holds(&m.arena, formula) {
        Ok(true) => println!("verify  : extracted lasso satisfies the LTL spec"),
        other => println!("verify  : FAILED ({other:?})"),
    }
    println!("time    : {dt:?}");
}
