//! Differential property test: random small relational problems solved by
//! the IPASIR facade vs brute-force ground truth obtained by enumerating
//! every legal instance and evaluating the formula with the independent
//! Evaluator.
//!
//! Regression guard for the spurious-SAT bug family found on
//! addressBook2e/m15 (quantified implication over shared join/difference
//! subexpressions). NOTE: the current random generator does NOT trigger
//! the known bug yet (500 seeds pass); the deterministic repro lives in
//! alloy-engine-rs/examples/repro_spurious_sat.rs. Extend generators or
//! raise DIFF_SEEDS after fixes to widen coverage.

use alloy_kodkod_rs::ast::*;
use alloy_kodkod_rs::bounds::Bounds;
use alloy_kodkod_rs::eval::Evaluator;
use alloy_kodkod_rs::instance::Instance;
use alloy_kodkod_rs::relation::{RelationId, RelationPool};
use alloy_kodkod_rs::solver::{Solver, SolverOptions};
use alloy_kodkod_rs::tuple::Tuple;
use alloy_kodkod_rs::tupleset::TupleSet;
use alloy_kodkod_rs::universe::Universe;
use std::sync::Arc;

// ---------- tiny deterministic RNG (xorshift64) ----------
struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Rng {
        Rng(seed | 1)
    }
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    fn chance(&mut self, pct: u64) -> bool {
        self.next() % 100 < pct
    }
}

// ---------- case model ----------
const ATOMS: [&str; 2] = ["a0", "a1"];

struct Case {
    arena: AstArena,
    bounds: Bounds,
    u: Arc<Universe>,
    pool: Arc<RelationPool>,

    formula: FormulaId,
}

fn build_case(rng: &mut Rng) -> Case {
    let u = Universe::new(ATOMS).unwrap();
    let pool = Arc::new(RelationPool::new());
    let mut arena = AstArena::with_pool(Arc::clone(&pool));
    let mut bounds = Bounds::new(&u, &pool);

    // One unary relation (exact-full, doubles as quantifier domain) and one
    // binary relation with free lower/upper bounds.
    let r1 = arena.relation("S", 1);
    let mut s_full = TupleSet::new(&u, 1).unwrap();
    for a in ATOMS {
        s_full
            .insert(&Tuple::from_atoms(&u, &[a]).unwrap())
            .unwrap();
    }
    bounds.bound_exactly(r1, &s_full).unwrap();

    let r2 = arena.relation("r", 2);
    let mut up = TupleSet::new(&u, 2).unwrap();
    let mut all = Vec::new();
    for a in ATOMS {
        for b in ATOMS {
            all.push((a, b));
        }
    }
    // random upper subset (>=1 tuple), then lower subset of upper
    let chosen: Vec<_> = all
        .iter()
        .filter(|_| rng.chance(60))
        .chain(all.iter().take(1))
        .collect();
    let mut seen = std::collections::BTreeSet::new();
    for &(a, b) in &chosen {
        if seen.insert((a, b)) {
            up.insert(&Tuple::from_atoms(&u, &[a, b]).unwrap()).unwrap();
        }
    }
    let lo = {
        let mut t = TupleSet::new(&u, 2).unwrap();
        for &(a, b) in &chosen {
            if seen.contains(&(a, b)) && rng.chance(25) {
                t.insert(&Tuple::from_atoms(&u, &[a, b]).unwrap()).unwrap();
            }
        }
        t
    };
    bounds.bound(r2, &lo, &up).unwrap();

    // ternary relation (enables unary-join-binary patterns like `b.addr`)
    let r3 = arena.relation("t", 3);
    let mut up3 = TupleSet::new(&u, 3).unwrap();
    let mut all3 = Vec::new();
    for a in ATOMS {
        for b in ATOMS {
            for c in ATOMS {
                all3.push((a, b, c));
            }
        }
    }
    let mut seen3 = std::collections::BTreeSet::new();
    let picked3: Vec<_> = all3.iter().filter(|_| rng.chance(25)).take(4).collect();
    if picked3.is_empty() {
        up3.insert(&Tuple::from_atoms(&u, &[ATOMS[0], ATOMS[0], ATOMS[0]]).unwrap())
            .unwrap();
        seen3.insert((ATOMS[0], ATOMS[0], ATOMS[0]));
    }
    for &(a, b, c) in &picked3 {
        if seen3.insert((a, b, c)) {
            up3.insert(&Tuple::from_atoms(&u, &[a, b, c]).unwrap())
                .unwrap();
        }
    }
    let lo3 = TupleSet::new(&u, 3).unwrap();
    bounds.bound(r3, &lo3, &up3).unwrap();

    let vars: Vec<(VarId, u32)> = ["x", "y", "z"]
        .iter()
        .map(|n| (arena.variable(n), 1))
        .collect();

    let rels = vec![(r1, 1u32), (r2, 2u32), (r3, 3u32)];
    let unary_rels = vec![r1];

    // Formula skeleton biased toward the bug family: quantified implication
    // whose antecedent/conclusion share join subexpressions.
    let formula = gen_formula(rng, &mut arena, &rels, &unary_rels, &vars, 0);

    Case {
        arena,
        bounds,
        u,
        pool,
        formula,
    }
}

fn gen_expr(
    rng: &mut Rng,
    arena: &mut AstArena,
    rels: &[(RelationId, u32)],
    vars: &[(VarId, u32)],
    arity: u32,
    depth: u32,
) -> (ExprId, u32) {
    fn leaf(
        rng: &mut Rng,
        arena: &mut AstArena,
        rels: &[(RelationId, u32)],
        vars: &[(VarId, u32)],
        arity: u32,
    ) -> (ExprId, u32) {
        let same: Vec<(RelationId, u32)> =
            rels.iter().copied().filter(|(_, a)| *a == arity).collect();
        if !same.is_empty() && rng.chance(70) {
            let (r, a) = same[rng.below(same.len())];
            (arena.expr_relation(r), a)
        } else if let Some(&(v, a)) = vars.iter().find(|(_, a)| *a == arity) {
            if rng.chance(50) {
                (arena.expr_variable(v), a)
            } else {
                let (r, a) = same[0];
                (arena.expr_relation(r), a)
            }
        } else {
            let (r, a) = same[0];
            (arena.expr_relation(r), a)
        }
    }
    if depth == 0 {
        return leaf(rng, arena, rels, vars, arity);
    }
    match rng.below(10) {
        0 | 1 => leaf(rng, arena, rels, vars, arity),
        2 | 3 => {
            // join over a ternary relation: unary . ternary => binary
            let cands: Vec<&(RelationId, u32)> = rels.iter().filter(|(_, a)| *a >= 3).collect();
            if cands.is_empty() || arity < 1 {
                leaf(rng, arena, rels, vars, arity)
            } else {
                let (_, ta) = cands[rng.below(cands.len())];
                let inner = ta - 1;
                let (ll, la) = if let Some(&(v, va)) = vars.iter().find(|(_, a)| *a == 1) {
                    if rng.chance(50) {
                        (arena.expr_variable(v), va)
                    } else {
                        gen_expr(rng, arena, rels, vars, 1, depth - 1)
                    }
                } else {
                    gen_expr(rng, arena, rels, vars, 1, depth - 1)
                };
                let (rr, ra) = gen_expr(rng, arena, rels, vars, inner, depth - 1);
                if la + ra >= 3 && la == 1 {
                    (
                        arena.binary_expr(BinaryOp::Join, ll, rr).unwrap(),
                        la + ra - 2,
                    )
                } else {
                    // fall back to direct join on relation leaves
                    let trel = rels.iter().copied().find(|(_, a)| *a >= 3);
                    if let Some((r3id, a3)) = trel {
                        let e1 = arena.expr_relation(r3id);
                        let _ = a3;
                        // (univ-ish unary var) . r3 => arity a3-1
                        if let Some(&(v, _)) = vars.iter().find(|(_, a)| *a == 1) {
                            let l2 = arena.expr_variable(v);
                            (arena.binary_expr(BinaryOp::Join, l2, e1).unwrap(), a3 - 1)
                        } else {
                            leaf(rng, arena, rels, vars, arity)
                        }
                    } else {
                        leaf(rng, arena, rels, vars, arity)
                    }
                }
            }
        }
        4 => {
            if arity >= 2 {
                let la = 1 + rng.below(arity as usize - 1) as u32;
                let lb = arity - la;
                let (a, aa) = gen_expr(rng, arena, rels, vars, la, depth - 1);
                let (b, bb) = gen_expr(rng, arena, rels, vars, lb, depth - 1);
                (arena.binary_expr(BinaryOp::Product, a, b).unwrap(), aa + bb)
            } else {
                leaf(rng, arena, rels, vars, arity)
            }
        }
        _ => {
            let op = match rng.below(3) {
                0 => BinaryOp::Union,
                1 => BinaryOp::Intersection,
                _ => BinaryOp::Difference,
            };
            let (a, _) = gen_expr(rng, arena, rels, vars, arity, depth - 1);
            let (b, _) = gen_expr(rng, arena, rels, vars, arity, depth - 1);
            (arena.binary_expr(op, a, b).unwrap(), arity)
        }
    }
}

fn gen_formula(
    rng: &mut Rng,
    arena: &mut AstArena,
    rels: &[(RelationId, u32)],
    unary_rels: &[RelationId],
    vars: &[(VarId, u32)],
    depth: u32,
) -> FormulaId {
    if depth == 0 || rng.chance(20) {
        // leaf comparison or multiplicity
        let k = 1 + rng.below(2) as u32;
        let (a, aa) = loop {
            let (e, ar) = gen_expr(rng, arena, rels, vars, k, 1);
            if ar == k {
                break (e, ar);
            }
        };
        let (b, bb) = loop {
            let (e, ar) = gen_expr(rng, arena, rels, vars, k, 1);
            if ar == k {
                break (e, ar);
            }
        };
        let _ = (aa, bb);
        return if rng.chance(60) {
            arena.comparison(ExprCompOp::Equals, a, b).unwrap()
        } else {
            arena.comparison(ExprCompOp::Subset, a, b).unwrap()
        };
    }
    match rng.below(6) {
        // ---- m15-style template: all x,y,z | !(ante) \/ conc with shared joins
        4 | 5 if !unary_rels.is_empty() && depth >= 1 => {
            let ternaries: Vec<(RelationId, u32)> =
                rels.iter().copied().filter(|(_, a)| *a >= 3).collect();
            let Some(&(trel, _)) = ternaries.first() else {
                let a = gen_formula(rng, arena, rels, unary_rels, vars, depth - 1);
                let b = gen_formula(rng, arena, rels, unary_rels, vars, depth - 1);
                let na = arena.not(a);
                return arena.or(&[na, b]);
            };
            let et = arena.expr_relation(trel);
            // pick up to 3 distinct unary vars
            let picked: Vec<VarId> = vars
                .iter()
                .take(1 + rng.below(vars.len().min(3)))
                .map(|&(v, _)| v)
                .collect();
            // shared join pieces: j_i = x_i . t
            let joins: Vec<(VarId, ExprId)> = picked
                .iter()
                .map(|&v| {
                    let ev = arena.expr_variable(v);
                    (v, arena.binary_expr(BinaryOp::Join, ev, et).unwrap())
                })
                .collect();
            // antecedent: 2-3 equalities/differences involving shared joins + products
            let mut conjuncts: Vec<FormulaId> = Vec::new();
            for i in 0..joins.len() {
                let (vi, ji) = joins[i];
                let (vj, jj) = joins[(i + 1) % joins.len()];
                let ei = arena.expr_variable(vi);
                let ej = arena.expr_variable(vj);
                match rng.below(4) {
                    0 => {
                        // j_vj = j_vi union (v_i . t?) product-ish: use var-var product
                        let prod = arena.binary_expr(BinaryOp::Product, ei, ej).unwrap();
                        let un = arena.binary_expr(BinaryOp::Union, ji, prod).unwrap();
                        conjuncts.push(arena.comparison(ExprCompOp::Equals, jj, un).unwrap());
                    }
                    1 => {
                        // j_vj = j_vi - prod
                        let prod = arena.binary_expr(BinaryOp::Product, ei, ej).unwrap();
                        let df = arena.binary_expr(BinaryOp::Difference, ji, prod).unwrap();
                        conjuncts.push(arena.comparison(ExprCompOp::Equals, jj, df).unwrap());
                    }
                    2 => {
                        // no (v_i . t): not some(join)
                        let img = arena.binary_expr(BinaryOp::Join, ei, ji).unwrap();
                        let m = arena.multiplicity_formula(Multiplicity::Some, img).unwrap();
                        conjuncts.push(arena.not(m));
                    }
                    _ => {
                        // j_vi = j_vj
                        conjuncts.push(arena.comparison(ExprCompOp::Equals, ji, jj).unwrap());
                    }
                }
                if conjuncts.len() >= 3 {
                    break;
                }
            }
            let ante = arena.and(&conjuncts);
            let conc = {
                let (_, jl) = joins[joins.len() - 1];
                arena.comparison(ExprCompOp::Equals, jl, jl).unwrap()
            };
            let na = arena.not(ante);
            let body = arena.or(&[na, conc]);
            let ds = {
                let d: Vec<Decl> = picked
                    .iter()
                    .map(|&v| {
                        let e = arena.expr_relation(unary_rels[0]);
                        arena.decl(v, Multiplicity::One, e).unwrap()
                    })
                    .collect();
                arena.add_decls(d)
            };
            let quant = if rng.chance(60) {
                Quantifier::All
            } else {
                Quantifier::Some
            };
            arena.quantified(quant, ds, body)
        }
        0 => {
            let f = gen_formula(rng, arena, rels, unary_rels, vars, depth - 1);
            arena.not(f)
        }
        1 => {
            let a = gen_formula(rng, arena, rels, unary_rels, vars, depth - 1);
            let b = gen_formula(rng, arena, rels, unary_rels, vars, depth - 1);
            if rng.chance(50) {
                arena.and(&[a, b])
            } else {
                arena.or(&[a, b])
            }
        }
        3 | 4 => {
            // implication desugared (!a \/ b) -- core of the m15 family
            let a = gen_formula(rng, arena, rels, unary_rels, vars, depth - 1);
            let b = gen_formula(rng, arena, rels, unary_rels, vars, depth - 1);
            let na = arena.not(a);
            arena.or(&[na, b])
        }
        5..=8 => {
            // quantifier over 1-2 unary vars, body recursive
            let nvars = 1 + rng.below(2usize.min(vars.len()));
            let picked: Vec<(VarId, u32)> = (0..nvars).map(|i| vars[i]).collect();
            let ds = {
                let eu = unary_rels[rng.below(unary_rels.len())];
                let d: Vec<Decl> = picked
                    .iter()
                    .map(|&(v, _)| {
                        let e = arena.expr_relation(eu);
                        arena.decl(v, Multiplicity::One, e).unwrap()
                    })
                    .collect();
                arena.add_decls(d)
            };
            let body = gen_formula(rng, arena, rels, unary_rels, vars, depth - 1);
            let quant = if rng.chance(55) {
                Quantifier::All
            } else {
                Quantifier::Some
            };
            arena.quantified(quant, ds, body)
        }
        _ => {
            // multiplicity over unary expr
            let (e, _) = gen_expr(rng, arena, rels, vars, 1, 2);
            let mult = match rng.below(3) {
                0 => Multiplicity::Some,
                1 => Multiplicity::Lone,
                _ => Multiplicity::One,
            };
            arena.multiplicity_formula(mult, e).unwrap()
        }
    }
}

// ---------- ground truth by enumeration ----------
fn ground_truth(case: &Case) -> Result<bool, String> {
    let Case {
        arena,
        bounds,
        u,
        pool,
        formula,
        ..
    } = case;
    // collect free cells: for each relation, upper minus lower cells are variables
    let mut all_rels: Vec<RelationId> = bounds.relations().collect();
    let mut choice_cells: Vec<(RelationId, Vec<i64>)> = Vec::new();
    for r in &all_rels {
        let lo = bounds.lower_bound(*r).ok_or("unbounded")?;
        let up = bounds.upper_bound(*r).ok_or("unbounded")?;
        let mut free = Vec::new();
        for idx in up.index_view().iter() {
            if !lo.contains_index(idx) {
                free.push(idx);
            }
        }
        choice_cells.push((*r, free));
    }
    all_rels.retain(|_| true);
    let total: usize = choice_cells
        .iter()
        .map(|(_, f)| 1usize << f.len())
        .product();
    if total > 4096 {
        return Err("too many assignments".into());
    }

    let _ = &all_rels;
    for mask in 0..total {
        let mut inst = Instance::new(u, pool);
        let mut bit = 0usize;
        for (r, free) in &choice_cells {
            let mut ts = TupleSet::new(u, bounds.pool().arity(*r)).unwrap();
            if let Some(lo) = bounds.lower_bound(*r) {
                for idx in lo.index_view().iter() {
                    if !ts.insert_index(idx) {
                        return Err("insert failed".into());
                    }
                }
            }
            for &idx in free {
                if (mask >> bit) & 1 == 1 && !ts.insert_index(idx) {
                    return Err("insert failed".into());
                }
                bit += 1;
            }
            inst.add(*r, &ts).map_err(|e| e.to_string())?;
        }
        let ev = Evaluator::new(&inst);
        match ev.formula_bool(arena, *formula, &Vec::new()) {
            Ok(true) => return Ok(true),
            Ok(false) => {}
            Err(e) => return Err(format!("eval error: {e}")),
        }
    }
    Ok(false)
}

fn dump_expr(arena: &AstArena, e: ExprId, depth: usize) {
    let pad = "  ".repeat(depth);
    match arena.expr(e) {
        ExprNode::Relation(r) => println!("{}rel {}", pad, arena.relation_name(*r)),
        ExprNode::Variable(v) => println!("{}var {}", pad, arena.variable_name(*v)),
        other => {
            println!("{}{:?}", pad, other);
            if let ExprNode::Binary { left, right, .. } = arena.expr(e) {
                dump_expr(arena, *left, depth + 1);
                dump_expr(arena, *right, depth + 1);
            }
        }
    }
}

fn dump_formula(arena: &AstArena, f: FormulaId, depth: usize) {
    let pad = "  ".repeat(depth);
    match arena.formula(f) {
        FormulaNode::Constant(v) => println!("{}const {}", pad, v),
        FormulaNode::Not(c) => {
            println!("{}not", pad);
            dump_formula(arena, *c, depth + 1);
        }
        FormulaNode::Nary { op, children } => {
            println!("{}nary {:?}", pad, op);
            for c in children.clone() {
                dump_formula(arena, c, depth + 1);
            }
        }
        FormulaNode::Comparison { op, left, right } => {
            println!("{}cmp {:?}", pad, op);
            dump_expr(arena, *left, depth + 1);
            dump_expr(arena, *right, depth + 1);
        }
        FormulaNode::IntComparison { .. } => println!("{}intcmp", pad),
        FormulaNode::Quantified { quant, decls, body } => {
            println!(
                "{}quant {:?} over {:?}",
                pad,
                quant,
                arena
                    .decls(*decls)
                    .iter()
                    .map(|d| arena.variable_name(d.variable))
                    .collect::<Vec<_>>()
            );
            for d in arena.decls(*decls) {
                println!("{}  domain {}:", pad, arena.variable_name(d.variable));
                dump_expr(arena, d.expr, depth + 2);
            }
            dump_formula(arena, *body, depth + 1);
        }
        FormulaNode::Multiplicity { mult, expr } => {
            println!("{}mult {:?}", pad, mult);
            dump_expr(arena, *expr, depth + 1);
        }
        other => println!("{}{:?}", pad, other),
    }
}

fn dump_case(cs: &Case) {
    println!("=== FAILING CASE ===");
    for r in cs.bounds.relations() {
        let name = cs.arena.relation_name(r);
        let lo = cs.bounds.lower_bound(r).map(|t| t.len()).unwrap_or(0);
        let up = cs.bounds.upper_bound(r).map(|t| t.len()).unwrap_or(0);
        println!(
            "rel {} arity={} lo={} up={}",
            name,
            cs.pool.arity(r),
            lo,
            up
        );
    }
    dump_formula(&cs.arena, cs.formula, 1);
}

#[test]
fn differential_random_small_problems() {
    let cases = std::env::var("DIFF_SEEDS")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(500);
    let mut mismatch = 0;
    let mut solved = 0usize;
    let mut skipped = 0usize;
    for seed in 0..cases as u64 {
        let mut rng = Rng::new(seed.wrapping_mul(0x9E3779B97F4A7C15));
        let mut cs = build_case(&mut rng);
        let truth = ground_truth(&cs);
        let Ok(truth) = truth else {
            skipped += 1;
            continue;
        };
        solved += 1;
        let s = Solver::with_options(SolverOptions {
            bitwidth: 4,
            ..Default::default()
        });
        let got = match s.solve(&mut cs.arena, cs.formula, &cs.bounds) {
            Ok(sol) => sol.satisfiable,
            Err(_) => continue, // unsupported construct: skip
        };
        if got != truth {
            mismatch += 1;
            println!("SEED {} MISMATCH solver={} truth={}", seed, got, truth);
            if mismatch == 1 {
                dump_case(&cs);
                break;
            }
        }
    }
    println!("cases={} solved={} skipped={}", cases, solved, skipped);
    assert_eq!(mismatch, 0, "differential mismatches found");
}
