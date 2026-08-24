//! Iter-6 demo: `cargo run --example solve -- queens16`
//!
//! Solves a named problem through the `Solver` facade and prints the
//! materialized instance (or UNSAT). Available problems:
//! queensN, pigeonhole:KxM, coloring:<n>-<c>[:edges]

#[path = "../tests/puzzles.rs"]
mod puzzles;

use puzzles::Puzzle;
use std::time::Instant;

fn build(name: &str) -> Option<(String, Puzzle)> {
    if let Some(n) = name.strip_prefix("queens") {
        let n: usize = n.parse().ok()?;
        return Some((format!("{n}-queens"), puzzles::queens(n)));
    }
    if let Some(rest) = name.strip_prefix("pigeonhole:") {
        let (k, m) = rest.split_once('x')?;
        let (k, m): (usize, usize) = (k.parse().ok()?, m.parse().ok()?);
        return Some((
            format!("pigeonhole {k} pigeons x {m} holes"),
            puzzles::pigeonhole(k, m),
        ));
    }
    if let Some(rest) = name.strip_prefix("coloring:") {
        // coloring:<nodes>-<colors>[-<a.b,c.d,...>]  e.g. coloring:4-3-0.1,1.2,2.3,0.2
        let parts: Vec<&str> = rest.split('-').collect();
        let n: usize = parts.first()?.parse().ok()?;
        let c: usize = parts.get(1)?.parse().ok()?;
        let edges: Vec<(usize, usize)> = match parts.get(2) {
            None => Vec::new(),
            Some(spec) => spec
                .split(',')
                .map(|e| {
                    let (a, b) = e.split_once('.').expect("edge format a.b");
                    (a.parse().unwrap(), b.parse().unwrap())
                })
                .collect(),
        };
        return Some((
            format!("coloring n={n} colors={c} edges={edges:?}"),
            puzzles::coloring(n, &edges, c),
        ));
    }
    None
}

fn main() {
    let arg = std::env::args().nth(1).unwrap_or_else(|| "queens16".into());
    let (desc, mut p) = match build(&arg) {
        Some(x) => x,
        None => {
            eprintln!(
                "unknown problem '{arg}'. try: queens<N> | pigeonhole:KxM | \
                 coloring:N-C-a.b,c.d,..."
            );
            std::process::exit(2);
        }
    };

    println!("problem : {desc}");
    let solver = alloy_kodkod_rs::Solver::new();
    let t0 = Instant::now();
    let sol = match solver.solve(&mut p.arena, p.formula, &p.bounds) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("solve failed: {e}");
            std::process::exit(1);
        }
    };
    let dt = t0.elapsed();

    if !sol.satisfiable {
        println!("result  : UNSAT");
        println!("time    : {dt:?}");
        return;
    }

    let inst = sol.instance.expect("SAT implies instance");
    println!(
        "result  : SAT (primary vars={}, backend={})",
        sol.num_primary_variables, sol.backend
    );
    for r in inst.relations().collect::<Vec<_>>() {
        let ts = inst.tuples(r).unwrap();
        let atoms = inst.universe();
        let rendered: Vec<String> = ts
            .index_view()
            .iter()
            .take(40)
            .map(|idx| {
                let dims = atoms.size();
                let mut tuple = Vec::new();
                let mut cur = idx;
                for _ in 0..ts.arity() {
                    tuple.insert(0, atoms.atom((cur % dims as i64) as usize).unwrap());
                    cur /= dims as i64;
                }
                tuple
                    .iter()
                    .map(|s| s.as_ref())
                    .collect::<Vec<_>>()
                    .join("->")
            })
            .collect();
        let suffix = if ts.len() > 40 {
            format!(", … (+{} more)", ts.len() - 40)
        } else {
            String::new()
        };
        println!(
            "  {} = {{{}}}{suffix}",
            inst.pool().name(r),
            rendered.join(", ")
        );
    }

    // pretty board for queens problems
    if desc.ends_with("-queens") && inst.relations().count() >= 3 {
        let n = p.u.size();
        let q = inst
            .relations()
            .find(|&r| inst.pool().name(r).as_ref() == "Q");
        if let Some(q) = q {
            let qs = inst.tuples(q).unwrap();
            let dims = p.u.size() as i64;
            println!("board   :");
            for r in 0..dims {
                let mut line = String::new();
                for c in 0..dims {
                    line.push(if qs.contains_index(r * dims + c) {
                        'Q'
                    } else {
                        '.'
                    });
                }
                println!("  {line}");
            }
            let _ = n;
        }
    }
    println!("time    : {dt:?}");
}
