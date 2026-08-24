//! Iter 9 demo: Sudoku UNSAT core extraction (`-core=rce` equivalent).
//!
//! Sudoku rules are encoded as hard CNF clauses (extended encoding over
//! p(r,c,v) variables); the givens are soft groups, one per clue. A
//! solvable puzzle is solved first; a contradictory puzzle (two clues in
//! the same row demanding the same value) then demonstrates the core:
//! the backend's failed assumptions (`ipasir_failed` / CaDiCaL `failed()`)
//! seed an RCEStrategy-equivalent deletion filter that pins down the
//! minimal set of culprit clues.
//!
//! Run: cargo run --release --example sudoku_core --features ipasir

use alloy_kodkod_rs::ipasir_bridge::IpasirSolver;
use alloy_kodkod_rs::sat::SatSolver;
use alloy_kodkod_rs::ucore::{extract_cnf_core, SoftGroup};

const N: usize = 4; // 4x4 grid with 2x2 boxes, values 1..=4

/// p(r,c,v) variable (all indices 0-based, v in 0..4).
fn cell(r: usize, c: usize, v: usize) -> i64 {
    ((r * N + c) * N + v + 1) as i64
}

fn exactly_one(lits: &[i64], out: &mut Vec<Vec<i64>>) {
    out.push(lits.to_vec());
    for i in 0..lits.len() {
        for j in (i + 1)..lits.len() {
            out.push(vec![-lits[i], -lits[j]]);
        }
    }
}

/// Sudoku rules as hard clauses.
fn rules() -> Vec<Vec<i64>> {
    let mut hard = Vec::new();
    for r in 0..N {
        for c in 0..N {
            let lits: Vec<i64> = (0..N).map(|v| cell(r, c, v)).collect();
            exactly_one(&lits, &mut hard);
        }
    }
    // Rows and columns.
    for r in 0..N {
        for v in 0..N {
            let row: Vec<i64> = (0..N).map(|c| cell(r, c, v)).collect();
            exactly_one(&row, &mut hard);
        }
    }
    for c in 0..N {
        for v in 0..N {
            let col: Vec<i64> = (0..N).map(|r| cell(r, c, v)).collect();
            exactly_one(&col, &mut hard);
        }
    }
    // 2x2 boxes.
    for br in 0..2 {
        for bc in 0..2 {
            for v in 0..N {
                let box_lits: Vec<i64> = (0..2)
                    .flat_map(|i| (0..2).map(move |j| (br * 2 + i, bc * 2 + j)))
                    .map(|(r, c)| cell(r, c, v))
                    .collect();
                exactly_one(&box_lits, &mut hard);
            }
        }
    }
    hard
}

fn main() {
    println!("alloy-kodkod-rs Sudoku core extraction (grid {N}x{N})");
    let hard = rules();

    // --- Part 1: a solvable puzzle still works through the same pipeline.
    let clues_ok = [(0usize, 0usize, 1usize), (1, 3, 2), (3, 0, 3)];
    let soft_ok: Vec<SoftGroup> = clues_ok
        .iter()
        .map(|&(r, c, v)| {
            SoftGroup::new(format!("clue r{r}c{c}={v}"), vec![vec![cell(r, c, v - 1)]])
        })
        .collect();
    let mut s = IpasirSolver::new().expect("ipasir backend");
    match extract_cnf_core(&mut s, &hard, &soft_ok).unwrap() {
        None => {
            println!("\n[solvable] SAT");
            print_grid(&s);
        }
        Some(core) => panic!("solvable puzzle reported a core: {core:?}"),
    }

    // --- Part 2: contradictory puzzle — two row-mates claim value 1.
    // The row rule is HARD, so only the two culprit clues can be blamed.
    let bad = [
        (0usize, 0usize, 1usize),
        (0usize, 2usize, 1usize), // conflicts with (0,0)=1 in row 0
        (2usize, 1usize, 4usize),
    ];
    let soft_bad: Vec<SoftGroup> = bad
        .iter()
        .map(|&(r, c, v)| {
            SoftGroup::new(format!("clue r{r}c{c}={v}"), vec![vec![cell(r, c, v - 1)]])
        })
        .collect();

    let mut s = IpasirSolver::new().expect("ipasir backend");
    let core = extract_cnf_core(&mut s, &hard, &soft_bad)
        .unwrap()
        .expect("contradictory puzzle must be UNSAT");

    println!("\n[contradictory] UNSAT — core extraction (-core=rce 相当)");
    println!("backend          : {}", s.backend_name());
    println!(
        "initial failed   : {} group(s): {:?}",
        core.initial.len(),
        core.initial
            .iter()
            .map(|&i| &soft_bad[i].name)
            .collect::<Vec<_>>()
    );
    println!("solve calls      : {}", core.solves);
    println!(
        "minimized core   : {} group(s): {:?}",
        core.groups.len(),
        core.groups
            .iter()
            .map(|&i| &soft_bad[i].name)
            .collect::<Vec<_>>()
    );
    for &g in &core.groups {
        println!("  culprit → {}", soft_bad[g].name);
    }
}

fn print_grid(s: &IpasirSolver) {
    for r in 0..N {
        let mut row = String::new();
        for c in 0..N {
            let v = (0..N)
                .find(|&v| SatSolver::value_of(s, cell(r, c, v)))
                .expect("cell value");
            row.push_str(&format!("{} ", v + 1));
        }
        println!("  {row}");
    }
}
