//! Iter-6 criterion benchmarks: end-to-end solve pipeline
//! (FOL -> bool -> CNF -> SAT -> materialize) on representative problems.
//!
//! Run with: cargo bench -p alloy-kodkod-rs --features ipasir

#[path = "../tests/puzzles.rs"]
mod puzzles;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use std::time::Instant;

fn bench_solve(c: &mut Criterion) {
    let solver = alloy_kodkod_rs::Solver::new();
    let mut group = c.benchmark_group("solve");
    group.sample_size(10);

    for n in [8usize, 10] {
        let name = format!("queens{n}");
        group.bench_function(name, |b| {
            b.iter_custom(|iters| {
                let start = Instant::now();
                for _ in 0..iters {
                    let mut p = puzzles::queens(black_box(n));
                    let sol = solver.solve(&mut p.arena, p.formula, &p.bounds).unwrap();
                    assert!(sol.satisfiable);
                }
                start.elapsed()
            })
        });
    }

    // unsatisfiable case: 5 pigeons into 4 holes
    group.bench_function("pigeonhole_5x4", |b| {
        b.iter_custom(|iters| {
            let start = Instant::now();
            for _ in 0..iters {
                let mut p = puzzles::pigeonhole(black_box(5), black_box(4));
                let sol = solver.solve(&mut p.arena, p.formula, &p.bounds).unwrap();
                assert!(!sol.satisfiable);
            }
            start.elapsed()
        })
    });

    // 3-coloring of a diamond-ish graph
    group.bench_function("coloring_3col", |b| {
        b.iter_custom(|iters| {
            let start = Instant::now();
            for _ in 0..iters {
                let mut p = puzzles::coloring(
                    black_box(6),
                    black_box(&[(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (0, 5), (1, 5)]),
                    black_box(3),
                );
                let sol = solver.solve(&mut p.arena, p.formula, &p.bounds).unwrap();
                assert!(sol.satisfiable);
            }
            start.elapsed()
        })
    });

    group.finish();
}

criterion_group!(benches, bench_solve);
criterion_main!(benches);
