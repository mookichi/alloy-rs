//! Heavy benchmark: 16-queens end-to-end (minutes-scale).
//! Run explicitly with: cargo bench -p alloy-kodkod-rs --features ipasir --bench heavy

#[path = "../tests/puzzles.rs"]
mod puzzles;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use std::time::Duration;

fn bench_queens16(c: &mut Criterion) {
    let solver = alloy_kodkod_rs::Solver::new();
    let mut group = c.benchmark_group("heavy");
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(600));
    group.bench_function("queens16", |b| {
        b.iter(|| {
            let mut p = puzzles::queens(black_box(16));
            let sol = solver.solve(&mut p.arena, p.formula, &p.bounds).unwrap();
            assert!(sol.satisfiable);
        })
    });
    group.finish();
}

criterion_group!(benches, bench_queens16);
criterion_main!(benches);
