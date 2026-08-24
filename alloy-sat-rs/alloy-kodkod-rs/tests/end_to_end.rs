#![cfg(feature = "ipasir")]

use alloy_kodkod_rs::bool::{BoolFactory, BoolRef};
use alloy_kodkod_rs::cnf::translate_into_solver;
use alloy_kodkod_rs::ipasir_bridge::IpasirSolver;
use alloy_kodkod_rs::sat::SatSolver;

struct Lcg(u64);

impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 33
    }

    fn below(&mut self, n: u64) -> usize {
        (self.next() % n) as usize
    }
}

fn random_circuit(rng: &mut Lcg, f: &mut BoolFactory, nvars: usize, depth: u32) -> BoolRef {
    if depth == 0 {
        return BoolRef(rng.below(nvars as u64) as i32 + 1);
    }
    match rng.below(6) {
        0 => {
            let a = [random_circuit(rng, f, nvars, depth - 1)];
            f.not(a[0])
        }
        1 | 2 => {
            let kids: Vec<BoolRef> = (0..2 + rng.below(3))
                .map(|_| random_circuit(rng, f, nvars, depth - 1))
                .collect();
            f.and(&kids)
        }
        3 | 4 => {
            let kids: Vec<BoolRef> = (0..2 + rng.below(3))
                .map(|_| random_circuit(rng, f, nvars, depth - 1))
                .collect();
            f.or(&kids)
        }
        _ => {
            let c = random_circuit(rng, f, nvars, depth - 1);
            let t = random_circuit(rng, f, nvars, depth - 1);
            let e = random_circuit(rng, f, nvars, depth - 1);
            f.ite(c, t, e)
        }
    }
}

fn circuit_satisfiable(f: &BoolFactory, root: BoolRef, nvars: usize) -> bool {
    for mask in 0u128..(1u128 << nvars) {
        let model: Vec<bool> = (0..nvars).map(|i| (mask >> i) & 1 == 1).collect();
        if f.eval(root, &model) {
            return true;
        }
    }
    false
}

#[test]
fn known_sat_and_unsat_circuits() {
    let mut f = BoolFactory::new();
    let x = f.variable();
    let y = f.variable();

    let sat_root = f.or(&[x, y]);
    let mut solver = IpasirSolver::new().unwrap();
    translate_into_solver(&mut solver, &f, sat_root, 2).unwrap();
    assert!(solver.solve());
    let x_val = solver.value_of(x.0 as i64);
    let y_val = solver.value_of(y.0 as i64);
    assert!(f.eval(sat_root, &[x_val, y_val]));

    let unsat_root = f.and(&[x, f.not(x)]);
    let mut solver = IpasirSolver::new().unwrap();
    translate_into_solver(&mut solver, &f, unsat_root, 2).unwrap();
    assert!(!solver.solve());
}

#[test]
fn end_to_end_fuzz_matches_circuit_semantics() {
    let mut rng = Lcg(0xBEEF);
    for case in 0..30 {
        let nvars = 1 + case % 6;
        let mut f = BoolFactory::new();
        for _ in 0..nvars {
            f.variable();
        }
        let root = random_circuit(&mut rng, &mut f, nvars, 4);
        let expected_sat = circuit_satisfiable(&f, root, nvars);

        let mut solver = IpasirSolver::new().unwrap();
        assert_eq!(
            solver.backend_name(),
            "cadical",
            "default backend should be cadical"
        );
        translate_into_solver(&mut solver, &f, root, nvars).unwrap();
        let actual_sat = solver.solve();
        assert_eq!(expected_sat, actual_sat, "case {}", case);

        if expected_sat {
            let primary: Vec<bool> = (1..=nvars as i64).map(|v| solver.value_of(v)).collect();
            assert!(
                f.eval(root, &primary),
                "case {}: caical model {:?} must satisfy the circuit",
                case,
                primary
            );
        }
    }
}
