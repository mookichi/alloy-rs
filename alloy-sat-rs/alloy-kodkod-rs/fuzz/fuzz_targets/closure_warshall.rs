#![no_main]

//! Invariant: BooleanMatrix::closure_transitive must equal a naive Warshall
//! reference for arbitrary (pseudo-random) sparse relations, including
//! cyclic ones.

use alloy_kodkod_rs::bmatrix::BooleanMatrix;
use alloy_kodkod_rs::bool::const_true;
use alloy_kodkod_rs::dimensions::Dimensions;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    if data.len() < 4 {
        return;
    }
    let n = ((data[0] as usize) % 12) + 2; // matrix size 2..=13
    let dims = Dimensions::square(n as u32, 2).unwrap();
    let ctx = alloy_kodkod_rs::BoolCtx::new();
    let mut m = BooleanMatrix::new(dims.clone(), &ctx);
    let mut edges = vec![vec![false; n]; n];
    for (i, &b) in data.iter().enumerate().skip(1) {
        let r = (b as usize + i) % n;
        let c = ((b as usize >> 4) ^ i) % n;
        if !edges[r][c] {
            edges[r][c] = true;
            m.set(r * n + c, const_true()).unwrap();
        }
        if i > 40 {
            break;
        }
    }

    // engine closure
    let got = m.closure_transitive().unwrap();
    let model_all_true = vec![true; got.dims().capacity() + 1];
    let dense = got.eval_dense(&model_all_true);

    // naive Warshall oracle
    let mut refc = edges.clone();
    for k in 0..n {
        for x in 0..n {
            if refc[x][k] {
                for y in 0..n {
                    if refc[k][y] {
                        refc[x][y] = true;
                    }
                }
            }
        }
    }
    for x in 0..n {
        for y in 0..n {
            assert_eq!(
                dense[x * n + y],
                refc[x][y],
                "closure mismatch at ({x},{y}) n={n}"
            );
        }
    }
});
