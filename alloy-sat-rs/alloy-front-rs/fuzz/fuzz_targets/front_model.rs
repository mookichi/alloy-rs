#![no_main]

//! Structured fuzz: bytes seed the deterministic model generator; every
//! generated model is checked against the brute-force oracle (solver SAT
//! agreement, validate acceptance, query alignment). Panics on violation.

use alloy_front_rs::fuzzgen::{check_model, gen_model, Rng};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    if data.len() < 8 {
        return;
    }
    let mut rng = Rng::from_bytes(data);
    let src = gen_model(&mut rng);
    let _ = check_model(&src);
});
