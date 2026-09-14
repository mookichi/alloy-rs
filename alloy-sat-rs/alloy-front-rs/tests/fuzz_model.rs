//! Deterministic structured fuzz: random tiny models checked against the
//! brute-force oracle. Same generator the libfuzzer targets use.

use alloy_front_rs::fuzzgen::{check_model, gen_model, Outcome, Rng};

#[test]
fn fuzz_seeds_agree_with_oracle() {
    let mut checked = 0usize;
    let mut skipped: std::collections::HashMap<&'static str, usize> =
        std::collections::HashMap::new();
    // 400 seeds; each tiny case solves in milliseconds.
    for seed in 0..400u64 {
        let mut rng = Rng::from_seed(seed.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(seed));
        let src = gen_model(&mut rng);
        match check_model(&src) {
            Outcome::Checked => checked += 1,
            Outcome::Skipped(reason) => {
                *skipped.entry(reason).or_default() += 1;
            }
        }
    }
    eprintln!("checked={checked} skipped={skipped:?}");
    // The generator must yield a healthy mix, not all-skips.
    assert!(checked >= 100, "too few checked cases: {checked}");
}
