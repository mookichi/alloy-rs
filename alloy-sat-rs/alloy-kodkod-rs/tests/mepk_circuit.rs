//! Equivalence tests: S2 circuit primitives vs the `int_ext` oracle, and the
//! symbolic `mepk_*_c` exponent layer vs the concrete `Mepk` oracle.
//!
//! All circuits here take constant inputs and are evaluated with an empty
//! model (constant folding through the gates); variable-bit paths are
//! covered by the shared `int_circuit.rs` harness style.

use alloy_kodkod_rs::bool::BoolRef;
use alloy_kodkod_rs::int_ext;
use alloy_kodkod_rs::mepk::{
    mepk_add, mepk_add_c, mepk_div, mepk_div_c, mepk_mul, mepk_mul_c, Mepk, MepkCircuit,
    MepkWidths,
};
use alloy_kodkod_rs::{BoolCtx, IntCircuit};

fn const_c(v: i64, width: u32, ctx: &BoolCtx) -> IntCircuit {
    IntCircuit::constant(v, width, ctx)
}

/// Decode a bit-vector as unsigned via per-bit evaluation.
fn decode_u(bits: &[BoolRef], ctx: &BoolCtx) -> u128 {
    let mut v: u128 = 0;
    for (i, &b) in bits.iter().enumerate() {
        if ctx.eval(b, &[]) {
            v |= 1u128 << i;
        }
    }
    v
}

fn mepk_const(m: i64, e: i64, p: i64, k: i64, w: &MepkWidths, ctx: &BoolCtx) -> MepkCircuit {
    MepkCircuit::constant(m, e, p, k, w, ctx)
}

// ---- S2: widening ops ------------------------------------------------------

#[test]
fn widen_add_sub_mul_are_exact() {
    let ctx = BoolCtx::new();
    // Exercise warts of truncation: 100+100 overflows i8, 13*17 overflows i8.
    let a = const_c(100, 8, &ctx);
    let b = const_c(100, 8, &ctx);
    assert_eq!(a.widen_add(&b).value_of(&[]), 200);
    assert_eq!(a.widen_sub(&b).value_of(&[]), 0);
    let c = const_c(13, 8, &ctx);
    let d = const_c(17, 8, &ctx);
    assert_eq!(c.widen_mul(&d).value_of(&[]), 221);
    let n = const_c(-7, 8, &ctx);
    assert_eq!(n.widen_mul(&d).value_of(&[]), -119);
    assert_eq!(n.widen_add(&d).value_of(&[]), 10);
}

#[test]
fn shl_const_and_srl_const() {
    let ctx = BoolCtx::new();
    let a = const_c(13, 8, &ctx);
    assert_eq!(a.shl_const(4).value_of(&[]), 13 << 4);
    let n = const_c(-3, 8, &ctx);
    assert_eq!(n.shl_const(2).value_of(&[]), -12);
    // Logical right shift zero-fills: 0b1000_0000 (=-128) >> 1 == 64.
    let top = const_c(-128, 8, &ctx);
    assert_eq!(top.srl_const(1, 8).value_of(&[]), 64);
}

// ---- S2: sign / compare / min-max / bit-length -----------------------------

#[test]
fn abs_mag_and_apply_sign_roundtrip() {
    let ctx = BoolCtx::new();
    for v in [-128i64, -13, -1, 0, 1, 42, 127] {
        let c = const_c(v, 8, &ctx);
        let (mag, neg) = c.abs_to_mag();
        assert_eq!(decode_u(&mag, &ctx), v.unsigned_abs() as u128, "mag {v}");
        assert_eq!(ctx.eval(neg, &[]), v < 0, "neg {v}");
        let back = IntCircuit::apply_sign(&mag, neg, &ctx);
        assert_eq!(back.value_of(&[]), v, "roundtrip {v}");
    }
}

#[test]
fn unsigned_compare_and_signed_minmax() {
    let ctx = BoolCtx::new();
    // -1 signed is 0xFF unsigned: ult must read zero-extended magnitudes.
    let minus_one = const_c(-1, 8, &ctx);
    let one = const_c(1, 8, &ctx);
    assert!(ctx.eval(one.ult(&minus_one), &[]));
    assert!(!ctx.eval(minus_one.ult(&one), &[]));
    assert!(ctx.eval(one.ule(&one), &[]));
    assert!(ctx.eval(one.ule(&minus_one), &[]));
    let three = const_c(3, 8, &ctx);
    let seven = const_c(7, 8, &ctx);
    assert_eq!(three.max_c(&seven).value_of(&[]), 7);
    assert_eq!(three.min_c(&seven).value_of(&[]), 3);
    assert_eq!(minus_one.max_c(&one).value_of(&[]), 1);
    assert_eq!(minus_one.min_c(&one).value_of(&[]), -1);
}

#[test]
fn bit_len_c_matches_oracle() {
    let ctx = BoolCtx::new();
    for v in [0i64, 1, 2, 3, 5, 15, 16, 100, 127, -1, -128, -100] {
        let c = const_c(v, 8, &ctx);
        let bl = c.bit_len_c().value_of(&[]) as u32;
        assert_eq!(bl, int_ext::bit_len(v.unsigned_abs() as u128), "bitlen {v}");
    }
}

// ---- S2: rounding / division vs oracle -------------------------------------

#[test]
fn round_mag_const_drop_matches_oracle() {
    let ctx = BoolCtx::new();
    // (raw, p) grid incl. ties, carry-out renormalize, negatives.
    let cases: &[(i64, u32)] = &[
        (15, 3),
        (16, 3),
        (100, 5),
        (255, 8),
        (255, 4),
        (-15, 3),
        (-100, 5),
        (7, 3),
        (127, 7),
        (1023, 5),
        (1, 1),
        (3, 1),
        (5, 2),
    ];
    for &(raw, p) in cases {
        let w = 12u32;
        let c = const_c(raw, w, &ctx);
        let bl = int_ext::bit_len(raw.unsigned_abs() as u128);
        if bl <= p {
            continue; // zero-fill path: no drop needed.
        }
        let drop = bl - p;
        let (field, carry) = c.round_mag_const_drop_c(drop, p);
        assert_eq!(field.len() as u32, p);
        let (exp_m, _) = int_ext::round_to_precision_raw(raw as i128, 0, p).unwrap();
        let exp_mag = exp_m.unsigned_abs();
        let carry_v = ctx.eval(carry, &[]);
        if carry_v {
            // Renormalize case: field wrapped to 0, oracle magnitude is 2^(p-1).
            assert_eq!(decode_u(&field, &ctx), 0, "field raw={raw} p={p}");
            assert_eq!(exp_mag, 1u128 << (p - 1), "oracle raw={raw} p={p}");
        } else {
            assert_eq!(decode_u(&field, &ctx), exp_mag, "round raw={raw} p={p}");
        }
    }
}

#[test]
fn div_nearest_wide_matches_oracle() {
    let ctx = BoolCtx::new();
    let cases: &[(i64, i64, u32)] = &[
        (100, 50, 4),
        (1, 2, 4),
        (1, 3, 4),
        (2, 3, 4),
        (3, 2, 0),
        (5, 2, 0),
        (-7, 2, 4),
        (7, -2, 4),
        (-7, -2, 0),
        (127, 3, 6),
    ];
    for &(m1, m2, guard) in cases {
        let a = const_c(m1, 10, &ctx);
        let b = const_c(m2, 10, &ctx);
        let (q, round_up, neg, dbz) = a.div_nearest_wide(&b, guard);
        assert!(!ctx.eval(dbz, &[]), "dbz {m1}/{m2}");
        assert_eq!(ctx.eval(neg, &[]), (m1 < 0) != (m2 < 0));
        // Quotients on this grid are narrow and non-negative by construction,
        // so signed `value_of` decodes them exactly.
        let q0 = q.value_of(&[]) as u128;
        let trunc = ((m1.unsigned_abs() as u128) << guard) / (m2.unsigned_abs() as u128);
        assert_eq!(q0, trunc, "truncated q {m1}/{m2} g={guard}");
        let up = ctx.eval(round_up, &[]);
        let rounded = q0 + (up as u128);
        let oracle = int_ext::scaled_div_nearest(
            m1.unsigned_abs() as u128,
            m2.unsigned_abs() as u128,
            guard,
        )
        .unwrap();
        assert_eq!(rounded, oracle, "rounded q {m1}/{m2} g={guard}");
    }
}

// ---- S3: symbolic exponent layer vs concrete oracle ------------------------

fn check_add(x1: Mepk, x2: Mepk, sign: i8, w: &MepkWidths) {
    let ctx = BoolCtx::new();
    let a = mepk_const(x1.m as i64, x1.e as i64, x1.p as i64, x1.k as i64, w, &ctx);
    let b = mepk_const(x2.m as i64, x2.e as i64, x2.p as i64, x2.k as i64, w, &ctx);
    let res = mepk_add_c(&a, &b, sign, w);
    let exp = mepk_add(&x1, &x2, sign).unwrap();
    assert_eq!(res.p.value_of(&[]), exp.p as i64, "p");
    assert_eq!(res.e.value_of(&[]), exp.e as i64, "e");
    assert_eq!(res.k.value_of(&[]), exp.k as i64, "k");
}

#[test]
fn symbolic_add_matches_concrete() {
    let w = MepkWidths::uniform(10);
    // MepkOpsTest.addSubKRule values.
    let x1 = Mepk::new(100, 6, 8, 1).unwrap();
    let x2 = Mepk::new(50, 5, 8, 2).unwrap();
    check_add(x1, x2, 1, &w);
    check_add(x1, x2, -1, &w);
    // Cancellation to zero: T = 0 -> e' = ell + p' - 1.
    let z1 = Mepk::new(4, 2, 3, 0).unwrap();
    let z2 = Mepk::new(4, 2, 3, 1).unwrap();
    check_add(z1, z2, -1, &w);
    // Mixed precisions.
    let m1 = Mepk::new(127, 6, 8, 1).unwrap();
    let m2 = Mepk::new(63, 5, 7, 2).unwrap();
    check_add(m1, m2, 1, &w);
    // Negative operands.
    let n1 = Mepk::new(-100, 6, 8, 1).unwrap();
    check_add(n1, x2, 1, &w);
    check_add(n1, x2, -1, &w);
}

#[test]
fn symbolic_mul_matches_concrete() {
    let w = MepkWidths::uniform(10);
    let cases = [
        (Mepk::new(127, 6, 8, 1).unwrap(), Mepk::new(63, 5, 7, 2).unwrap()),
        (Mepk::new(100, 6, 8, 1).unwrap(), Mepk::new(50, 5, 8, 2).unwrap()),
        (Mepk::new(-6, 2, 4, 0).unwrap(), Mepk::new(7, 2, 4, 1).unwrap()),
        (Mepk::new(1, 0, 3, 0).unwrap(), Mepk::new(1, 0, 3, 0).unwrap()),
    ];
    for (x1, x2) in cases {
        let ctx = BoolCtx::new();
        let a = mepk_const(x1.m as i64, x1.e as i64, x1.p as i64, x1.k as i64, &w, &ctx);
        let b = mepk_const(x2.m as i64, x2.e as i64, x2.p as i64, x2.k as i64, &w, &ctx);
        let res = mepk_mul_c(&a, &b, &w);
        let exp = mepk_mul(&x1, &x2).unwrap();
        assert_eq!(res.p.value_of(&[]), exp.p as i64, "p {x1:?}*{x2:?}");
        assert_eq!(res.e.value_of(&[]), exp.e as i64, "e {x1:?}*{x2:?}");
        assert_eq!(res.k.value_of(&[]), exp.k as i64, "k {x1:?}*{x2:?}");
    }
}

#[test]
fn symbolic_div_matches_concrete_and_guards() {
    let w = MepkWidths::uniform(12).with_guard(4);
    let num = Mepk::new(100, 6, 8, 1).unwrap();
    let den = Mepk::new(50, 5, 8, 1).unwrap();
    let ctx = BoolCtx::new();
    let a = mepk_const(num.m as i64, num.e as i64, num.p as i64, num.k as i64, &w, &ctx);
    let b = mepk_const(den.m as i64, den.e as i64, den.p as i64, den.k as i64, &w, &ctx);
    let (res, undef) = mepk_div_c(&a, &b, &w);
    assert!(!ctx.eval(undef, &[]));
    let exp = mepk_div(&num, &den, 4).unwrap();
    assert_eq!(res.p.value_of(&[]), exp.p as i64, "p");
    assert_eq!(res.e.value_of(&[]), exp.e as i64, "e");
    assert_eq!(res.k.value_of(&[]), exp.k as i64, "k");
    // Precondition violation -> undef flag (UNSAT gate), concrete -> None.
    let bad = Mepk::new(50, 5, 4, 4).unwrap();
    let ctx2 = BoolCtx::new();
    let nb = mepk_const(num.m as i64, num.e as i64, num.p as i64, num.k as i64, &w, &ctx2);
    let bb = mepk_const(bad.m as i64, bad.e as i64, bad.p as i64, bad.k as i64, &w, &ctx2);
    let (_, undef2) = mepk_div_c(&nb, &bb, &w);
    assert!(ctx2.eval(undef2, &[]));
    assert!(mepk_div(&num, &bad, 4).is_none());
}

// ---- carry contract: e' lower estimate, k' conservative -------------------
// A round-up carry bumps the true exponent past E0 (bit length of the
// unrounded total) by one. Symbolic lanes must satisfy
// `oracle_e - sym_e ∈ {0, 1}` and `sym_k - oracle_k ∈ {0, 1}`.

#[test]
fn symbolic_carry_within_contract() {
    let w = MepkWidths::uniform(10);
    // T = 101 at p' = 1 rounds 1 -> 2 -> renormalize: oracle e = 6,
    // symbolic E0 = -1 + bitlen(101) - 1 = 5.
    let x1 = Mepk::new(100, 6, 8, 1).unwrap();
    let x2 = Mepk::new(1, -1, 1, 0).unwrap();
    let ctx = BoolCtx::new();
    let a = mepk_const(x1.m as i64, x1.e as i64, x1.p as i64, x1.k as i64, &w, &ctx);
    let b = mepk_const(x2.m as i64, x2.e as i64, x2.p as i64, x2.k as i64, &w, &ctx);
    let res = mepk_add_c(&a, &b, 1, &w);
    let exp = mepk_add(&x1, &x2, 1).unwrap();
    assert_eq!(res.p.value_of(&[]), exp.p as i64, "p exact");
    let se = res.e.value_of(&[]);
    let sk = res.k.value_of(&[]);
    assert!(
        (0..=1).contains(&(exp.e as i64 - se)),
        "e contract: oracle {} vs sym {se}",
        exp.e
    );
    assert!(
        (0..=1).contains(&(sk - exp.k as i64)),
        "k contract: sym {sk} vs oracle {}",
        exp.k
    );
    // This instance does carry: pin the direction (E0 below oracle).
    assert_eq!((se, exp.e), (5, 6));
}

// ---- widths from environment ------------------------------------------------

#[test]
fn widths_from_env() {
    // Single test owns the process-global env keys end-to-end (set -> read ->
    // remove) so parallel tests (which never call from_env) are unaffected.
    let keys = [
        "MEPK_M_WIDTH",
        "MEPK_E_WIDTH",
        "MEPK_P_WIDTH",
        "MEPK_K_WIDTH",
        "MEPK_GUARD",
    ];
    for k in keys {
        std::env::remove_var(k);
    }
    let d = MepkWidths::from_env(4).unwrap();
    // Rule-based default for int_count=4: E=5, M=5, w_exp=4, guard=4.
    assert_eq!(d, MepkWidths::from_rule(4));
    assert_eq!((d.m_width, d.e_width, d.p_width, d.k_width, d.guard), (5, 4, 4, 4, 4));
    std::env::set_var("MEPK_M_WIDTH", "8");
    std::env::set_var("MEPK_E_WIDTH", "6");
    std::env::set_var("MEPK_GUARD", "2");
    let c = MepkWidths::from_env(4).unwrap();
    assert_eq!(c.m_width, 8);
    assert_eq!(c.e_width, 6);
    assert_eq!(c.p_width, 4);
    assert_eq!(c.guard, 2);
    std::env::set_var("MEPK_K_WIDTH", "bogus");
    assert!(MepkWidths::from_env(4).is_err());
    std::env::set_var("MEPK_K_WIDTH", "99");
    assert!(MepkWidths::from_env(4).is_err());
    for k in keys {
        std::env::remove_var(k);
    }
}
