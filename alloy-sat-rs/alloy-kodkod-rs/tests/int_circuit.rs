use alloy_kodkod_rs::bool::{const_false, const_true, BoolRef};
use alloy_kodkod_rs::{BoolCtx, IntCircuit};

fn decode(bits: &[BoolRef], ctx: &BoolCtx, model: &[bool]) -> i64 {
    let c = IntCircuit::from_bits(bits.to_vec(), ctx);
    c.value_of(model)
}

fn signed(v: i64, width: u32) -> i64 {
    let mask = (1i64 << width) - 1;
    let t = v & mask;
    let sign = 1i64 << (width - 1);
    if t & sign != 0 {
        t - (1i64 << width)
    } else {
        t
    }
}

#[test]
fn constants_encode_twos_complement() {
    let ctx = BoolCtx::new();
    for v in [-8i64, -5, -1, 0, 3, 7] {
        let c = IntCircuit::constant(v, 4, &ctx);
        assert_eq!(c.value_of(&[]), v, "constant {}", v);
    }
}

#[test]
fn bitwise_and_arithmetic_ops_match_wraparound_semantics() {
    let ctx = BoolCtx::new();
    let vars: Vec<BoolRef> = (0..8).map(|_| ctx.variable()).collect();
    let a_bits: Vec<BoolRef> = vars[0..4].to_vec();
    let b_bits: Vec<BoolRef> = vars[4..8].to_vec();
    let a = IntCircuit::from_bits(a_bits.clone(), &ctx);
    let b = IntCircuit::from_bits(b_bits.clone(), &ctx);
    let bw = 4u32;

    for mask in 0u32..256 {
        let model: Vec<bool> = (0..8).map(|i| (mask >> i) & 1 == 1).collect();
        let x = decode(&a_bits, &ctx, &model);
        let y = decode(&b_bits, &ctx, &model);

        assert_eq!(
            a.add(&b, bw).value_of(&model),
            signed(x + y, bw),
            "add {}+{}",
            x,
            y
        );
        assert_eq!(
            a.sub(&b, bw).value_of(&model),
            signed(x - y, bw),
            "sub {}-{}",
            x,
            y
        );
        assert_eq!(
            a.mul(&b, bw).value_of(&model),
            signed(x * y, bw),
            "mul {}*{}",
            x,
            y
        );
        assert_eq!(a.bit_and(&b).value_of(&model), x & y, "and");
        assert_eq!(a.bit_or(&b).value_of(&model), x | y, "or");
        assert_eq!(a.bit_xor(&b).value_of(&model), x ^ y, "xor");
        assert_eq!(a.neg(bw).value_of(&model), signed(-x, bw), "neg {}", x);
        let not_x = signed((!x) & 0xF, bw);
        assert_eq!(a.bit_not().value_of(&model), not_x, "not {}", x);
    }
}

#[test]
fn shifts_shift_by_low_bits_mod_width_like_kodkod() {
    let ctx = BoolCtx::new();
    let vars: Vec<BoolRef> = (0..8).map(|_| ctx.variable()).collect();
    let a = IntCircuit::from_bits(vars[0..4].to_vec(), &ctx);
    let sh = IntCircuit::from_bits(vars[4..8].to_vec(), &ctx);
    let bw = 4u32;

    for mask in 0u32..256 {
        let model: Vec<bool> = (0..8).map(|i| (mask >> i) & 1 == 1).collect();
        let x = decode(&vars[0..4], &ctx, &model);
        let amount = ((decode(&vars[4..8], &ctx, &model) as u64 & 0xF) as usize) % (bw as usize);

        let want_left = signed((((x as u64) << amount) & 0xF) as i64, bw);
        let _ = bw;
        let want_right = signed(((x as u64 & 0xF) >> amount) as i64, bw);
        let sign_fill = if x < 0 { 1u64 } else { 0 };
        let want_arith = signed(((x >> amount) as u64 & 0xF) as i64, bw);
        let _ = sign_fill;

        assert_eq!(
            a.shl(&sh, bw).value_of(&model),
            want_left,
            "shl {}<<{}",
            x,
            amount
        );
        assert_eq!(
            a.shr(&sh, bw).value_of(&model),
            want_right,
            "shr {}>>{}",
            x,
            amount
        );
        assert_eq!(
            a.sha(&sh, bw).value_of(&model),
            want_arith,
            "sha {}>>>{}",
            x,
            amount
        );
    }
}

#[test]
fn comparisons_match_native_ordering() {
    let ctx = BoolCtx::new();
    let vars: Vec<BoolRef> = (0..8).map(|_| ctx.variable()).collect();
    let a = IntCircuit::from_bits(vars[0..4].to_vec(), &ctx);
    let b = IntCircuit::from_bits(vars[4..8].to_vec(), &ctx);

    for mask in 0u32..256 {
        let model: Vec<bool> = (0..8).map(|i| (mask >> i) & 1 == 1).collect();
        let x = decode(&vars[0..4], &ctx, &model);
        let y = decode(&vars[4..8], &ctx, &model);
        assert_eq!(ctx.eval(a.eq(&b), &model), x == y, "eq {}={}", x, y);
        assert_eq!(ctx.eval(a.neq(&b), &model), x != y, "neq");
        assert_eq!(ctx.eval(a.lt(&b), &model), x < y, "lt {}<{}", x, y);
        assert_eq!(ctx.eval(a.lte(&b), &model), x <= y, "lte");
        assert_eq!(ctx.eval(a.gt(&b), &model), x > y, "gt");
        assert_eq!(ctx.eval(a.gte(&b), &model), x >= y, "gte");
    }
}

#[test]
fn choice_selects_per_condition() {
    let ctx = BoolCtx::new();
    let cond = ctx.variable();
    let t_bits: Vec<BoolRef> = vec![const_true(), const_false(), const_false(), const_true()];
    let e_bits: Vec<BoolRef> = vec![const_false(), const_true(), const_true(), const_false()];
    let t = IntCircuit::from_bits(t_bits, &ctx);
    let e = IntCircuit::from_bits(e_bits, &ctx);
    let chosen = t.choice(cond, &e);

    let model_t = [true];
    let model_e = [false];
    assert_eq!(chosen.value_of(&model_t), t.value_of(&[]));
    assert_eq!(chosen.value_of(&model_e), e.value_of(&[]));
}

#[test]
fn division_matches_truncation_for_nonzero_divisors() {
    let ctx = BoolCtx::new();
    let vars: Vec<BoolRef> = (0..8).map(|_| ctx.variable()).collect();
    let a = IntCircuit::from_bits(vars[0..4].to_vec(), &ctx);
    let b = IntCircuit::from_bits(vars[4..8].to_vec(), &ctx);
    let bw = 4u32;

    for mask in 0u32..256 {
        let model: Vec<bool> = (0..8).map(|i| (mask >> i) & 1 == 1).collect();
        let x = decode(&vars[0..4], &ctx, &model);
        let y = decode(&vars[4..8], &ctx, &model);
        if y == 0 {
            continue;
        }
        let raw_q = x / y;
        let want_q = signed((raw_q as u64 & 0xF) as i64, bw);
        let want_r = x % y;
        assert_eq!(a.div(&b, bw).value_of(&model), want_q, "{} div {}", x, y);
        assert_eq!(a.rem(&b, bw).value_of(&model), want_r, "{} rem {}", x, y);
    }
}

#[test]
fn wide_barrel_shift_above_64_bits() {
    // Regression: `shl` evaluated `1usize << i` for every `i < width`,
    // panicking on widths above 64 (widened interval-arithmetic shifts
    // legitimately reach ~108 bits under `for 12 Int`). Only the low
    // ceil(log2(width)) stages do work; the rest must be skipped.
    let ctx = BoolCtx::new();
    // 3215 << 9 = 1646080, exact in 108 bits.
    let base = IntCircuit::constant(3215, 13, &ctx);
    let amount = IntCircuit::constant(9, 8, &ctx);
    assert_eq!(base.shl(&amount, 108).value_of(&[]), 3215i64 << 9);
    // Sign extension survives the widening: -7 << 70.
    let neg = IntCircuit::constant(-7, 5, &ctx);
    let big = IntCircuit::constant(70, 8, &ctx);
    assert_eq!(neg.shl(&big, 108).value_of(&[]), ((-7i128 << 70) as i64));
    // Shift-out past the width drops high bits (zero fill into low part).
    let past = IntCircuit::constant(100, 8, &ctx);
    assert_eq!(
        base.shl(&past, 108).value_of(&[]),
        ((3215i128 << 100) as i64)
    );
    // Variable amount at a wide width, driven by a model.
    let vars: Vec<BoolRef> = (0..8).map(|_| ctx.variable()).collect();
    let v = IntCircuit::from_bits(vars.clone(), &ctx);
    let three = IntCircuit::constant(3, 4, &ctx);
    let model: Vec<bool> = (0..8).map(|i| (70u32 >> i) & 1 == 1).collect();
    assert_eq!(three.shl(&v, 100).value_of(&model), ((3i128 << 70) as i64));
}
