//! Cost-measurement prototype: exact-centre pin for add/sub
//! (`mepk_add_c_exact`) vs the production exponent-only `mepk_add_c`.
//!
//! NOT production code: it exists to quantify, with real gate counts,
//! what exact-pin would cost. Scope notes (all documented in-test):
//! - `p_new` is a *constant* (production needs variable `p' = min(pa,pb)`;
//!   the case split below would multiply out further).
//! - only add/sub (`T` exact total); mul/div would add their own heads.
//! - ties-to-even is bit-exact (matches [`mepk_add`] oracle).
//!
//! Findings are summarized in the review report; the two
//! `gate_count_*` tests pin the measured ratios.

use alloy_kodkod_rs::bool::{const_false, const_true, BoolRef};
use alloy_kodkod_rs::mepk::{mepk_add, mepk_add_c, Mepk, MepkCircuit, MepkWidths};
use alloy_kodkod_rs::{BoolCtx, IntCircuit};

fn const_c(v: i64, width: u32, ctx: &BoolCtx) -> IntCircuit {
    IntCircuit::constant(v, width, ctx)
}

fn mepk_const(m: i64, e: i64, p: i64, k: i64, w: &MepkWidths, ctx: &BoolCtx) -> MepkCircuit {
    MepkCircuit::constant(m, e, p, k, w, ctx)
}

/// Safe magnitude-bit read (zero past the end; magnitudes are unsigned).
fn mag_bit(mag: &[BoolRef], i: usize) -> BoolRef {
    if i < mag.len() {
        mag[i]
    } else {
        const_false()
    }
}

/// Exact-centre add/sub over free-variable inputs at constant `p_new`.
///
/// Returns `(m_exact, e_exact)` circuits equal (as integers) to the oracle
/// `round_to_precision(T, ell, p_new)` on every input. Construction:
/// - `T`, `ell` exactly as in [`mepk_add_c`] (doubled-`m` barrel + widen);
/// - `bl = bitlen(|T|)` via [`IntCircuit::bit_len_c`];
/// - case split over `bl = 0..=T_WIDTH`: zero-fill path (`bl <= p_new`,
///   constant left shift, no rounding, no carry) vs constant-`drop`
///   rounding ([`IntCircuit::round_mag_const_drop_c`], ties-to-even,
///   carry-out renormalize + `e + 1`), all muxed with `choice`
///   (`cond ? new : prev`).
fn mepk_add_c_exact(
    x1: &MepkCircuit,
    x2: &MepkCircuit,
    sign: i8,
    p_new: u32,
    w: &MepkWidths,
) -> (IntCircuit, IntCircuit) {
    assert!(sign == 1 || sign == -1);
    assert!(p_new >= 1);
    assert!(w.e_width >= 1);
    let ctx = x1.ctx().clone();
    let ew = w.e_width;
    let lsb1 = x1.lsb_c(w);
    let lsb2 = x2.lsb_c(w);
    let ell = lsb1.min_c(&lsb2);
    let d1 = lsb1.sub(&ell, ew);
    let d2 = lsb2.sub(&ell, ew);
    let mw2 = w.m_width * 2;
    let a_promoted = IntCircuit::from_bits(
        (0..mw2 as usize).map(|i| x1.m.bit(i)).collect(),
        &ctx,
    );
    let b_promoted = IntCircuit::from_bits(
        (0..mw2 as usize).map(|i| x2.m.bit(i)).collect(),
        &ctx,
    );
    let a_aligned = a_promoted.shl(&d1, mw2);
    let b_aligned = b_promoted.shl(&d2, mw2);
    let t = if sign == 1 {
        a_aligned.widen_add(&b_aligned)
    } else {
        a_aligned.widen_sub(&b_aligned)
    };
    let tw = t.width();
    let bl = t.bit_len_c();
    let (tmag, tneg) = t.abs_to_mag();
    let tmag_c = IntCircuit::from_bits(tmag.clone(), &ctx);
    // `E0 = ell + bl - 1` (nonzero) shared by all cases.
    let one_ew = const_c(1, ew, &ctx);
    let e0_nz = ell.add(&bl, ew).sub(&one_ew, ew);
    // Fold cases in: `sel = cond ? case : sel`.
    let mut m_sel: Option<IntCircuit> = None;
    let mut e_sel: Option<IntCircuit> = None;
    let mut take_case = |cond: BoolRef, m_mag: IntCircuit, e: IntCircuit| {
        match m_sel.take() {
            None => {
                m_sel = Some(m_mag);
                e_sel = Some(e);
            }
            Some(prev_m) => {
                let prev_e = e_sel.take().unwrap();
                m_sel = Some(m_mag.choice(cond, &prev_m));
                e_sel = Some(e.choice(cond, &prev_e));
            }
        }
    };
    for blv in 0..=(tw as u32) {
        let cond = bl.eq(&const_c(blv as i64, bl.width() as u32, &ctx));
        // All magnitude fields are `p_new + 1` bits (extra zero on top):
        // a `p`-bit normalized magnitude reaches `2^p − 1`, which needs
        // `p + 1` bits signed. Without the spare bit the top magnitude
        // bit would read as a sign bit (e.g. 250 at p = 8 reads as −6).
        let spare = |mut field: Vec<BoolRef>| {
            field.push(const_false());
            field
        };
        if blv == 0 {
            // `T = 0`: `(0, ell + p' - 1)` (oracle zero rule).
            let p_c = const_c(p_new as i64, ew, &ctx);
            let e_z = ell.add(&p_c, ew).sub(&one_ew, ew);
            let m_z = IntCircuit::apply_sign(
                &spare((0..p_new as usize).map(|_| const_false()).collect()),
                tneg,
                &ctx,
            );
            take_case(cond, m_z, e_z);
        } else if blv <= p_new {
            // Zero-fill: `m = |T| << (p' - bl)`, `e = E0`, no carry.
            // `|T| < 2^blv` shifted by `p' - blv` fits `p'` bits exactly.
            let sh = (p_new - blv) as usize;
            let field: Vec<BoolRef> = (0..p_new as usize)
                .map(|i| {
                    if i < sh {
                        const_false()
                    } else {
                        mag_bit(&tmag, i - sh)
                    }
                })
                .collect();
            let m_case = IntCircuit::apply_sign(&spare(field), tneg, &ctx);
            take_case(cond, m_case, e0_nz.clone());
        } else {
            // Drop path: constant-drop ties-to-even + carry renormalize.
            let drop = blv - p_new;
            let (field, carry) = tmag_c.round_mag_const_drop_c(drop, p_new);
            // On carry-out the field wrapped to 0: renormalize to `2^(p-1)`.
            let renorm: Vec<BoolRef> = (0..p_new as usize)
                .map(|i| {
                    if i == (p_new - 1) as usize {
                        const_true()
                    } else {
                        const_false()
                    }
                })
                .collect();
            let renorm_c = IntCircuit::from_bits(renorm, &ctx);
            let field_c = IntCircuit::from_bits(field, &ctx);
            // `choice(cond, other) = cond ? self : other`: carry selects
            // the renormalized `2^(p-1)`, otherwise the rounded field.
            let mag_case = renorm_c.choice(carry, &field_c);
            // Spare top bit is constant zero (both alternatives are
            // `< 2^p_new` by construction).
            let mag_ext: Vec<BoolRef> = (0..p_new as usize)
                .map(|i| mag_case.bit(i))
                .chain(std::iter::once(const_false()))
                .collect();
            let m_case = IntCircuit::apply_sign(&mag_ext, tneg, &ctx);
            // `e = E0 + carry`.
            let cbit = IntCircuit::from_bits(
                std::iter::once(carry)
                    .chain((1..ew as usize).map(|_| const_false()))
                    .collect(),
                &ctx,
            );
            let e_case = e0_nz.add(&cbit, ew);
            take_case(cond, m_case, e_case);
        }
    }
    (m_sel.expect("at least bl=0 case"), e_sel.expect("paired e"))
}

// ---------------------------------------------------------------------------
// Differential: prototype centres vs the concrete oracle on constants.
// ---------------------------------------------------------------------------

#[test]
fn exact_proto_matches_oracle_grid() {
    let w = MepkWidths::uniform(10);
    let p_new = 8u32;
    // (m1, e1, m2, e2, sign): ties, carry-out renormalize, zero-fill,
    // cancellation to zero, negatives, mixed magnitudes.
    let cases: &[(i64, i64, i64, i64, i8)] = &[
        (100, 6, 50, 5, 1),
        (100, 6, 50, 5, -1),
        (15, 0, 1, 0, 1),
        (100, 6, 1, -1, 1),
        (4, 2, 4, 2, -1), // exact cancellation to zero
        (0, 3, 50, 5, 1), // zero addend
        (-100, 6, 50, 5, 1),
        (-100, 6, 50, 5, -1),
        (127, 6, 63, 5, 1),
        (1, 0, 1, 0, 1),
        (1, 0, -1, 0, 1), // cancellation of ones
        (3, 0, 5, 0, 1),
        (7, 2, 7, 2, 1),
        (96, 3, 32, 2, -1),
        (-7, 2, -7, 2, -1),
    ];
    for &(m1, e1, m2, e2, sign) in cases {
        let x1 = Mepk::new(m1 as i128, e1 as i32, 8, 1).unwrap();
        let x2 = Mepk::new(m2 as i128, e2 as i32, 8, 1).unwrap();
        let exp = mepk_add(&x1, &x2, sign).unwrap();
        // Oracle p' must equal the prototype's constant for comparison.
        assert_eq!(exp.p, p_new);
        let ctx = BoolCtx::new();
        let a = mepk_const(m1, e1, 8, 1, &w, &ctx);
        let b = mepk_const(m2, e2, 8, 1, &w, &ctx);
        let (m_c, e_c) = mepk_add_c_exact(&a, &b, sign, p_new, &w);
        assert_eq!(m_c.value_of(&[]), exp.m as i64, "m {x1:?} {x2:?}");
        assert_eq!(e_c.value_of(&[]), exp.e as i64, "e {x1:?} {x2:?}");
    }
}

#[test]
fn exact_proto_matches_oracle_fuzz() {
    // Deterministic xorshift over small lanes (p' = 8 fixed by inputs).
    let w = MepkWidths::uniform(10);
    let mut s: u64 = 0x9E3779B97F4A7C15;
    let mut next = move || {
        s ^= s >> 12;
        s ^= s << 25;
        s ^= s >> 27;
        s = s.wrapping_mul(0x2545F4914F6CDD1D);
        s
    };
    for _ in 0..300 {
        let m1 = (next() % 201) as i64 - 100;
        let m2 = (next() % 201) as i64 - 100;
        let e1 = (next() % 9) as i64 - 2;
        let e2 = (next() % 9) as i64 - 2;
        let sign = if next() & 1 == 1 { 1 } else { -1 };
        let (Some(x1), Some(x2)) = (
            Mepk::new(m1 as i128, e1 as i32, 8, (next() % 4) as i32),
            Mepk::new(m2 as i128, e2 as i32, 8, (next() % 4) as i32),
        ) else {
            continue;
        };
        let Some(exp) = mepk_add(&x1, &x2, sign) else {
            continue;
        };
        assert_eq!(exp.p, 8);
        let ctx = BoolCtx::new();
        let a = mepk_const(m1, e1, 8, x1.k as i64, &w, &ctx);
        let b = mepk_const(m2, e2, 8, x2.k as i64, &w, &ctx);
        let (m_c, e_c) = mepk_add_c_exact(&a, &b, sign, 8, &w);
        assert_eq!(m_c.value_of(&[]), exp.m as i64, "m {x1:?} {x2:?} s={sign}");
        assert_eq!(e_c.value_of(&[]), exp.e as i64, "e {x1:?} {x2:?} s={sign}");
    }
}

// ---------------------------------------------------------------------------
// Gate counts: exact-pin add-on cost over free-variable inputs.
// ---------------------------------------------------------------------------

/// Build `mepk_add_c` (production shape) over free inputs; return slots.
fn build_current_free(w: &MepkWidths, sign: i8) -> usize {
    let ctx = BoolCtx::new();
    let x1 = MepkCircuit::free(w, &ctx);
    let x2 = MepkCircuit::free(w, &ctx);
    let _ = mepk_add_c(&x1, &x2, sign, w);
    ctx.num_slots()
}

/// Build the exact-centre prototype over free inputs; return slots.
fn build_exact_free(w: &MepkWidths, sign: i8, p_new: u32) -> usize {
    let ctx = BoolCtx::new();
    let x1 = MepkCircuit::free(w, &ctx);
    let x2 = MepkCircuit::free(w, &ctx);
    let _ = mepk_add_c_exact(&x1, &x2, sign, p_new, w);
    ctx.num_slots()
}

#[test]
fn gate_count_exact_vs_window() {
    // uniform(10) lanes, p' = 8: prints the ratio; asserts the exact
    // add-on costs a multiple (locks the estimate against silent blowup
    // in either direction).
    let w = MepkWidths::uniform(10);
    let cur = build_current_free(&w, 1);
    let exact = build_exact_free(&w, 1, 8);
    eprintln!("slots: current(window)={cur} exact-pin={exact}");
    assert!(cur > 0 && exact > cur);
    let ratio = exact as f64 / cur as f64;
    assert!(
        (1.5..=12.0).contains(&ratio),
        "exact/window slot ratio out of expected band: {ratio} ({cur} vs {exact})"
    );
    // Subtraction head shares the shape (sanity: same order).
    let cur_s = build_current_free(&w, -1);
    let exact_s = build_exact_free(&w, -1, 8);
    let ratio_s = exact_s as f64 / cur_s as f64;
    assert!(
        (1.5..=12.0).contains(&ratio_s),
        "sub ratio out of band: {ratio_s}"
    );
}

#[test]
fn gate_count_default_widths() {
    // Same measurement at default-like lanes (m = 5, p' = 4).
    let w = MepkWidths::uniform(5);
    let cur = build_current_free(&w, 1);
    let exact = build_exact_free(&w, 1, 4);
    eprintln!("slots(default): current(window)={cur} exact-pin={exact}");
    assert!(cur > 0 && exact > cur);
    let ratio = exact as f64 / cur as f64;
    assert!(
        (1.2..=12.0).contains(&ratio),
        "default-width ratio out of band: {ratio} ({cur} vs {exact})"
    );
}
