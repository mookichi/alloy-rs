//! Pure (concrete, `i128`) integer primitives underpinning the
//! `(m, e, p, k)` error-tracking pseudo-real format (`mepk_formal.md`).
//!
//! This module is the SAT-free oracle: the symbolic circuits in
//! [`crate::int`] / `mepk.rs` must agree with these functions on all
//! in-range inputs. Port of the Java oracle `MepkOps.java`
//! (`roundToPrecision`, guard-bit division, `combine_k`), restricted to
//! `i128` (no `num-bigint` dependency). Out-of-range inputs return `None`.

/// `combine_k(A, B) = max(A - B, 0) + 1` (theory §2).
#[inline]
pub fn combine_k(a: i32, b: i32) -> i32 {
    a.saturating_sub(b).max(0) + 1
}

/// Weight of the least significant bit: `lsb = e - p + 1`.
#[inline]
pub fn lsb(e: i32, p: i32) -> i32 {
    e - p + 1
}

/// Exponent of the error radius: `R = 2^(e - p + k)`.
#[inline]
pub fn radius_exp(e: i32, p: i32, k: i32) -> i32 {
    e - p + k
}

/// Bit length of a magnitude: `0 -> 0`, else `128 - leading_zeros`.
#[inline]
pub fn bit_len(mag: u128) -> u32 {
    128 - mag.leading_zeros()
}

/// Absolute value split into `(magnitude, negative)`.
#[inline]
pub fn abs_parts(v: i128) -> (u128, bool) {
    if v < 0 {
        // `i128::MIN.abs()` would overflow; handle via unsigned arithmetic.
        let mag = (v as u128).wrapping_neg();
        (mag, true)
    } else {
        (v as u128, false)
    }
}

/// Round-to-nearest (ties-to-even) integer `raw` at scale `raw_lsb` to a
/// `p`-bit normalized mantissa. Returns `(m', e')`.
///
/// Mirrors `MepkOps.roundToPrecision`: `bitLen <= p` is zero-fill with no
/// rounding error; otherwise drop `bitLen - p` bits, compare `rest` against
/// `half = 1 << (drop - 1)`, round up on `rest > half` or
/// (`rest == half` and `kept` odd), renormalizing on carry-out (`e += 1`).
/// Zero maps to `(0, raw_lsb + p - 1)`. Returns `None` when `p == 0`,
/// `p > 127`, or the result does not fit in `i128`.
pub fn round_to_precision_raw(raw: i128, raw_lsb: i32, p: u32) -> Option<(i128, i32)> {
    if p == 0 || p > 127 {
        return None;
    }
    if raw == 0 {
        let e = raw_lsb.checked_add(p as i32)?.checked_sub(1)?;
        return Some((0, e));
    }
    let (mag, neg) = abs_parts(raw);
    let bl = bit_len(mag);
    let e_base = raw_lsb.checked_add(bl as i32)?.checked_sub(1)?;
    if bl <= p {
        let shift = p - bl;
        let m_mag = mag.checked_shl(shift)?;
        if m_mag > i128::MAX as u128 {
            return None;
        }
        let m = if neg { -(m_mag as i128) } else { m_mag as i128 };
        return Some((m, e_base));
    }
    let drop = bl - p;
    // `drop >= 1` here; `drop - 1 < 127` since `bl <= 128` and `p >= 1`.
    let kept = mag >> drop;
    let rest_mask = if drop >= 128 { u128::MAX } else { (1u128 << drop) - 1 };
    let rest = mag & rest_mask;
    let half = 1u128 << (drop - 1);
    let mut kept = kept;
    let mut e = e_base;
    if rest > half || (rest == half && (kept & 1) == 1) {
        kept += 1;
        if bit_len(kept) > p {
            kept >>= 1;
            e = e.checked_add(1)?;
        }
    }
    if kept > i128::MAX as u128 {
        return None;
    }
    let m = if neg { -(kept as i128) } else { kept as i128 };
    Some((m, e))
}

/// Round-half-to-even helper shared by division: given quotient `q`,
/// remainder `rem` and positive denominator magnitude `den`, bump `q`
/// when `2*rem > den` or (`2*rem == den` and `q` odd).
pub fn round_half_even_step(q: u128, rem: u128, den: u128) -> Option<u128> {
    if den == 0 {
        return None;
    }
    let twice = rem.checked_mul(2)?;
    if twice > den || (twice == den && (q & 1) == 1) {
        q.checked_add(1)
    } else {
        Some(q)
    }
}

/// Scaled integer division with round-to-nearest on the guard bits:
/// `q0 = (m1_mag << guard) / m2_mag`, rounded via [`round_half_even_step`].
/// Returns `None` on `m2_mag == 0`, `guard >= 128`, or overflow.
pub fn scaled_div_nearest(m1_mag: u128, m2_mag: u128, guard: u32) -> Option<u128> {
    if m2_mag == 0 || guard >= 128 {
        return None;
    }
    let num = m1_mag.checked_shl(guard)?;
    let q0 = num.checked_div(m2_mag)?;
    let rem = num.checked_rem(m2_mag)?;
    round_half_even_step(q0, rem, m2_mag)
}

/// §3 addition exponent: `A = ell + max(k1 + d1, k2 + d2)`.
#[inline]
pub fn add_a(ell: i32, k1: i32, d1: i32, k2: i32, d2: i32) -> i32 {
    ell + (k1 + d1).max(k2 + d2)
}

/// §4 multiplication exponent:
/// `C = e1 + e2 + max(k1-p1+1, k2-p2+1, k1+k2-p1-p2) + 2`.
#[inline]
pub fn mul_c(e1: i32, e2: i32, k1: i32, p1: i32, k2: i32, p2: i32) -> i32 {
    let t1 = k1 - p1 + 1;
    let t2 = k2 - p2 + 1;
    let t3 = (k1 + k2) - (p1 + p2);
    e1 + e2 + t1.max(t2).max(t3) + 2
}

/// §5 division exponent: `D = e1 - e2 + max(k1-p1, k2-p2) + 3`.
#[inline]
pub fn div_d(e1: i32, e2: i32, k1: i32, p1: i32, k2: i32, p2: i32) -> i32 {
    (e1 - e2) + (k1 - p1).max(k2 - p2) + 3
}

/// §5 division precondition: denominator interval cannot span zero
/// iff `k2 < p2`.
#[inline]
pub fn div_guard(k2: i32, p2: i32) -> bool {
    k2 < p2
}

/// CEGAR budget: `tau = p - k - g` (theory §7).
#[inline]
pub fn accuracy_tau(p: i32, k: i32, g: i32) -> i32 {
    (p - k) - g
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn combine_k_grid() {
        assert_eq!(combine_k(3, 5), 1);
        assert_eq!(combine_k(5, 5), 1);
        assert_eq!(combine_k(8, 5), 4);
        for a in -4..=8 {
            for b in -4..=8 {
                let k = combine_k(a, b);
                assert!(k >= 1);
                assert!(b + k >= a);
            }
        }
    }

    #[test]
    fn round_short_zero_fills() {
        // 5 (0b101) at lsb 0, p=8 -> 5 << 5, e = 2.
        let (m, e) = round_to_precision_raw(5, 0, 8).unwrap();
        assert_eq!(m, 5 << 5);
        assert_eq!(e, 2);
    }

    #[test]
    fn round_zero_maps() {
        assert_eq!(round_to_precision_raw(0, 3, 8).unwrap(), (0, 3 + 8 - 1));
    }

    #[test]
    fn round_rejects_bad_p() {
        assert!(round_to_precision_raw(1, 0, 0).is_none());
        assert!(round_to_precision_raw(1, 0, 128).is_none());
    }

    fn lemma1_holds(raw: i128, raw_lsb: i32, p: u32) {
        let (m, e) = round_to_precision_raw(raw, raw_lsb, p).unwrap();
        // Compare in units of `2^lo` where `lo = min(raw_lsb, lsb')`, so all
        // shifts are non-negative. The Lemma 1 bound in the same units is
        // `2^(e' - p - lo)`; when negative the bound is fractional, so only
        // an exact result passes.
        let lsb_new = e - p as i32 + 1;
        let lo = raw_lsb.min(lsb_new);
        let orig = raw
            .checked_shl((raw_lsb - lo) as u32)
            .expect("test shift overflow (orig)");
        let centre = m
            .checked_shl((lsb_new - lo) as u32)
            .expect("test shift overflow (centre)");
        let err = orig.wrapping_sub(centre).unsigned_abs();
        let exp = (e - p as i32) - lo;
        let ok = if exp >= 0 {
            err <= (1u128 << (exp as u32))
        } else {
            err == 0
        };
        assert!(ok, "Lemma1 violated: raw={raw} p={p} err={err} 2^{exp}");
    }

    #[test]
    fn round_nearest_small_cases_obey_lemma1() {
        // 15 = 0b1111, p=3: kept=0b111, rest=half, kept odd -> round up to
        // 0b1000 -> carry-out renormalize -> m=0b100, e=4.
        assert_eq!(round_to_precision_raw(15, 0, 3).unwrap(), (4, 4));
        for raw in [-33i128, -16, -15, -7, -1, 1, 7, 15, 16, 33, 100, 255] {
            for p in [1u32, 2, 3, 4, 5, 8] {
                lemma1_holds(raw, 0, p);
            }
        }
    }

    #[test]
    fn round_fuzz_lemma1_bound() {
        // xorshift64* deterministic PRNG (no rand dependency).
        let mut s: u64 = 0x9E3779B97F4A7C15;
        let mut next = move || {
            s ^= s >> 12;
            s ^= s << 25;
            s ^= s >> 27;
            s = s.wrapping_mul(0x2545F4914F6CDD1D);
            s
        };
        for _ in 0..2000 {
            let p = 1 + (next() % 16) as u32;
            let mut mag = next() as u128 | ((next() as u128) << 64);
            mag &= (1u128 << 40) - 1;
            if mag == 0 {
                mag = 1;
            }
            let mut raw = mag as i128;
            if next() & 1 == 1 {
                raw = -raw;
            }
            let raw_lsb = (next() % 11) as i32 - 5;
            let (m, e) = round_to_precision_raw(raw, raw_lsb, p).unwrap();
            if m != 0 {
                assert_eq!(bit_len(m.unsigned_abs()), p, "not normalized");
            }
            let lsb_new = e - p as i32 + 1;
            let lo = raw_lsb.min(lsb_new);
            let shift_o = (raw_lsb - lo) as u32;
            let shift_c = (lsb_new - lo) as u32;
            // Shifts stay small: raw_lsb in [-5,5], mantissae < 2^40.
            // Both sides are scaled into units of `2^lo`, so the Lemma 1
            // bound in the same units is `2^(e-p-lo)`.
            let orig = raw.checked_shl(shift_o).unwrap();
            let centre = m.checked_shl(shift_c).unwrap();
            let err = orig.wrapping_sub(centre).unsigned_abs();
            let exp = (e - p as i32) - lo;
            let ok = if exp >= 0 {
                exp < 128 && err <= (1u128 << (exp as u32))
            } else {
                err == 0
            };
            assert!(ok, "Lemma1 violated: raw={raw} p={p}");
        }
    }

    #[test]
    fn scaled_div_matches_truncation_plus_rounding() {
        // 100/50 = 2 exact at any guard.
        assert_eq!(scaled_div_nearest(100, 50, 4).unwrap(), 2 << 4);
        // 1/2 with guard 4 -> 8 exact.
        assert_eq!(scaled_div_nearest(1, 2, 4).unwrap(), 8);
        // 1/3 with guard 4 -> 16/3 = 5.33 -> 5.
        assert_eq!(scaled_div_nearest(1, 3, 4).unwrap(), 5);
        // 2/3 with guard 4 -> 32/3 = 10.67 -> 11.
        assert_eq!(scaled_div_nearest(2, 3, 4).unwrap(), 11);
        // Ties-to-even: 3/2 guard 0 -> 1.5 -> 2 (q=1 odd rounds up).
        assert_eq!(scaled_div_nearest(3, 2, 0).unwrap(), 2);
        // Ties-to-even: 5/2 guard 0 -> 2.5 -> 2 (q=2 even stays).
        assert_eq!(scaled_div_nearest(5, 2, 0).unwrap(), 2);
        assert!(scaled_div_nearest(1, 0, 4).is_none());
    }

    #[test]
    #[allow(clippy::unnecessary_min_or_max)] // values mirror the theory formulas
    fn exponent_helpers_match_theory() {
        // addA: ell + max(k1+d1, k2+d2).
        assert_eq!(add_a(-1, 1, 1, 2, 0), -1 + 2);
        // mulC/divD spot values cross-checked against MepkOpsTest.
        let c = mul_c(6, 5, 1, 8, 2, 7);
        let t = (1 - 8 + 1).max(2 - 7 + 1).max((1 + 2) - (8 + 7));
        assert_eq!(c, 6 + 5 + t + 2);
        assert_eq!(div_d(6, 5, 1, 8, 1, 8), (6 - 5) + (1 - 8).max(1 - 8) + 3);
        assert!(div_guard(1, 8));
        assert!(!div_guard(4, 4));
        assert_eq!(accuracy_tau(8, 7, 1), 0);
    }
}
