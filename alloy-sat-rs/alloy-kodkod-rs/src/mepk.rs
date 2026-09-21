//! Symbolic `(m, e, p, k)` error-tracking pseudo-real arithmetic
//! (`mepk_formal.md`) over [`IntCircuit`]s.
//!
//! # Two layers
//!
//! * **Concrete oracle** ([`Mepk`] + [`mepk_add`]/[`mepk_mul`]/[`mepk_div`]):
//!   exact centres via [`crate::int_ext`], the Rust counterpart of Java
//!   `MepkOps`. Used for testing and for computing centres outside the solver.
//! * **Symbolic layer** ([`MepkCircuit`] + `mepk_*_c`): pins the *error
//!   exponents* (`p'`, `k'`, `div_guard`) as solver-backed constraints
//!   over exponent circuits, like `util/mepk.als` (`mepkAdd/mepkMul/`
//!   `mepkDiv` pin `res.p`/`res.k`; the exact centre is delegated to the
//!   oracle). `e'` is pinned to `E0` (see below); the result mantissa
//!   `m'` is a fresh free variable, to be bound by the oracle / future
//!   full rounding encoding (see `round_mag_const_drop`).
//!
//! # Carry contract (`e'` is a lower estimate)
//!
//! The symbolic `e'` is derived from the bit length of the *unrounded*
//! exact total, so a round-up carry (at most one per rounding; a second
//! carry is impossible since a carried value is a power of two) can leave
//! it one below the true exponent: `e_oracle − e_sym ∈ {0, 1}` for every
//! op. Consequently `k'_sym − k_oracle ∈ {0, 1}` (conservative side).
//! Pair symbolic `(p', k')` with **oracle centres**; do not chain
//! symbolic `e'` into downstream error exponents without an oracle
//! rerounding in between.
//!
//! Bit widths come from the environment ([`MepkWidths::from_env`]):
//! `MEPK_M_WIDTH`, `MEPK_E_WIDTH`, `MEPK_P_WIDTH`, `MEPK_K_WIDTH`,
//! `MEPK_GUARD`. Unset entries fall back to the rule-based defaults
//! ([`MepkWidths::from_rule`]) derived from the `for n Int` atom count
//! (guard falls back to 4).

use crate::bool::BoolRef;
use crate::int::IntCircuit;
use crate::int_ext::{self, round_to_precision_raw, scaled_div_nearest};
use crate::BoolCtx;

// ---------------------------------------------------------------------------
// Width configuration
// ---------------------------------------------------------------------------

/// Circuit bit widths for the `(m, e, p, k)` components plus the division
/// guard-bit count. See module docs for the environment variables.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MepkWidths {
    /// Mantissa-centre width (signed).
    pub m_width: u32,
    /// MSB-exponent width (signed).
    pub e_width: u32,
    /// Precision width (signed).
    pub p_width: u32,
    /// Error-exponent width (signed).
    pub k_width: u32,
    /// Guard bits for scaled division (`q = (m1 << guard) / |m2|`).
    pub guard: u32,
}

impl MepkWidths {
    /// Uniform widths (all components share `bitwidth`), guard 4.
    /// Test helper; production defaults come from [`MepkWidths::from_rule`].
    pub fn uniform(bitwidth: u32) -> Self {
        MepkWidths {
            m_width: bitwidth,
            e_width: bitwidth,
            p_width: bitwidth,
            k_width: bitwidth,
            guard: 4,
        }
    }

    /// Rule-based default widths from the `for n Int` atom count `n`
    /// (agreed distribution rule):
    /// `E = min(n+1, 30)` (mirrors `effective_bitwidth`),
    /// `M = E` (the `m` lane spans exactly the circuit width, so every
    /// bit pattern reads exactly; usable precision is `p <= E-1`),
    /// `We = Wp = Wk = floor(log2(E+1)) + 2` (signed; covers `±E`).
    /// Guard defaults to 4.
    pub fn from_rule(int_count: u32) -> Self {
        let e_circ = (int_count + 1).clamp(1, 30);
        let m = e_circ;
        let w_exp = (e_circ + 1).ilog2() + 2;
        MepkWidths {
            m_width: m,
            e_width: w_exp,
            p_width: w_exp,
            k_width: w_exp,
            guard: 4,
        }
    }

    /// Override a single entry (for tests; avoids process-global env use).
    pub fn with_m_width(mut self, w: u32) -> Self {
        self.m_width = w;
        self
    }

    pub fn with_e_width(mut self, w: u32) -> Self {
        self.e_width = w;
        self
    }

    pub fn with_p_width(mut self, w: u32) -> Self {
        self.p_width = w;
        self
    }

    pub fn with_k_width(mut self, w: u32) -> Self {
        self.k_width = w;
        self
    }

    pub fn with_guard(mut self, g: u32) -> Self {
        self.guard = g;
        self
    }

    fn parse_env(name: &str, lo: u32, hi: u32) -> Result<Option<u32>, String> {
        match std::env::var(name) {
            Err(std::env::VarError::NotPresent) => Ok(None),
            Err(std::env::VarError::NotUnicode(_)) => {
                Err(format!("{name} is not valid unicode"))
            }
            Ok(s) => {
                let v: u32 = s
                    .trim()
                    .parse()
                    .map_err(|_| format!("{name}={s:?} is not a u32"))?;
                if !(lo..=hi).contains(&v) {
                    return Err(format!("{name}={v} out of range {lo}..={hi}"));
                }
                Ok(Some(v))
            }
        }
    }

    /// Read widths from the environment; unset entries fall back to the
    /// rule-based defaults ([`MepkWidths::from_rule`]) for `int_count`
    /// (guard falls back to 4). Explicit env values take precedence over
    /// the rule. Fails on malformed values.
    pub fn from_env(int_count: u32) -> Result<Self, String> {
        let mut w = Self::from_rule(int_count);
        if let Some(v) = Self::parse_env("MEPK_M_WIDTH", 1, 30)? {
            w.m_width = v;
        }
        if let Some(v) = Self::parse_env("MEPK_E_WIDTH", 1, 30)? {
            w.e_width = v;
        }
        if let Some(v) = Self::parse_env("MEPK_P_WIDTH", 1, 30)? {
            w.p_width = v;
        }
        if let Some(v) = Self::parse_env("MEPK_K_WIDTH", 1, 30)? {
            w.k_width = v;
        }
        if let Some(v) = Self::parse_env("MEPK_GUARD", 0, 64)? {
            w.guard = v;
        }
        Ok(w)
    }
}

// ---------------------------------------------------------------------------
// Concrete oracle
// ---------------------------------------------------------------------------

/// Concrete `(m, e, p, k)` value. Invariant: `p > 0`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Mepk {
    pub m: i128,
    pub e: i32,
    pub p: u32,
    pub k: i32,
}

impl Mepk {
    pub fn new(m: i128, e: i32, p: u32, k: i32) -> Option<Self> {
        if p == 0 || p > 127 {
            return None;
        }
        Some(Mepk { m, e, p, k })
    }

    /// Weight of the least significant bit: `lsb = e - p + 1`.
    pub fn lsb(&self) -> i32 {
        int_ext::lsb(self.e, self.p as i32)
    }

    /// Exponent of the error radius: `R = 2^(e - p + k)`.
    pub fn radius_exp(&self) -> i32 {
        int_ext::radius_exp(self.e, self.p as i32, self.k)
    }

    /// §5 division precondition.
    pub fn div_guard(&self) -> bool {
        int_ext::div_guard(self.k, self.p as i32)
    }

    /// CEGAR budget `tau = p - k - g` (§7).
    pub fn tau(&self, g: i32) -> i32 {
        int_ext::accuracy_tau(self.p as i32, self.k, g)
    }

    /// Exact decimal expansion of the centre `c = m · 2^lsb` using only
    /// integer arithmetic (never `f64`, so display rounding cannot weaken
    /// the guarantee). Shifts beyond ±120 fall back to `{m}*2^{lsb}`;
    /// fractional digits beyond that are capped accordingly.
    pub fn centre_exact(&self) -> String {
        decimal_of_scaled(self.m, self.lsb(), None)
    }

    /// Centre display with long fractions cut to 27 digits + `...`.
    pub fn centre_short(&self) -> String {
        decimal_of_scaled(self.m, self.lsb(), Some(27))
    }

    /// Radius display: exact decimal for `-4 <= n <= 20`
    /// (`n = e-p+k`), else the exact power `2^n` (avoids misleading
    /// digit walls like `0.0000...`).
    pub fn radius_str(&self) -> String {
        let n = self.e - self.p as i32 + self.k;
        if (-4..=20).contains(&n) {
            if n >= 0 {
                return (1i128 << (n as u32)).to_string();
            }
            // 2^-1 = 0.5, 2^-2 = 0.25, 2^-3 = 0.125, 2^-4 = 0.0625.
            let scaled = 10_000i128 >> ((-n) as u32);
            let s = format!("{:04}", scaled);
            let s = s.trim_end_matches('0');
            return format!("0.{s}");
        }
        format!("2^{n}")
    }

    /// One-line guarantee reading `c ± R (tau=t)` (short centre digits).
    pub fn interval_string(&self, g: i32) -> String {
        format!("{} ± {} (tau={})", self.centre_short(), self.radius_str(), self.tau(g))
    }

    /// One-line guarantee reading with full centre digits.
    pub fn interval_string_full(&self, g: i32) -> String {
        format!("{} ± {} (tau={})", self.centre_exact(), self.radius_str(), self.tau(g))
    }
}

/// Exact decimal expansion of `m · 2^lsb` (`frac_cap`: cut fractional
/// digits with `...`, `None` = full up to an internal 500-digit cap).
fn decimal_of_scaled(m: i128, lsb: i32, frac_cap: Option<usize>) -> String {
    if m == 0 {
        return "0".to_string();
    }
    let neg = m < 0;
    let mag = m.unsigned_abs();
    let sign = if neg { "-" } else { "" };
    if lsb >= 0 {
        match mag.checked_mul(1u128.checked_shl(lsb as u32).unwrap_or(u128::MAX)) {
            Some(v) => return format!("{sign}{v}"),
            None => return format!("{sign}{mag}*2^{lsb}"),
        }
    }
    // lsb < 0: terminating binary fraction. Exact u128 arithmetic
    // covers shifts up to 120 (rem × 10 stays below 2^124); tinier
    // values fall back to symbolic form.
    let shift = (-(lsb as i64)) as u32;
    if shift > 120 {
        return format!("{sign}{mag}*2^{lsb}");
    }
    let unit = 1u128 << shift;
    let int_part = mag >> shift;
    let mut rem = mag & (unit - 1);
    // Full expansion needs exactly `shift` fractional digits.
    let mut digits = Vec::with_capacity((shift as usize).min(64));
    for _ in 0..shift {
        if rem == 0 {
            break;
        }
        rem = match rem.checked_mul(10) {
            Some(v) => v,
            // Defensive: unreachable for shift <= 120 (rem < 2^shift).
            None => break,
        };
        digits.push((rem >> shift) as u8);
        rem &= unit - 1;
    }
    let rest_nonzero = rem != 0;
    let mut frac: String = digits.iter().map(|d| (b'0' + d) as char).collect();
    if let Some(cap) = frac_cap {
        if frac.len() > cap {
            frac.truncate(cap);
            return format!("{sign}{int_part}.{frac}...");
        }
    }
    if rest_nonzero {
        frac.push_str("...");
    }
    if frac.is_empty() {
        format!("{sign}{int_part}")
    } else {
        format!("{sign}{int_part}.{frac}")
    }
}

/// Addition / subtraction (§3). `sign` is +1 (add) or -1 (sub).
/// `None` on overflow or bad precision.
pub fn mepk_add(x1: &Mepk, x2: &Mepk, sign: i8) -> Option<Mepk> {
    if sign != 1 && sign != -1 {
        return None;
    }
    let ell = x1.lsb().min(x2.lsb());
    let d1 = (x1.lsb() - ell) as u32;
    let d2 = (x2.lsb() - ell) as u32;
    let t1 = x1.m.checked_shl(d1)?;
    let t2 = x2.m.checked_shl(d2)?;
    let total = if sign == 1 {
        t1.checked_add(t2)?
    } else {
        t1.checked_sub(t2)?
    };
    let p_new = x1.p.min(x2.p);
    let (m_new, e_new) = round_to_precision_raw(total, ell, p_new)?;
    let a = int_ext::add_a(ell, x1.k, d1 as i32, x2.k, d2 as i32);
    let b = e_new - p_new as i32;
    Mepk::new(m_new, e_new, p_new, int_ext::combine_k(a, b))
}

/// Multiplication (§4). `None` on overflow or bad precision.
pub fn mepk_mul(x1: &Mepk, x2: &Mepk) -> Option<Mepk> {
    let p_new = x1.p.min(x2.p);
    let prod = x1.m.checked_mul(x2.m)?;
    let raw_lsb = x1.lsb().checked_add(x2.lsb())?;
    let (m_new, e_new) = round_to_precision_raw(prod, raw_lsb, p_new)?;
    let c = int_ext::mul_c(
        x1.e,
        x2.e,
        x1.k,
        x1.p as i32,
        x2.k,
        x2.p as i32,
    );
    let b = e_new - p_new as i32;
    Mepk::new(m_new, e_new, p_new, int_ext::combine_k(c, b))
}

/// Division (§5). `None` when `k2 >= p2` (denominator may span zero),
/// on overflow, or on bad precision. `guard` is the caller's
/// `MepkWidths::guard` (default 4).
pub fn mepk_div(x1: &Mepk, x2: &Mepk, guard: u32) -> Option<Mepk> {
    if !x2.div_guard() {
        return None;
    }
    let p_new = x1.p.min(x2.p);
    let neg = (x1.m < 0) != (x2.m < 0);
    let qmag = scaled_div_nearest(x1.m.unsigned_abs(), x2.m.unsigned_abs(), guard)?;
    if qmag > i128::MAX as u128 {
        return None;
    }
    let q = if neg { -(qmag as i128) } else { qmag as i128 };
    let q_lsb = x1
        .lsb()
        .checked_sub(x2.lsb())?
        .checked_sub(guard as i32)?;
    let (m_new, e_new) = round_to_precision_raw(q, q_lsb, p_new)?;
    let d = int_ext::div_d(
        x1.e,
        x2.e,
        x1.k,
        x1.p as i32,
        x2.k,
        x2.p as i32,
    );
    let b = e_new - p_new as i32;
    Mepk::new(m_new, e_new, p_new, int_ext::combine_k(d, b))
}

// ---------------------------------------------------------------------------
// Decimal literal conversion
// ---------------------------------------------------------------------------

/// Result of [`decimal_to_mepk`]: the converted value, whether the
/// encoding is exact, and — for exact values — the minimal
/// exactly-encoding precision (`None` when no finite precision suffices).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DecimalConv {
    pub v: Mepk,
    pub exact: bool,
    pub min_p: Option<u32>,
}

/// Parsed decimal literal: `value = ±digits × 10^exp10` with `digits ≥ 0`.
fn parse_decimal(s: &str) -> Option<(bool, u128, i32)> {
    let t = s.trim();
    let t = t.strip_prefix('+').unwrap_or(t);
    let neg = t.starts_with('-');
    let t = t.strip_prefix('-').unwrap_or(t);
    let (mant, exp_str) = match t.find(['e', 'E']) {
        Some(i) => (&t[..i], Some(&t[i + 1..])),
        None => (t, None),
    };
    let exp10: i32 = match exp_str {
        None => 0,
        Some(e) => e.parse().ok()?,
    };
    let (int_part, frac_part) = match mant.find('.') {
        Some(i) => (&mant[..i], &mant[i + 1..]),
        None => (mant, ""),
    };
    if int_part.is_empty() && frac_part.is_empty() {
        return None;
    }
    if !int_part.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    if !frac_part.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    let mut d: u128 = 0;
    for ch in int_part.bytes().chain(frac_part.bytes()) {
        d = d.checked_mul(10)?.checked_add((ch - b'0') as u128)?;
    }
    let e = exp10.checked_sub(frac_part.len() as i32)?;
    Some((neg, d, e))
}

fn gcd_u128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

fn pow10_u128(k: u32) -> Option<u128> {
    if k > 40 {
        return None;
    }
    let mut v: u128 = 1;
    for _ in 0..k {
        v = v.checked_mul(10)?;
    }
    Some(v)
}

fn to_i128(v: u128) -> Option<i128> {
    if v > i128::MAX as u128 {
        return None;
    }
    Some(v as i128)
}

/// `floor(log2(digits / 10^k))` for `digits > 0` via binary search with
/// overflow-proof comparisons (overflow on either side decides the order).
fn floor_log2_div(digits: u128, k: u32) -> Option<i32> {
    debug_assert!(digits > 0);
    let den = pow10_u128(k)?;
    // 2^e <= digits / den?
    let le = |e: i32| -> bool {
        if e >= 0 {
            match 2u128.checked_pow(e as u32).and_then(|p| p.checked_mul(den)) {
                // Overflow: 2^e * den > u128::MAX >= digits.
                Some(v) => v <= digits,
                None => false,
            }
        } else {
            match digits.checked_shl((-e) as u32) {
                // Overflow: digits * 2^-e > u128::MAX >= den.
                Some(v) => v >= den,
                None => true,
            }
        }
    };
    // Invariants: le(-200) holds (den <= 10^38 < 2^200 <= digits*2^200),
    // le(200) fails (2^200 * den > u128::MAX >= digits).
    let (mut lo, mut hi) = (-200i32, 200i32);
    debug_assert!(le(lo) && !le(hi));
    while hi - lo > 1 {
        let mid = lo + (hi - lo) / 2;
        if le(mid) {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    Some(lo)
}

/// Convert a decimal real literal (e.g. `"3.14"`, `"-0.1"`, `"2.5"`,
/// `"1e-3"`) to `(m, e, p, k)` at precision `max_p`:
///
/// - dyadic values (reduced denominator a power of two, including plain
///   integers) encode **exactly**: zero-fill (or exact-drop of trailing
///   zeros) pads them up to `max_p` with `k = 0`. `min_p` reports the
///   minimal exactly-encoding precision (`bit length − trailing zeros`);
/// - other values round to nearest at `max_p` with `k = 1` (one guard bit
///   absorbs the decimal→binary pre-rounding; the pre-scale carries two
///   extra bits of margin). `min_p` is `None` (no finite precision
///   suffices).
/// - dyadic values with `min_p > max_p` round at the cap with `k = 0`
///   (still sound: a single rounding of an exact integer is within the
///   Lemma-1 bound); `min_p` reports the unmet need.
///
/// Padding exact values is always sound (`e` unchanged, error stays 0)
/// and keeps mixed-precision operands aligned instead of collapsing to
/// the coarsest minimal precision.
///
/// Returns `None` on malformed input, `max_p` outside `1..=127`, or values
/// outside the `i128` oracle range (documented limit: magnitudes roughly
/// within ±2^127, denominators up to 10^38).
pub fn decimal_to_mepk(s: &str, max_p: u32) -> Option<DecimalConv> {
    if max_p == 0 || max_p > 127 {
        return None;
    }
    let (neg, digits, exp10) = parse_decimal(s)?;
    if digits == 0 {
        let (m, e) = round_to_precision_raw(0, 0, max_p)?;
        return Some(DecimalConv {
            v: Mepk::new(m, e, max_p, 0)?,
            exact: true,
            min_p: Some(1),
        });
    }
    let apply_sign = |v: i128| -> Option<i128> {
        if neg {
            v.checked_neg()
        } else {
            Some(v)
        }
    };
    if exp10 >= 0 {
        // Exact scaled integer: D × 10^E at lsb 0, rounded (or padded)
        // to max_p with k = 0.
        let den = pow10_u128(exp10 as u32)?;
        let raw_u = digits.checked_mul(den)?;
        let raw = apply_sign(to_i128(raw_u)?)?;
        // Minimal exactly-encoding precision: trailing zeros need no bits.
        let bl = int_ext::bit_len(raw_u);
        let p_star = (bl - raw_u.trailing_zeros()).max(1);
        let (m, e) = round_to_precision_raw(raw, 0, max_p)?;
        let v = Mepk::new(m, e, max_p, 0)?;
        return Some(DecimalConv {
            v,
            exact: p_star <= max_p,
            min_p: Some(p_star),
        });
    }
    // exp10 < 0: value = D / 10^k, reduced to num/den.
    let k = exp10.checked_neg()? as u32;
    let den = pow10_u128(k)?;
    let g = gcd_u128(digits, den);
    let num_r = digits / g;
    let mut den_r = den / g;
    // Strip powers of two: den_r = 2^a * o.
    let mut a = 0u32;
    while den_r.is_multiple_of(2) {
        den_r /= 2;
        a += 1;
    }
    if den_r == 1 {
        // Dyadic: value = ±num_r × 2^-a, exact single rounding at max_p.
        let raw = apply_sign(to_i128(num_r)?)?;
        let lsb = -(a as i32);
        let bl = int_ext::bit_len(num_r);
        let p_star = (bl - num_r.trailing_zeros()).max(1);
        let (m, e) = round_to_precision_raw(raw, lsb, max_p)?;
        let v = Mepk::new(m, e, max_p, 0)?;
        return Some(DecimalConv {
            v,
            exact: p_star <= max_p,
            min_p: Some(p_star),
        });
    }
    // Non-dyadic: pre-round value × 2^s to an integer with two margin
    // bits (s = max_p − e + 2), reusing the ties-to-even scaled
    // division; the combined error stays below 2^(e−p+1), hence k = 1.
    // Factoring out 2^a keeps intermediates small: q ≈ value × 2^s.
    let o = den_r;
    let e_est = floor_log2_div(digits, k)?;
    let s = (max_p as i32 - e_est + 2).max(0) as u32;
    let (q, q_lsb) = if s >= a {
        (scaled_div_nearest(num_r, o, s - a)?, -(s as i32))
    } else {
        let den2 = o.checked_mul(2u128.checked_pow(a - s)?)?;
        (scaled_div_nearest(num_r, den2, 0)?, -(s as i32))
    };
    let signed = apply_sign(to_i128(q)?)?;
    let (m, e) = round_to_precision_raw(signed, q_lsb, max_p)?;
    let v = Mepk::new(m, e, max_p, 1)?;
    Some(DecimalConv {
        v,
        exact: false,
        min_p: None,
    })
}

// ---------------------------------------------------------------------------
// Symbolic layer
// ---------------------------------------------------------------------------

/// Symbolic `(m, e, p, k)` value: four [`IntCircuit`]s sharing one [`BoolCtx`].
#[derive(Clone, Debug)]
pub struct MepkCircuit {
    pub m: IntCircuit,
    pub e: IntCircuit,
    pub p: IntCircuit,
    pub k: IntCircuit,
}

impl MepkCircuit {
    /// Constant tuple (each lane encoded at its configured width).
    pub fn constant(m: i64, e: i64, p: i64, k: i64, w: &MepkWidths, ctx: &BoolCtx) -> Self {
        MepkCircuit {
            m: IntCircuit::constant(m, w.m_width, ctx),
            e: IntCircuit::constant(e, w.e_width, ctx),
            p: IntCircuit::constant(p, w.p_width, ctx),
            k: IntCircuit::constant(k, w.k_width, ctx),
        }
    }

    /// Fresh free-variable tuple (result centres / unknowns).
    pub fn free(w: &MepkWidths, ctx: &BoolCtx) -> Self {
        let fresh = |width: u32| {
            IntCircuit::from_bits((0..width).map(|_| ctx.variable()).collect(), ctx)
        };
        MepkCircuit {
            m: fresh(w.m_width),
            e: fresh(w.e_width),
            p: fresh(w.p_width),
            k: fresh(w.k_width),
        }
    }

    pub fn ctx(&self) -> &BoolCtx {
        self.m.ctx()
    }

    /// `lsb = e - p + 1` circuit (width `e_width`, wrapping).
    pub fn lsb_c(&self, w: &MepkWidths) -> IntCircuit {
        let one = IntCircuit::constant(1, w.e_width, self.ctx());
        self.e.sub(&self.p, w.e_width).add(&one, w.e_width)
    }
}

/// `combine_k(A, B) = max(A - B, 0) + 1` as a circuit.
/// Operands are read sign-extended; result carries `max(a.width, b.width)+2` bits.
fn combine_k_c(a: &IntCircuit, b: &IntCircuit) -> IntCircuit {
    let ctx = a.ctx().clone();
    let d = a.widen_sub(b);
    let neg = d.bit(d.width() - 1);
    let zero = IntCircuit::constant(0, d.width() as u32, &ctx);
    // `neg ? 0 : d`, then `+ 1`.
    let nonneg = zero.choice(neg, &d);
    let one = IntCircuit::constant(1, d.width() as u32, &ctx);
    nonneg.add(&one, d.width() as u32)
}

/// Truncate-or-sign-extend circuit `v` to exactly `width` bits (two's complement).
fn resize(v: &IntCircuit, width: u32) -> IntCircuit {
    let ctx = v.ctx().clone();
    let bits: Vec<BoolRef> = (0..width as usize).map(|i| v.bit(i)).collect();
    let mut ret = IntCircuit::from_bits(bits, &ctx);
    ret = ret.with_taint(v.is_tainted());
    ret
}

/// Lower estimate `E0` of the result exponent from the exact integer
/// total `t` at scale `raw_lsb`: `E0 = raw_lsb + bitlen(|t|) - 1`, with
/// the zero case mapping to `raw_lsb + p' - 1` (mirrors the concrete
/// zero rule). A round-up carry can bump the true exponent by one
/// (see the module-level carry contract); `E0` never overshoots.
fn result_exp_c(
    t: &IntCircuit,
    raw_lsb: &IntCircuit,
    p_new: &IntCircuit,
    w: &MepkWidths,
) -> IntCircuit {
    let ctx = t.ctx().clone();
    let bl = t.bit_len_c();
    let is_zero = bl.eq(&IntCircuit::constant(0, bl.width() as u32, &ctx));
    let one = IntCircuit::constant(1, w.e_width, &ctx);
    // Nonzero: `raw_lsb + bl - 1`; zero: `raw_lsb + p' - 1`.
    let e_nz = raw_lsb.add(&bl, w.e_width).sub(&one, w.e_width);
    let e_z = raw_lsb.add(p_new, w.e_width).sub(&one, w.e_width);
    e_z.choice(is_zero, &e_nz)
}

/// Shared tail of add/sub/mul/div: given the exact-total circuit `t`,
/// its scale `raw_lsb`, `p'`, and the Lemma-2 error exponent `err_exp`
/// (`A`/`C`/`D`), pin `e'`, `B = e' - p'`, `k' = combine_k(err_exp, B)`.
/// Returns `(e_full, k_full)`; the caller resizes to configured widths.
fn finish_c(
    t: &IntCircuit,
    raw_lsb: &IntCircuit,
    p_new: &IntCircuit,
    err_exp: &IntCircuit,
    w: &MepkWidths,
) -> (IntCircuit, IntCircuit) {
    let ctx = t.ctx().clone();
    let ew = w.e_width;
    let e_new = result_exp_c(t, raw_lsb, p_new, w);
    let b = e_new.sub(p_new, ew);
    let k_unsized = combine_k_c(err_exp, &b);
    let _ = &ctx;
    (e_new, k_unsized)
}

/// Addition / subtraction (§3, symbolic exponent layer).
/// `sign` is +1 (add) or -1 (sub). The result `m` is a fresh free
/// variable (centre delegated to the oracle); `p'` is exact, `e'` is
/// the `E0` lower estimate, and `k'` is conservative (see the
/// module-level carry contract).
///
/// Alignment shifts use the variable barrel shifter over a doubled `m`
/// width: exact whenever both `d1, d2 < m_width` (bounded-shift
/// precondition; `lsb` gaps beyond that are out of scope, like bitwidth
/// wrapping for plain `Int`).
pub fn mepk_add_c(x1: &MepkCircuit, x2: &MepkCircuit, sign: i8, w: &MepkWidths) -> MepkCircuit {
    assert!(sign == 1 || sign == -1);
    let ctx = x1.ctx().clone();
    let ew = w.e_width;
    let lsb1 = x1.lsb_c(w);
    let lsb2 = x2.lsb_c(w);
    let ell = lsb1.min_c(&lsb2);
    let d1 = lsb1.sub(&ell, ew);
    let d2 = lsb2.sub(&ell, ew);
    // Widen mantissae, align, exact-add.
    let mw2 = w.m_width * 2;
    let a_promoted: IntCircuit = {
        let bits: Vec<BoolRef> = (0..mw2 as usize).map(|i| x1.m.bit(i)).collect();
        IntCircuit::from_bits(bits, &ctx)
    };
    let b_promoted: IntCircuit = {
        let bits: Vec<BoolRef> = (0..mw2 as usize).map(|i| x2.m.bit(i)).collect();
        IntCircuit::from_bits(bits, &ctx)
    };
    let a_aligned = a_promoted.shl(&d1, mw2);
    let b_aligned = b_promoted.shl(&d2, mw2);
    let t = if sign == 1 {
        a_aligned.widen_add(&b_aligned)
    } else {
        a_aligned.widen_sub(&b_aligned)
    };
    let p_new = x1.p.min_c(&x2.p);
    // `A = ell + max(k1 + d1, k2 + d2)`.
    let t1 = x1.k.add(&d1, w.k_width);
    let t2 = x2.k.add(&d2, w.k_width);
    let a_exp = ell.add(&t1.max_c(&t2), ew);
    let (e_new, k_new) = finish_c(&t, &ell, &p_new, &a_exp, w);
    let mut res = MepkCircuit::free(w, &ctx);
    res.p = resize(&p_new, w.p_width);
    res.e = resize(&e_new, w.e_width);
    res.k = resize(&k_new, w.k_width);
    res
}

/// Multiplication (§4, symbolic exponent layer). Centre conventions as in
/// [`mepk_add_c`] (`e'` is the `E0` lower estimate, `k'` conservative).
pub fn mepk_mul_c(x1: &MepkCircuit, x2: &MepkCircuit, w: &MepkWidths) -> MepkCircuit {
    let ctx = x1.ctx().clone();
    let ew = w.e_width;
    let prod = x1.m.widen_mul(&x2.m);
    let raw_lsb = x1.lsb_c(w).add(&x2.lsb_c(w), ew);
    let p_new = x1.p.min_c(&x2.p);
    // `C = e1 + e2 + max(k1-p1+1, k2-p2+1, k1+k2-p1-p2) + 2`.
    let one = IntCircuit::constant(1, ew, &ctx);
    let two = IntCircuit::constant(2, ew, &ctx);
    let u1 = x1.k.sub(&x1.p, ew).add(&one, ew);
    let u2 = x2.k.sub(&x2.p, ew).add(&one, ew);
    let u3 = x1.k.add(&x2.k, ew).sub(&x1.p.add(&x2.p, ew), ew);
    let mx = u1.max_c(&u2).max_c(&u3);
    let c_exp = x1.e.add(&x2.e, ew).add(&mx, ew).add(&two, ew);
    let (e_new, k_new) = finish_c(&prod, &raw_lsb, &p_new, &c_exp, w);
    let mut res = MepkCircuit::free(w, &ctx);
    res.p = resize(&p_new, w.p_width);
    res.e = resize(&e_new, w.e_width);
    res.k = resize(&k_new, w.k_width);
    res
}

/// Division (§5, symbolic exponent layer). Returns `(result, undef)` where
/// `undef = (k2 >= p2)` is the §5 precondition-violation flag: a model with
/// `undef` true must be treated as UNSAT (no finite bound can absorb a
/// denominator interval spanning zero), mirroring `divGuard` in `mepk.als`
/// and division-by-zero handling in [`IntCircuit::div`].
/// `e'`/`k'` follow the carry contract (lower estimate / conservative).
pub fn mepk_div_c(
    x1: &MepkCircuit,
    x2: &MepkCircuit,
    w: &MepkWidths,
) -> (MepkCircuit, BoolRef) {
    let ctx = x1.ctx().clone();
    let ew = w.e_width;
    // `undef = (k2 >= p2) = NOT (k2 < p2)`.
    let undef = ctx.not(x2.k.lt(&x2.p));
    // Quotient scale needs no division circuit: `q_lsb = lsb1 - lsb2 - guard`.
    let guard_c = IntCircuit::constant(w.guard as i64, ew, &ctx);
    let q_lsb = x1.lsb_c(w).sub(&x2.lsb_c(w), ew).sub(&guard_c, ew);
    // `e'` needs `bitlen(|q|)`: obtain the wide truncated quotient magnitude
    // via the exact division circuit on magnitudes.
    let (_q_wide, _round_up, _neg, _dbz) = x1.m.div_nearest_wide(&x2.m, w.guard);
    // `e'` from the wide quotient's bit-length (zero case handled inside).
    let p_new = x1.p.min_c(&x2.p);
    let e_new = result_exp_c(&_q_wide, &q_lsb, &p_new, w);
    // `D = e1 - e2 + max(k1-p1, k2-p2) + 3`.
    let three = IntCircuit::constant(3, ew, &ctx);
    let v1 = x1.k.sub(&x1.p, ew);
    let v2 = x2.k.sub(&x2.p, ew);
    let d_exp = x1
        .e
        .sub(&x2.e, ew)
        .add(&v1.max_c(&v2), ew)
        .add(&three, ew);
    let b = e_new.sub(&p_new, ew);
    let k_new = combine_k_c(&d_exp, &b);
    let mut res = MepkCircuit::free(w, &ctx);
    res.p = resize(&p_new, w.p_width);
    res.e = resize(&e_new, w.e_width);
    res.k = resize(&k_new, w.k_width);
    (res, undef)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn widths_env_parsing() {
        let w = MepkWidths::uniform(4);
        assert_eq!(w.guard, 4);
        assert_eq!(w.m_width, 4);
    }

    #[test]
    fn widths_rule_distribution() {
        // (int_count, E, M, w_exp) per the agreed rule (M = E: lanes
        // span exactly the circuit width, so every pattern reads exactly).
        for (n, e, m, wx) in [(4u32, 5u32, 5u32, 4u32), (8, 9, 9, 5), (10, 11, 11, 5), (30, 30, 30, 6)] {
            let w = MepkWidths::from_rule(n);
            assert_eq!((w.m_width, w.e_width, w.p_width, w.k_width, w.guard), (m, wx, wx, wx, 4),
                "n={n}");
            // Exponent lanes cover ±E and precision p <= E.
            let max = (1i64 << (wx - 1)) - 1;
            assert!(max >= e as i64, "lane too narrow for E={e}");
            let _ = m;
        }
    }

    #[test]
    fn concrete_add_matches_java_oracle() {
        // MepkOpsTest.addSubKRule: x1=(100,6,8,1), x2=(50,5,8,2).
        let x1 = Mepk::new(100, 6, 8, 1).unwrap();
        let x2 = Mepk::new(50, 5, 8, 2).unwrap();
        let s = mepk_add(&x1, &x2, 1).unwrap();
        // lsb1 = -1, lsb2 = -2, ell = -2, d1 = 1, d2 = 0.
        // total = 200 + 50 = 250, p' = 8.
        assert_eq!(s.p, 8);
        // A = ell + max(k1+d1, k2+d2) = -2 + max(2, 2).
        let a = -2 + 2;
        let b = s.e - 8;
        assert_eq!(s.k, int_ext::combine_k(a, b));
        // Centre within rounding error of the exact sum (both in 2^ell
        // units; the Lemma 1 bound in the same units is 2^(e'-p'-ell)).
        let ell = -2;
        let exact = 100i128 * 2 + 50;
        let got = s.m << ((s.e - 8 + 1) - ell);
        let err = (exact - got).abs();
        let exp = (s.e - 8) - ell;
        assert!(exp < 0 && err == 0 || exp >= 0 && err <= 1i128 << (exp as u32));
    }

    #[test]
    fn concrete_div_rejects_bad_denominator() {
        let num = Mepk::new(100, 6, 8, 1).unwrap();
        let bad = Mepk::new(50, 5, 4, 4).unwrap();
        assert!(mepk_div(&num, &bad, 4).is_none());
        let ok = Mepk::new(50, 5, 8, 1).unwrap();
        let r = mepk_div(&num, &ok, 4).unwrap();
        // D = (e1-e2) + max(k1-p1, k2-p2) + 3 = 1 + (-7) + 3.
        let d = (6 - 5) + (1 - 8) + 3;
        assert_eq!(r.k, int_ext::combine_k(d, r.e - r.p as i32));
    }

    /// Check `|decimal − centre| ≤ R` rationally in units of `2^lo`
    /// (mirrors the Lemma-1 test pattern; inputs are small).
    fn assert_decimal_sound(s: &str, max_p: u32) {
        let conv = decimal_to_mepk(s, max_p).unwrap();
        let x = conv.v;
        let (neg, digits, exp10) = parse_decimal(s).unwrap();
        // value = ±digits × 10^exp10 = num/den with split exponents.
        // Conversion already succeeded, so negating exp10 is safe here.
        let (num10, den10) = if exp10 >= 0 {
            (pow10_u128(exp10 as u32).unwrap() as i128, 1i128)
        } else {
            (
                1i128,
                pow10_u128(exp10.checked_neg().unwrap() as u32).unwrap() as i128,
            )
        };
        let num = (if neg { -(digits as i128) } else { digits as i128 })
            .checked_mul(num10)
            .unwrap();
        let den = den10;
        let lsb = x.e - x.p as i32 + 1;
        // Compare num/den vs m·2^lsb in units of 2^min(0,lsb)/den:
        // |num·2^a − m·den·2^b| ≤ R·(2^−lo·den), computed in i128.
        let lo = lsb.min(0);
        let a = (0 - lo) as u32;
        let b = (lsb - lo) as u32;
        let lhs = (num.checked_mul(1i128.checked_shl(a).unwrap()).unwrap()
            - x.m.checked_mul(den).unwrap().checked_mul(1i128.checked_shl(b).unwrap()).unwrap())
        .abs();
        // R = 2^(e−p+k) in the same units: 2^(e−p+k−lo)·den. With a
        // negative exponent, scale the error up instead (exact integer
        // arithmetic either way; test values are small).
        let rexp = (x.e - x.p as i32 + x.k) - lo;
        if rexp >= 0 {
            let rhs = den
                .checked_mul(1i128.checked_shl(rexp as u32).unwrap())
                .unwrap();
            assert!(lhs <= rhs, "unsound conversion of {s}: err {lhs} > {rhs}");
        } else {
            let lhs2 = lhs.checked_shl((-rexp) as u32).unwrap();
            assert!(lhs2 <= den, "unsound conversion of {s}: err {lhs} > R");
        }
    }

    #[test]
    fn decimal_exact_dyadic() {
        // Exact values pad up to max_p (zero-fill keeps them exact).
        // 0.5 = 1/2 → (128, -1, 8, 0), minimal p = 1.
        let c = decimal_to_mepk("0.5", 8).unwrap();
        assert_eq!((c.v.m, c.v.e, c.v.p, c.v.k), (128, -1, 8, 0));
        assert!(c.exact);
        assert_eq!(c.min_p, Some(1));
        // 2.5 = 5/2 → (160, 1, 8, 0), minimal p = 3.
        let c = decimal_to_mepk("2.5", 8).unwrap();
        assert_eq!((c.v.m, c.v.e, c.v.p, c.v.k), (160, 1, 8, 0));
        assert!(c.exact);
        assert_eq!(c.min_p, Some(3));
        // 0.25 = 1/4.
        let c = decimal_to_mepk("0.25", 8).unwrap();
        assert_eq!((c.v.m, c.v.e, c.v.p, c.v.k), (128, -2, 8, 0));
        assert!(c.exact);
        // 12 = 0b1100: trailing zeros need no bits (minimal p = 2),
        // padded to 8 → m = 12 << 6.
        let c = decimal_to_mepk("12", 8).unwrap();
        assert_eq!((c.v.m, c.v.e, c.v.p, c.v.k), (192, 3, 8, 0));
        assert!(c.exact);
        assert_eq!(c.min_p, Some(2));
        // Integers and signs.
        let c = decimal_to_mepk("3", 8).unwrap();
        assert_eq!((c.v.m, c.v.e, c.v.p, c.v.k), (192, 1, 8, 0));
        let c = decimal_to_mepk("-0.5", 8).unwrap();
        assert_eq!((c.v.m, c.v.e, c.v.p, c.v.k), (-128, -1, 8, 0));
        assert!(c.exact);
        // Zeros pad like everything else.
        for z in ["0", "0.00", "-0.0", "+0"] {
            let c = decimal_to_mepk(z, 8).unwrap();
            assert_eq!((c.v.m, c.v.e, c.v.p, c.v.k), (0, 7, 8, 0), "{z}");
            assert!(c.exact);
            assert_eq!(c.min_p, Some(1));
        }
        // Explicit small cap still rounds (here exactly, by luck of zeros).
        let c = decimal_to_mepk("12", 2).unwrap();
        assert_eq!((c.v.m, c.v.e, c.v.p, c.v.k), (3, 3, 2, 0));
        assert!(c.exact);
    }

    #[test]
    fn decimal_exp_forms() {
        let c = decimal_to_mepk("1e2", 8).unwrap();
        assert_eq!((c.v.m, c.v.e, c.v.p, c.v.k), (200, 6, 8, 0));
        assert!(c.exact);
        assert_eq!(c.min_p, Some(5));
        let c = decimal_to_mepk("2E3", 8).unwrap();
        assert!(c.exact);
        assert_eq!(c.v.m << (c.v.e - c.v.p as i32 + 1), 2000);
        // 1.5e-1 = 0.15 = 3/20: non-dyadic → rounded, k = 1.
        let c = decimal_to_mepk("1.5e-1", 8).unwrap();
        assert!(!c.exact);
        assert_eq!((c.v.p, c.v.k), (8, 1));
    }

    #[test]
    fn decimal_rounded_nondyadic() {
        // 0.1 at max_p = 5: hand-checked (26, −4, 5, 1).
        let c = decimal_to_mepk("0.1", 5).unwrap();
        assert_eq!((c.v.m, c.v.e, c.v.p, c.v.k), (26, -4, 5, 1));
        assert!(!c.exact);
        // Soundness over a grid of non-dyadic decimals and precisions.
        for s in ["0.1", "0.2", "0.3", "3.14", "2.718", "0.07", "123.456", "-0.1", "10.01"] {
            for p in [1u32, 2, 3, 5, 8, 12] {
                assert_decimal_sound(s, p);
            }
        }
        // Dyadic grid is exactly sound too.
        for s in ["0.5", "2.5", "0.25", "3", "12", "1e2", "0.75", "6.25"] {
            for p in [1u32, 2, 4, 8] {
                assert_decimal_sound(s, p);
            }
        }
    }

    #[test]
    fn decimal_dyadic_over_cap() {
        // 1023 needs p = 10; capped at 4 → rounded but still k = 0
        // (single rounding of an exact integer).
        let c = decimal_to_mepk("1023", 4).unwrap();
        assert_eq!((c.v.p, c.v.k), (4, 0));
        assert!(!c.exact);
        assert_eq!(c.min_p, Some(10));
        assert_decimal_sound("1023", 4);
    }

    #[test]
    fn decimal_rejects() {
        for bad in ["", " ", "abc", "1.2.3", "--1", "1e", "e5", ".", "NaN", "inf", "1,5"] {
            assert!(decimal_to_mepk(bad, 8).is_none(), "{bad:?}");
        }
        assert!(decimal_to_mepk("0.5", 0).is_none());
        assert!(decimal_to_mepk("0.5", 128).is_none());
        // Out of the i128 oracle range.
        assert!(decimal_to_mepk("1e100", 8).is_none());
        assert!(decimal_to_mepk("12345678901234567890123456789012345678901234567890", 8).is_none());
    }

    #[test]
    fn interval_display() {
        // (m=7, e=2, p=3, k=1): lsb 0, centre 7, R = 2^0.
        let x = Mepk::new(7, 2, 3, 1).unwrap();
        assert_eq!(x.interval_string(0), "7 ± 1 (tau=2)");
        assert_eq!(x.interval_string_full(0), "7 ± 1 (tau=2)");
        // 0.1015625 ± 2^-8 (small radius stays symbolic).
        let x = Mepk::new(26, -4, 5, 1).unwrap();
        assert_eq!(x.interval_string(0), "0.1015625 ± 2^-8 (tau=4)");
        // Negative centre, threshold radius (R = 2^-2).
        let x = Mepk::new(-1, -1, 1, 0).unwrap();
        assert_eq!(x.interval_string(0), "-0.5 ± 0.25 (tau=1)");
        // Zero.
        let x = Mepk::new(0, 0, 1, 0).unwrap();
        assert_eq!(x.interval_string(0), "0 ± 0.5 (tau=1)");
        // Huge radius stays a power of two.
        let x = Mepk::new(1, 100, 8, 2).unwrap();
        assert_eq!(x.radius_str(), "2^94");
        assert!(x.interval_string(0).contains("± 2^94"));
        // Long fractions truncate with `...` in short mode only
        // (2^-37 needs 37 fractional digits).
        let x = Mepk::new(1, -30, 8, 0).unwrap();
        assert_eq!(x.centre_exact(), "0.0000000000072759576141834259033203125");
        assert_eq!(x.centre_short(), "0.000000000007275957614183425...");
        assert_eq!(x.radius_str(), "2^-38");
        // Symbolic fallback for extreme shifts.
        let x = Mepk::new(3, -1000, 8, 0).unwrap();
        assert_eq!(x.centre_short(), "3*2^-1007");
    }
}
