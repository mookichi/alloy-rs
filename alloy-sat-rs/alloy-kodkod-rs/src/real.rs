//! Exact-centre `Real` runtime (`c = m * 2^e`, shared with `EReal`).
//!
//! `mepk` (`m * 2^(e-p+1)`) とは異なり `p/k` を持たない。`Real` の
//! `(m, e)` レーンは `EReal` と共通 (継承で共有)。正規形は
//! `m == 0` (e 自由) または `odd(m)`。演算は exact のみ:
//! 割り切れない除算・非 dyadic リテラルは `None` (solver では UNSAT)。
//! `decimal_to_real_rounded` の丸めは例外: 非 dyadic 値を `m` 幅
//! いっぱいに丸めるが、丸め誤差自体は追跡されない (bracketing 用途は
//! Down/Up の2値で挟むこと)。

use crate::int_ext::round_half_even_step;

/// Exact-centre実数 `c = m * 2^e`。不変条件: `m == 0 || odd(m)`。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RealCenter {
    pub m: i128,
    pub e: i32,
}

impl RealCenter {
    /// 正規化コンストラクタ (`m` の偶因子を `e` に吸収)。
    /// `None` は `e` の `checked` オーバーフローのみ (入力は常に正規化される)。
    pub fn new(m: i128, e: i32) -> Option<Self> {
        let (m, e) = normalize(m, e)?;
        Some(RealCenter { m, e })
    }

    /// 幅検査付き: `m` が符号付き `m_width` ビットに収まること。
    pub fn new_valid(m: i128, e: i32, m_width: Option<u32>) -> Option<Self> {
        let v = Self::new(m, e)?;
        if v.is_valid(m_width) {
            Some(v)
        } else {
            None
        }
    }

    /// `m` が符号付き `m_width` ビットに収まること (`None` = 無検査)。
    /// 正規形 (`odd`) 自体は `new` で保証済みのためここでは検査しない。
    pub fn is_valid(&self, m_width: Option<u32>) -> bool {
        match m_width {
            None => true,
            Some(w) => {
                if w == 0 || w > 127 {
                    return false;
                }
                let lo = -(1i128 << (w - 1));
                let hi = (1i128 << (w - 1)) - 1;
                lo <= self.m && self.m <= hi
            }
        }
    }

    /// 中心値の正確な10進展開 (`mepk` の表示流用、同形式)。
    pub fn centre_exact(&self) -> String {
        decimal_of_scaled(self.m, self.e, None)
    }

    pub fn centre_short(&self) -> String {
        decimal_of_scaled(self.m, self.e, Some(27))
    }
}

/// `m` の偶因子を `e` に吸収 (`m == 0` はそのまま)。
fn normalize(m: i128, e: i32) -> Option<(i128, i32)> {
    if m == 0 {
        return Some((0, e));
    }
    let mut mag = m.unsigned_abs();
    let mut e = e;
    while mag.is_multiple_of(2) {
        mag /= 2;
        e = e.checked_add(1)?;
    }
    let m = if m < 0 {
        if mag == i128::MAX as u128 + 1 {
            i128::MIN
        } else if mag > i128::MAX as u128 {
            return None;
        } else {
            -(mag as i128)
        }
    } else {
        if mag > i128::MAX as u128 {
            return None;
        }
        mag as i128
    };
    Some((m, e))
}

fn decimal_of_scaled(m: i128, e: i32, frac_cap: Option<usize>) -> String {
    if m == 0 {
        return "0".to_string();
    }
    let neg = m < 0;
    let mag = m.unsigned_abs();
    let sign = if neg { "-" } else { "" };
    if e >= 0 {
        match mag.checked_mul(1u128.checked_shl(e as u32).unwrap_or(u128::MAX)) {
            Some(v) => return format!("{sign}{v}"),
            None => return format!("{sign}{mag}*2^{e}"),
        }
    }
    let shift = (-(e as i64)) as u32;
    if shift > 120 {
        return format!("{sign}{mag}*2^{e}");
    }
    let unit = 1u128 << shift;
    let int_part = mag >> shift;
    let mut rem = mag & (unit - 1);
    let mut digits = Vec::with_capacity((shift as usize).min(64));
    for _ in 0..shift {
        if rem == 0 {
            break;
        }
        rem = match rem.checked_mul(10) {
            Some(v) => v,
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

/// 加減算 (`sign` = +1/-1)。exact、`None` はオーバーフロー。
pub fn real_add(x1: &RealCenter, x2: &RealCenter, sign: i8) -> Option<RealCenter> {
    if sign != 1 && sign != -1 {
        return None;
    }
    if x1.m == 0 {
        return if sign == 1 || x2.m == 0 {
            Some(*x2)
        } else {
            RealCenter::new(x2.m.checked_neg()?, x2.e)
        };
    }
    if x2.m == 0 {
        return Some(*x1);
    }
    let ell = x1.e.min(x2.e);
    let d1 = (x1.e - ell) as u32;
    let d2 = (x2.e - ell) as u32;
    // シフト量の上限 (i128 範囲外はオーバーフロー扱い)。
    if d1 > 127 || d2 > 127 {
        return None;
    }
    let t1 = x1.m.checked_shl(d1)?;
    let mut t2 = x2.m.checked_shl(d2)?;
    if sign == -1 {
        t2 = t2.checked_neg()?;
    }
    let total = t1.checked_add(t2)?;
    RealCenter::new(total, ell)
}

/// 乗算。exact、`None` はオーバーフロー。
pub fn real_mul(x1: &RealCenter, x2: &RealCenter) -> Option<RealCenter> {
    if x1.m == 0 || x2.m == 0 {
        // ゼロは `e` を正規化しない (スケール情報を保持)。
        let e = x1.e.checked_add(x2.e)?;
        return Some(RealCenter { m: 0, e });
    }
    let prod = x1.m.checked_mul(x2.m)?;
    let e = x1.e.checked_add(x2.e)?;
    RealCenter::new(prod, e)
}

/// 除算 (exact のみ)。`m2 == 0`・割り切れない組み合わせは `None`
/// (solver では UNSAT)。ゼロ分子は `e = e1 - e2` で `m = 0`。
pub fn real_div(x1: &RealCenter, x2: &RealCenter) -> Option<RealCenter> {
    if x2.m == 0 {
        return None;
    }
    if x1.m == 0 {
        let e = x1.e.checked_sub(x2.e)?;
        return Some(RealCenter { m: 0, e });
    }
    let neg = (x1.m < 0) != (x2.m < 0);
    let mut a = x1.m.unsigned_abs();
    let mut b = x2.m.unsigned_abs();
    // 2の因子を除去: a = a_odd * 2^sa, b = b_odd * 2^sb。
    // (RealCenter は正規形なので a, b とも奇数のはずだが、
    // 汎用に除去して exact 判定する。)
    let mut sa = 0i32;
    while a.is_multiple_of(2) {
        a /= 2;
        sa = sa.checked_add(1)?;
    }
    let mut sb = 0i32;
    while b.is_multiple_of(2) {
        b /= 2;
        sb = sb.checked_add(1)?;
    }
    if a.checked_rem(b)? != 0 {
        return None;
    }
    let q_odd = a / b;
    let e = x1
        .e
        .checked_sub(x2.e)?
        .checked_add(sa)?
        .checked_sub(sb)?;
    let q = if q_odd > i128::MAX as u128 {
        return None;
    } else {
        q_odd as i128
    };
    let q = if neg { q.checked_neg()? } else { q };
    RealCenter::new(q, e)
}

// ---------------------------------------------------------------------------
// 10進リテラル変換 (dyadic のみ exact)
// ---------------------------------------------------------------------------

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
    // 小数点必須 (整数は Int リテラルであり Real ではない)。
    if frac_part.is_empty() && exp_str.is_none() && !mant.contains('.') {
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
    if k > 38 {
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

/// 10進リテラルを exact dyadic として変換。非 dyadic・範囲外は `None`。
/// `m_width` 指定時は幅も検査する。
pub fn decimal_to_real(s: &str, m_width: Option<u32>) -> Option<RealCenter> {
    let (neg, digits, exp10) = parse_decimal(s)?;
    if digits == 0 {
        let v = RealCenter { m: 0, e: 0 };
        return if v.is_valid(m_width) { Some(v) } else { None };
    }
    let apply_sign = |v: i128| -> Option<i128> {
        if neg { v.checked_neg() } else { Some(v) }
    };
    if exp10 >= 0 {
        let raw_u = digits.checked_mul(pow10_u128(exp10 as u32)?)?;
        let raw = apply_sign(to_i128(raw_u)?)?;
        // e=0 の整数として正規化 (偶因子は e に吸収)。
        let v = RealCenter::new(raw, 0)?;
        return if v.is_valid(m_width) { Some(v) } else { None };
    }
    // exp10 < 0: digits / 10^k を約分し、分母から 2 を除去して
    // 5^b が残れば分子に 2^b を掛けて dyadic 化する。
    let k = exp10.checked_neg()? as u32;
    let den = pow10_u128(k)?;
    let g = gcd_u128(digits, den);
    let num_r = digits / g;
    let mut den_r = den / g;
    let mut a = 0i32;
    while den_r.is_multiple_of(2) {
        den_r /= 2;
        a = a.checked_add(1)?;
    }
    // den_r に 2 以外の素因数 (5 を含む) が残れば非 dyadic。
    if den_r != 1 {
        return None;
    }
    let e = -a;
    let raw = apply_sign(to_i128(num_r)?)?;
    let v = RealCenter::new(raw, e)?;
    if v.is_valid(m_width) { Some(v) } else { None }
}

/// 丸めモード (`decimal_to_real_rounded` 用)。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RealRound {
    /// 最近傍 (タイは half-even、`int_ext` と同一規則)。
    Nearest,
    /// 下側 (`≤ 真値` の最大の表現可能値、toward −inf)。
    Down,
    /// 上側 (`≥ 真値` の最小の表現可能値、toward +inf)。
    Up,
}

/// `floor(log2(digits / 10^k))` (`digits > 0`)。`mepk` の同名関数と同形。
fn floor_log2_div(digits: u128, k: u32) -> Option<i32> {
    debug_assert!(digits > 0);
    let den = pow10_u128(k)?;
    let le = |e: i32| -> bool {
        if e >= 0 {
            match 2u128.checked_pow(e as u32).and_then(|p| p.checked_mul(den)) {
                Some(v) => v <= digits,
                None => false,
            }
        } else {
            match digits.checked_shl((-e) as u32) {
                Some(v) => v >= den,
                None => true,
            }
        }
    };
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

/// 10進リテラルを `m` 幅いっぱいの仮数に丸めて変換。dyadic 入力は
/// 全モードで exact 変換と同一 (`decimal_to_real` 相当)。非 dyadic は
/// `q ≈ value·2^s` (`bitlen(q) = m_width−1` 狙い) を整数除算し、モード
/// に応じて丸める。`m_width == None` の非 dyadic は幅不定のため `None`。
/// 丸め誤差は追跡されない (Down/Up の bracketing で挟むこと)。
pub fn decimal_to_real_rounded(
    s: &str,
    m_width: Option<u32>,
    mode: RealRound,
) -> Option<RealCenter> {
    let (neg, digits, exp10) = parse_decimal(s)?;
    if digits == 0 {
        let v = RealCenter { m: 0, e: 0 };
        return if v.is_valid(m_width) { Some(v) } else { None };
    }
    // dyadic 判定: 約分後の分母が 2 の冪のみか。
    let is_dyadic = |digits: u128, exp10: i32| -> bool {
        if exp10 >= 0 {
            return true;
        }
        let k = match exp10.checked_neg() {
            Some(k) => k as u32,
            None => return false,
        };
        let den = match pow10_u128(k) {
            Some(d) => d,
            None => return false,
        };
        let mut den_r = den / gcd_u128(digits, den);
        while den_r.is_multiple_of(2) {
            den_r /= 2;
        }
        den_r == 1
    };
    if is_dyadic(digits, exp10) {
        return decimal_to_real(s, m_width);
    }
    // 非 dyadic: 丸め幅が必須。
    let mw = m_width?;
    if mw < 2 || mw > 30 {
        return None;
    }
    // 目標仮数ビット長 (符号込みレーン幅から符号分を除く)。
    let p = (mw - 1).max(1);
    if exp10 >= 0 {
        // 非 dyadic かつ exp10 >= 0 は到達不能 (整数は常に dyadic)。
        return None;
    }
    let k = exp10.checked_neg()? as u32;
    let den = pow10_u128(k)?;
    // `s = p − 1 − e_est` で `q = digits·2^s / den` の bitlen ≈ p。
    let e_est = floor_log2_div(digits, k)?;
    let s = (p as i32 - 1 - e_est).max(0) as u32;
    if s >= 128 {
        return None;
    }
    let num = digits.checked_mul(2u128.checked_pow(s)?)?;
    let q0 = num.checked_div(den)?;
    let rem = num.checked_rem(den)?;
    let qmag = match mode {
        RealRound::Nearest => round_half_even_step(q0, rem, den)?,
        RealRound::Down => {
            // `≤ 真値`: 正は切り捨て、負は切り上げ (絶対値増)。
            if rem == 0 {
                q0
            } else if neg {
                q0.checked_add(1)?
            } else {
                q0
            }
        }
        RealRound::Up => {
            if rem == 0 {
                q0
            } else if neg {
                q0
            } else {
                q0.checked_add(1)?
            }
        }
    };
    let raw = to_i128(qmag)?;
    let raw = if neg { raw.checked_neg()? } else { raw };
    let v = RealCenter::new(raw, -(s as i32))?;
    if v.is_valid(Some(mw)) { Some(v) } else { None }
}

/// Exact rational `num/den` (`den > 0`)。検証・leaf 入力用。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Rat {
    pub num: i128,
    pub den: i128,
}

impl Rat {
    pub fn new(num: i128, den: i128) -> Option<Self> {
        if den <= 0 {
            return None;
        }
        Some(Rat { num, den })
    }

    fn add(self, o: Rat) -> Option<Rat> {
        Rat::new(
            self.num.checked_mul(o.den)?.checked_add(o.num.checked_mul(self.den)?)?,
            self.den.checked_mul(o.den)?,
        )
    }

    fn sub(self, o: Rat) -> Option<Rat> {
        Rat::new(
            self.num.checked_mul(o.den)?.checked_sub(o.num.checked_mul(self.den)?)?,
            self.den.checked_mul(o.den)?,
        )
    }

    fn mul(self, o: Rat) -> Option<Rat> {
        Rat::new(self.num.checked_mul(o.num)?, self.den.checked_mul(o.den)?)
    }

    fn div(self, o: Rat) -> Option<Rat> {
        if o.num == 0 {
            return None;
        }
        let (n, d) = if o.num > 0 {
            (self.num.checked_mul(o.den)?, self.den.checked_mul(o.num)?)
        } else {
            (
                self.num.checked_mul(o.den)?.checked_neg()?,
                self.den.checked_mul(o.num.checked_neg()?)?,
            )
        };
        Rat::new(n, d)
    }
}

/// leaf の exact 入力を `RealCenter` に丸めなしで変換。
/// dyadic のみ `Some` (非 dyadic は leaf 自体が表現不能で `None`)。
fn leaf_round(num: i128, den: i128) -> Option<RealCenter> {
    if den <= 0 {
        return None;
    }
    if num == 0 {
        return Some(RealCenter { m: 0, e: 0 });
    }
    if den == 1 {
        return RealCenter::new(num, 0);
    }
    // num/den を約分し、分母が 2 の冪のみなら exact dyadic。
    let neg = (num < 0) != (den < 0);
    let n = num.unsigned_abs();
    let d = den.unsigned_abs();
    let g = gcd_u128(n, d);
    let n = n / g;
    let mut d = d / g;
    let mut e: i32 = 0;
    while d.is_multiple_of(2) {
        d /= 2;
        e = e.checked_sub(1)?;
    }
    if d != 1 {
        return None;
    }
    let raw = to_i128(n)?;
    let raw = if neg { raw.checked_neg()? } else { raw };
    RealCenter::new(raw, e)
}

// ---------------------------------------------------------------------------
// 式木 (ランタイム評価用、CEGAR なし)
// ---------------------------------------------------------------------------

/// 二項演算子。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RealOp {
    Add,
    Sub,
    Mul,
    Div,
}

/// 式木: exact-rational leaf + 演算子ノード。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RealExpr {
    Leaf { num: i128, den: i128 },
    Bin {
        op: RealOp,
        left: Box<RealExpr>,
        right: Box<RealExpr>,
    },
}

impl RealExpr {
    pub fn leaf(num: i128, den: i128) -> Self {
        RealExpr::Leaf { num, den }
    }

    pub fn bin(op: RealOp, left: RealExpr, right: RealExpr) -> Self {
        RealExpr::Bin {
            op,
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

/// 評価失敗理由。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RealEvalError {
    /// ゼロ除算。
    DivByZero,
    /// 割り切れない除算 (exact 表現なし)。
    InexactDiv,
    /// 非 dyadic leaf (丸めなしでは表現不能)。
    InexactLeaf,
    /// `i128` 範囲超過。
    OracleRange,
}

/// 中心のみのボトムアップ評価 (exact)。
pub fn evaluate(e: &RealExpr) -> Result<RealCenter, RealEvalError> {
    match e {
        RealExpr::Leaf { num, den } => leaf_round(*num, *den).ok_or_else(|| {
            if *den <= 0 {
                RealEvalError::OracleRange
            } else {
                RealEvalError::InexactLeaf
            }
        }),
        RealExpr::Bin { op, left, right } => {
            let l = evaluate(left)?;
            let r = evaluate(right)?;
            match op {
                RealOp::Add => real_add(&l, &r, 1).ok_or(RealEvalError::OracleRange),
                RealOp::Sub => real_add(&l, &r, -1).ok_or(RealEvalError::OracleRange),
                RealOp::Mul => real_mul(&l, &r).ok_or(RealEvalError::OracleRange),
                RealOp::Div => {
                    if r.m == 0 {
                        return Err(RealEvalError::DivByZero);
                    }
                    real_div(&l, &r).ok_or(RealEvalError::InexactDiv)
                }
            }
        }
    }
}

/// 真値伝播 (検証用)。`None` はオーバーフロー・ゼロ除算。
pub fn true_value(e: &RealExpr) -> Option<Rat> {
    match e {
        RealExpr::Leaf { num, den } => Rat::new(*num, *den),
        RealExpr::Bin { op, left, right } => {
            let (l, r) = (true_value(left)?, true_value(right)?);
            match op {
                RealOp::Add => l.add(r),
                RealOp::Sub => l.sub(r),
                RealOp::Mul => l.mul(r),
                RealOp::Div => l.div(r),
            }
        }
    }
}

/// `truth == centre` を exact に検査。`None` はオーバーフロー。
pub fn verify(v: &RealCenter, t: Rat) -> Option<bool> {
    // t.num/t.den == m * 2^e ⟺ t.num == m * t.den * 2^e (e >= 0)
    // または t.num * 2^-e == m * t.den (e < 0)。
    if v.m == 0 {
        return Some(t.num == 0);
    }
    if v.e >= 0 {
        let rhs = v
            .m
            .checked_mul(t.den)?
            .checked_mul(1i128.checked_shl(v.e as u32)?)?;
        Some(t.num == rhs)
    } else {
        let lhs = t.num.checked_mul(1i128.checked_shl((-v.e) as u32)?)?;
        let rhs = v.m.checked_mul(t.den)?;
        Some(lhs == rhs)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn normalize_strips_twos() {
        assert_eq!(RealCenter::new(12, 0), Some(RealCenter { m: 3, e: 2 }));
        assert_eq!(RealCenter::new(0, 99), Some(RealCenter { m: 0, e: 99 }));
        assert_eq!(RealCenter::new(-12, 0), Some(RealCenter { m: -3, e: 2 }));
    }

    #[test]
    fn add_sub_exact() {
        let a = RealCenter::new(3, 0).unwrap(); // 3
        let b = RealCenter::new(1, -1).unwrap(); // 0.5
        assert_eq!(real_add(&a, &b, 1).unwrap(), RealCenter { m: 7, e: -1 });
        assert_eq!(real_add(&a, &b, -1).unwrap(), RealCenter { m: 5, e: -1 });
    }

    #[test]
    fn mul_div_exact() {
        let a = RealCenter::new(3, 0).unwrap();
        let b = RealCenter::new(1, -1).unwrap();
        assert_eq!(real_mul(&a, &b).unwrap(), RealCenter { m: 3, e: -1 });
        // 3 / 0.5 = 6.
        assert_eq!(real_div(&a, &b).unwrap(), RealCenter { m: 3, e: 1 });
        // 1 / 3 は割り切れない。
        let one = RealCenter::new(1, 0).unwrap();
        let three = RealCenter::new(3, 0).unwrap();
        assert!(real_div(&one, &three).is_none());
        assert!(real_div(&a, &RealCenter { m: 0, e: 0 }).is_none());
    }

    #[test]
    fn decimal_dyadic_only() {
        assert_eq!(
            decimal_to_real("0.5", None).unwrap(),
            RealCenter { m: 1, e: -1 }
        );
        assert_eq!(
            decimal_to_real("3.0", None).unwrap(),
            RealCenter { m: 3, e: 0 }
        );
        assert!(decimal_to_real("0.1", None).is_none());
        assert!(decimal_to_real("3", None).is_none());
    }

    #[test]
    fn expr_verify() {
        // (1/2 + 1/4) * 4 = 3.
        let e = RealExpr::bin(
            RealOp::Mul,
            RealExpr::bin(
                RealOp::Add,
                RealExpr::leaf(1, 2),
                RealExpr::leaf(1, 4),
            ),
            RealExpr::leaf(4, 1),
        );
        let v = evaluate(&e).unwrap();
        assert_eq!(v, RealCenter { m: 3, e: 0 });
        assert_eq!(verify(&v, true_value(&e).unwrap()), Some(true));
    }

    /// 符号付き比較 `a ? b` (i128 範囲内の小さな値用): `-1/0/1`。
    fn cmp_centres(a: &RealCenter, b: &RealCenter) -> Option<i32> {
        let ell = a.e.min(b.e);
        let da = (a.e - ell) as u32;
        let db = (b.e - ell) as u32;
        if da > 100 || db > 100 {
            return None;
        }
        let x = a.m.checked_shl(da)?;
        let y = b.m.checked_shl(db)?;
        Some(x.cmp(&y) as i32)
    }

    #[test]
    fn rounded_modes_bracket_tenth() {
        // 0.1 at m_width 8 (p = 7): Nearest/Down/Up.
        let mw = Some(8u32);
        let n = decimal_to_real_rounded("0.1", mw, RealRound::Nearest).unwrap();
        let d = decimal_to_real_rounded("0.1", mw, RealRound::Down).unwrap();
        let u = decimal_to_real_rounded("0.1", mw, RealRound::Up).unwrap();
        for v in [&n, &d, &u] {
            assert!(v.is_valid(mw), "lane fit: {v:?}");
            assert!(v.m == 0 || v.m % 2 != 0, "odd: {v:?}");
        }
        // Bracketing: Down ≤ 0.1 ≤ Up (rational check), Down < Up.
        assert_eq!(cmp_centres(&d, &u), Some(-1));
        // |d| vs truth: d ≤ 1/10 ≤ u ⟺ d*10 ≤ 1 ≤ u*10.
        let scaled = |v: &RealCenter| -> Option<i128> {
            if v.e >= 0 {
                v.m.checked_mul(10)?.checked_mul(1i128.checked_shl(v.e as u32)?)
            } else {
                v.m.checked_mul(10)
            }
        };
        let unit = |v: &RealCenter| -> Option<i128> {
            if v.e >= 0 {
                Some(1)
            } else {
                1i128.checked_shl((-v.e) as u32)
            }
        };
        assert!(scaled(&d).unwrap() <= unit(&d).unwrap());
        assert!(scaled(&u).unwrap() >= unit(&u).unwrap());
        // Nearest is one of the two brackets.
        assert!(n == d || n == u, "nearest {n:?} not a bracket of {d:?}/{u:?}");
        // 1 ulp apart at the common scale (Down may normalize to a
        // coarser exponent, so compare scaled to ell = min).
        let ell = d.e.min(u.e);
        let ds = d.m.checked_shl((d.e - ell) as u32).unwrap();
        let us = u.m.checked_shl((u.e - ell) as u32).unwrap();
        assert_eq!(us - ds, 1);
    }

    #[test]
    fn rounded_dyadic_is_noop() {
        // dyadic 入力は全モードで exact 変換と同一。
        for lit in ["0.5", "3.0", "-1.5", "2.0"] {
            let exact = decimal_to_real(lit, Some(8)).unwrap();
            for mode in [RealRound::Nearest, RealRound::Down, RealRound::Up] {
                assert_eq!(decimal_to_real_rounded(lit, Some(8), mode).unwrap(), exact, "{lit} {mode:?}");
            }
        }
    }

    #[test]
    fn rounded_negative_tenth() {
        // 符号対称: Down(-0.1) == -Up(0.1), Up(-0.1) == -Down(0.1).
        let mw = Some(8u32);
        let dn = decimal_to_real_rounded("-0.1", mw, RealRound::Down).unwrap();
        let up = decimal_to_real_rounded("-0.1", mw, RealRound::Up).unwrap();
        let pd = decimal_to_real_rounded("0.1", mw, RealRound::Down).unwrap();
        let pu = decimal_to_real_rounded("0.1", mw, RealRound::Up).unwrap();
        assert_eq!((dn.m, dn.e), (-pu.m, pu.e));
        assert_eq!((up.m, up.e), (-pd.m, pd.e));
    }

    #[test]
    fn rounded_needs_width() {
        // 非 dyadic に幅なしは None (幅不定)。
        assert!(decimal_to_real_rounded("0.1", None, RealRound::Nearest).is_none());
    }
}
