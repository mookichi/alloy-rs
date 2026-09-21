use crate::bmatrix::BoolCtx;
use crate::bool::{const_false, const_true, BoolRef};

#[derive(Clone, Debug)]
pub struct IntCircuit {
    pub bits: Vec<BoolRef>,
    ctx: BoolCtx,
    /// True when a `Signed` value contributed to this circuit.
    /// Only tainted circuits produce arithmetic overflow signals;
    /// pure-`Int` circuits stay wrapping with `FALSE` overflow.
    tainted: bool,
    /// Overflow of this operation alone (FALSE when untainted,
    /// except division-by-zero which is always active).
    overflow: BoolRef,
    /// Transitive OR of all upstream overflows (incl. division-by-zero).
    accum_overflow: BoolRef,
}

fn xor2(ctx: &BoolCtx, a: BoolRef, b: BoolRef) -> BoolRef {
    ctx.or(&[ctx.and(&[a, ctx.not(b)]), ctx.and(&[ctx.not(a), b])])
}

fn sum3(ctx: &BoolCtx, a: BoolRef, b: BoolRef, c: BoolRef) -> BoolRef {
    let ab = xor2(ctx, a, b);
    xor2(ctx, ab, c)
}

fn carry3(ctx: &BoolCtx, a: BoolRef, b: BoolRef, c: BoolRef) -> BoolRef {
    let ab = ctx.and(&[a, b]);
    let ab_c = ctx.and(&[c, ctx.or(&[a, b])]);
    ctx.or(&[ab, ab_c])
}

fn iff(ctx: &BoolCtx, a: BoolRef, b: BoolRef) -> BoolRef {
    ctx.not(xor2(ctx, a, b))
}

fn implies(ctx: &BoolCtx, a: BoolRef, b: BoolRef) -> BoolRef {
    ctx.or(&[ctx.not(a), b])
}

impl IntCircuit {
    pub fn constant(value: i64, width: u32, ctx: &BoolCtx) -> IntCircuit {
        let mut bits = Vec::with_capacity(width as usize);
        for i in 0..width as usize {
            let bit_set = ((value >> i) & 1) == 1;
            bits.push(if bit_set { const_true() } else { const_false() });
        }
        IntCircuit {
            bits,
            ctx: ctx.clone(),
            tainted: false,
            overflow: const_false(),
            accum_overflow: const_false(),
        }
    }

    pub fn from_bits(bits: Vec<BoolRef>, ctx: &BoolCtx) -> IntCircuit {
        IntCircuit {
            bits,
            ctx: ctx.clone(),
            tainted: false,
            overflow: const_false(),
            accum_overflow: const_false(),
        }
    }

    /// Mark this circuit as `Signed`-derived. Chained by `fol` translation.
    pub fn with_taint(mut self, tainted: bool) -> IntCircuit {
        self.tainted = tainted;
        self
    }

    pub fn is_tainted(&self) -> bool {
        self.tainted
    }

    pub fn overflow(&self) -> BoolRef {
        self.overflow
    }

    pub fn accum_overflow(&self) -> BoolRef {
        self.accum_overflow
    }

    fn merged_accum(&self, other: &IntCircuit, fresh: BoolRef) -> BoolRef {
        self.ctx.or(&[
            self.accum_overflow,
            other.accum_overflow,
            fresh,
        ])
    }

    pub fn zero(ctx: &BoolCtx) -> IntCircuit {
        IntCircuit::constant(0, 1, ctx)
    }

    pub fn width(&self) -> usize {
        self.bits.len()
    }

    pub fn bit(&self, i: usize) -> BoolRef {
        if i < self.bits.len() {
            self.bits[i]
        } else {
            *self.bits.last().unwrap_or(&const_false())
        }
    }

    pub fn ctx(&self) -> &BoolCtx {
        &self.ctx
    }

    fn extend_bits(&self, extwidth: usize) -> Vec<BoolRef> {
        let mut ext = Vec::with_capacity(extwidth);
        ext.extend_from_slice(&self.bits);
        let sign = *self.bits.last().unwrap_or(&const_false());
        while ext.len() < extwidth {
            ext.push(sign);
        }
        ext
    }

    pub fn add(&self, other: &IntCircuit, bitwidth: u32) -> IntCircuit {
        let width = std::cmp::min(
            std::cmp::max(self.width(), other.width()) + 1,
            bitwidth as usize,
        );
        let mut out = Vec::with_capacity(width);
        let mut carry = const_false();
        let mut c1 = const_false();
        let mut c2 = const_false();
        for i in 0..width {
            let (v0, v1) = (self.bit(i), other.bit(i));
            out.push(sum3(&self.ctx, v0, v1, carry));
            carry = carry3(&self.ctx, v0, v1, carry);
            if i + 2 == width {
                c2 = carry;
            } else if i + 1 == width {
                c1 = carry;
            }
        }
        let tainted = self.tainted || other.tainted;
        // Java TwosComplementInt.plus: c1 XOR c2, only when width == bitwidth.
        let fresh = if tainted && width == bitwidth as usize {
            xor2(&self.ctx, c1, c2)
        } else {
            const_false()
        };
        let accum = self.merged_accum(other, fresh);
        let mut ret = IntCircuit::from_bits(out, &self.ctx);
        ret.tainted = tainted;
        ret.overflow = fresh;
        ret.accum_overflow = accum;
        ret
    }

    pub fn sub(&self, other: &IntCircuit, bitwidth: u32) -> IntCircuit {
        let width = std::cmp::min(
            std::cmp::max(self.width(), other.width()) + 1,
            bitwidth as usize,
        );
        let mut out = Vec::with_capacity(width);
        let mut carry = const_true();
        let mut c1 = const_false();
        let mut c2 = const_false();
        for i in 0..width {
            let (v0, v1) = (self.bit(i), self.ctx.not(other.bit(i)));
            out.push(sum3(&self.ctx, v0, v1, carry));
            carry = carry3(&self.ctx, v0, v1, carry);
            if i + 2 == width {
                c2 = carry;
            } else if i + 1 == width {
                c1 = carry;
            }
        }
        let tainted = self.tainted || other.tainted;
        let fresh = if tainted && width == bitwidth as usize {
            xor2(&self.ctx, c1, c2)
        } else {
            const_false()
        };
        let accum = self.merged_accum(other, fresh);
        let mut ret = IntCircuit::from_bits(out, &self.ctx);
        ret.tainted = tainted;
        ret.overflow = fresh;
        ret.accum_overflow = accum;
        ret
    }

    pub fn mul(&self, other: &IntCircuit, bitwidth: u32) -> IntCircuit {
        let ret_width = self.width() + other.width();
        let mut mult = vec![const_false(); ret_width];

        let i_bit_0 = self.bit(0);
        for (j, slot) in mult.iter_mut().enumerate() {
            *slot = self.ctx.and(&[i_bit_0, other.bit(j)]);
        }

        let last = ret_width - 1;
        for i in 1..last {
            let i_bit = self.bit(i);
            let mut carry = const_false();
            for j in 0..ret_width - i {
                let prod = self.ctx.and(&[i_bit, other.bit(j)]);
                let old = mult[i + j];
                mult[i + j] = sum3(&self.ctx, old, prod, carry);
                carry = carry3(&self.ctx, old, prod, carry);
            }
        }

        let i_bit = self.bit(last);
        let mut carry = const_true();
        for j in 0..ret_width - last {
            let prod = self.ctx.and(&[i_bit, other.bit(j)]);
            let negated = self.ctx.not(prod);
            let old = mult[last + j];
            mult[last + j] = sum3(&self.ctx, old, negated, carry);
            carry = carry3(&self.ctx, old, negated, carry);
        }

        let width = std::cmp::min(ret_width, bitwidth as usize);
        // Java TwosComplementInt.multiply: XOR chain over truncated high bits.
        // Skipped entirely for untainted (pure-Int) circuits: zero extra gates.
        let tainted = self.tainted || other.tainted;
        let fresh = if tainted && width < ret_width {
            let mut acc = const_false();
            for i in width..ret_width {
                acc = self.ctx.or(&[acc, xor2(&self.ctx, mult[i - 1], mult[i])]);
            }
            acc
        } else {
            const_false()
        };
        let accum = self.merged_accum(other, fresh);
        mult.truncate(width);
        let mut ret = IntCircuit::from_bits(mult, &self.ctx);
        ret.tainted = tainted;
        ret.overflow = fresh;
        ret.accum_overflow = accum;
        ret
    }

    fn non_restoring_division(
        &self,
        d: &IntCircuit,
        quotient: bool,
        bitwidth: u32,
    ) -> Vec<BoolRef> {
        let width = bitwidth as usize;
        let extended = width * 2 + 1;
        let mut s = self.extend_bits(extended);
        let mut q = vec![const_false(); width];
        let mut svalues = vec![const_false(); width];

        let d_msb = d.bit(width);
        let mut sleft = 0usize;
        for i in 0..width {
            svalues[i] = self.ctx.or(&s);
            let sright = (sleft + extended - 1) % extended;
            let qbit = iff(&self.ctx, s[sright], d_msb);
            q[width - i - 1] = qbit;
            s[sright] = const_false();
            sleft = sright;

            let mut carry = qbit;
            let mut si = (sleft + width) % extended;
            for di in 0..=width {
                let dbit = xor2(&self.ctx, qbit, d.bit(di));
                let sbit = s[si];
                s[si] = sum3(&self.ctx, sbit, dbit, carry);
                carry = carry3(&self.ctx, sbit, dbit, carry);
                si = (si + 1) % extended;
            }
        }

        let _any_svalues = self.ctx.or(&svalues);
        let all_svalues = self.ctx.and(&svalues);
        let s_nonzero = self.ctx.or(&s[..=width]);
        let sign_differs = xor2(&self.ctx, s[width], self.bit(width));
        let incorrect = self.ctx.or(&[
            self.ctx.not(all_svalues),
            self.ctx.and(&[sign_differs, s_nonzero]),
        ]);
        let corrector = iff(&self.ctx, s[width], d.bit(width));

        if quotient {
            for k in (1..width).rev() {
                q[k] = q[k - 1];
            }
            q[0] = const_true();

            let sign = self.ctx.and(&[incorrect, self.ctx.not(corrector)]);
            let mut carry = self.ctx.and(&[incorrect, corrector]);
            for qb_slot in q.iter_mut() {
                let qb = *qb_slot;
                *qb_slot = sum3(&self.ctx, qb, sign, carry);
                carry = carry3(&self.ctx, qb, sign, carry);
            }
            q
        } else {
            let mut carry = self.ctx.and(&[incorrect, corrector]);
            for (di, sb_slot) in s.iter_mut().take(width + 1).enumerate() {
                let dbit = self
                    .ctx
                    .and(&[incorrect, xor2(&self.ctx, corrector, d.bit(di))]);
                let sb = *sb_slot;
                *sb_slot = sum3(&self.ctx, sb, dbit, carry);
                carry = carry3(&self.ctx, sb, dbit, carry);
            }
            s[..width].to_vec()
        }
    }

    pub fn div(&self, other: &IntCircuit, bitwidth: u32) -> IntCircuit {
        let bits = self.non_restoring_division(other, true, bitwidth);
        let mut ret = IntCircuit::from_bits(bits, &self.ctx);
        let (fresh, accum) = self.div_overflow(other, bitwidth);
        ret.tainted = self.tainted || other.tainted;
        ret.overflow = fresh;
        ret.accum_overflow = accum;
        ret
    }

    pub fn rem(&self, other: &IntCircuit, bitwidth: u32) -> IntCircuit {
        let bits = self.non_restoring_division(other, false, bitwidth);
        let mut ret = IntCircuit::from_bits(bits, &self.ctx);
        let (fresh, accum) = self.div_overflow(other, bitwidth);
        ret.tainted = self.tainted || other.tainted;
        ret.overflow = fresh;
        ret.accum_overflow = accum;
        ret
    }

    /// `overflow = divByZero OR (tainted AND INT_MIN/-1)`.
    /// Division-by-zero is UNSAT regardless of `Signed` taint (agreed spec);
    /// the `INT_MIN / -1` case only fires for tainted circuits.
    fn div_overflow(&self, other: &IntCircuit, bitwidth: u32) -> (BoolRef, BoolRef) {
        let w = bitwidth as usize;
        let mut or_inputs = Vec::with_capacity(w);
        for i in 0..w {
            or_inputs.push(other.bit(i));
        }
        let any_nonzero = self.ctx.or(&or_inputs);
        let div_by_zero = self.ctx.not(any_nonzero);
        let tainted = self.tainted || other.tainted;
        let fresh = if tainted {
            let min = IntCircuit::constant(i64::MIN >> (64 - w as u32), w as u32, &self.ctx);
            let neg_one = IntCircuit::constant(-1, w as u32, &self.ctx);
            // self == INT_MIN AND other == -1; constants are untainted so
            // `eq` here is a pure comparison (no gating recursion).
            let is_min = self.raw_eq(&min);
            let is_neg_one = other.raw_eq(&neg_one);
            let single = self.ctx.and(&[is_min, is_neg_one]);
            self.ctx.or(&[div_by_zero, single])
        } else {
            div_by_zero
        };
        let accum = self.merged_accum(other, fresh);
        (fresh, accum)
    }

    /// Pure bitwise equality without overflow gating (helper for div_overflow).
    fn raw_eq(&self, other: &IntCircuit) -> BoolRef {
        let width = std::cmp::max(self.width(), other.width());
        let mut acc = const_true();
        for i in 0..width {
            acc = self
                .ctx
                .and(&[acc, iff(&self.ctx, self.bit(i), other.bit(i))]);
        }
        acc
    }

    pub fn neg(&self, bitwidth: u32) -> IntCircuit {
        IntCircuit::zero(&self.ctx).sub(self, bitwidth)
    }

    pub fn bit_not(&self) -> IntCircuit {
        let bits = self.bits.iter().map(|&b| self.ctx.not(b)).collect();
        let mut ret = IntCircuit::from_bits(bits, &self.ctx);
        ret.tainted = self.tainted;
        ret.overflow = const_false();
        ret.accum_overflow = self.accum_overflow;
        ret
    }

    fn bitwise(&self, other: &IntCircuit, f: impl Fn(BoolRef, BoolRef) -> BoolRef) -> IntCircuit {
        let width = std::cmp::max(self.width(), other.width());
        let mut ret = IntCircuit::from_bits(
            (0..width).map(|i| f(self.bit(i), other.bit(i))).collect(),
            &self.ctx,
        );
        ret.tainted = self.tainted || other.tainted;
        ret.overflow = const_false();
        ret.accum_overflow = self.ctx.or(&[self.accum_overflow, other.accum_overflow]);
        ret
    }

    pub fn bit_and(&self, other: &IntCircuit) -> IntCircuit {
        let ctx = self.ctx.clone();
        self.bitwise(other, |a, b| ctx.and(&[a, b]))
    }

    pub fn bit_or(&self, other: &IntCircuit) -> IntCircuit {
        let ctx = self.ctx.clone();
        self.bitwise(other, |a, b| ctx.or(&[a, b]))
    }

    pub fn bit_xor(&self, other: &IntCircuit) -> IntCircuit {
        let ctx = self.ctx.clone();
        self.bitwise(other, |a, b| xor2(&ctx, a, b))
    }

    pub fn shl(&self, other: &IntCircuit, bitwidth: u32) -> IntCircuit {
        let width = bitwidth as usize;
        let mut shifted = self.extend_bits(width);
        for i in 0..width {
            let shift = 1usize << i;
            let bit = other.bit(i);
            if i < (usize::BITS - (width - 1).leading_zeros()) as usize {
                for j in (0..width).rev() {
                    let moved = if j < shift {
                        const_false()
                    } else {
                        shifted[j - shift]
                    };
                    shifted[j] = self.ctx.ite(bit, moved, shifted[j]);
                }
            }
        }
        // TODO(Iter2): shift-out overflow detection (Java accumulate port).
        let mut ret = IntCircuit::from_bits(shifted, &self.ctx);
        ret.tainted = self.tainted || other.tainted;
        ret.accum_overflow = self.ctx.or(&[self.accum_overflow, other.accum_overflow]);
        ret
    }

    fn shr_with_fill(&self, other: &IntCircuit, fill_bit: BoolRef, bitwidth: u32) -> IntCircuit {
        let width = bitwidth as usize;
        let mut shifted = self.extend_bits(width);
        let max = (usize::BITS - (width - 1).leading_zeros()) as usize;
        for i in 0..max {
            let shift = 1usize << i;
            let fill = width - shift;
            let bit = other.bit(i);
            for j in 0..width {
                let moved = if j < fill {
                    shifted[j + shift]
                } else {
                    fill_bit
                };
                shifted[j] = self.ctx.ite(bit, moved, shifted[j]);
            }
        }
        let mut ret = IntCircuit::from_bits(shifted, &self.ctx);
        ret.tainted = self.tainted || other.tainted;
        ret.accum_overflow = self.ctx.or(&[self.accum_overflow, other.accum_overflow]);
        ret
    }

    pub fn shr(&self, other: &IntCircuit, bitwidth: u32) -> IntCircuit {
        self.shr_with_fill(other, const_false(), bitwidth)
    }

    pub fn sha(&self, other: &IntCircuit, bitwidth: u32) -> IntCircuit {
        let sign = *self.bits.last().unwrap_or(&const_false());
        self.shr_with_fill(other, sign, bitwidth)
    }

    pub fn choice(&self, condition: BoolRef, other: &IntCircuit) -> IntCircuit {
        let width = std::cmp::max(self.width(), other.width());
        let bits = (0..width)
            .map(|i| self.ctx.ite(condition, self.bit(i), other.bit(i)))
            .collect();
        let mut ret = IntCircuit::from_bits(bits, &self.ctx);
        ret.tainted = self.tainted || other.tainted;
        ret.overflow = const_false();
        ret.accum_overflow = self.ctx.or(&[self.accum_overflow, other.accum_overflow]);
        ret
    }

    pub fn eq(&self, other: &IntCircuit) -> BoolRef {
        self.raw_eq(other)
    }

    pub fn lte(&self, other: &IntCircuit) -> BoolRef {
        let last = std::cmp::max(self.width(), other.width()) - 1;
        let mut cmp = implies(&self.ctx, other.bit(last), self.bit(last));
        let mut prev_equals = iff(&self.ctx, self.bit(last), other.bit(last));
        for i in (0..last).rev() {
            let (v0, v1) = (self.bit(i), other.bit(i));
            cmp = self.ctx.and(&[
                cmp,
                implies(&self.ctx, prev_equals, implies(&self.ctx, v0, v1)),
            ]);
            prev_equals = self.ctx.and(&[prev_equals, iff(&self.ctx, v0, v1)]);
        }
        cmp
    }

    pub fn neq(&self, other: &IntCircuit) -> BoolRef {
        self.ctx.not(self.eq(other))
    }

    pub fn lt(&self, other: &IntCircuit) -> BoolRef {
        self.ctx.not(other.lte(self))
    }

    pub fn gt(&self, other: &IntCircuit) -> BoolRef {
        self.ctx.not(self.lte(other))
    }

    pub fn gte(&self, other: &IntCircuit) -> BoolRef {
        other.lte(self)
    }

    pub fn value_of(&self, model: &[bool]) -> i64 {
        self.ctx.with_factory(|factory| {
            let mut memo: Vec<Option<bool>> = Vec::new();
            let mut value: i64 = 0;
            for (i, &b) in self.bits.iter().enumerate() {
                if factory.eval_memo(b, model, &mut memo) {
                    value |= 1 << i;
                }
            }
            let w = self.bits.len() as u32;
            if w < 64 {
                let sign = 1i64 << (w - 1);
                if value & sign != 0 {
                    value -= 1i64 << w;
                }
            }
            value
        })
    }
}

/// Unsigned constant bit-vector (zero-extended), for magnitudes.
fn const_u_bits(value: u128, width: usize) -> Vec<BoolRef> {
    (0..width)
        .map(|i| {
            if ((value >> i) & 1) == 1 {
                const_true()
            } else {
                const_false()
            }
        })
        .collect()
}

/// Zero-extending bit accessor for unsigned (magnitude) vectors.
fn zbit(bits: &[BoolRef], i: usize) -> BoolRef {
    if i < bits.len() {
        bits[i]
    } else {
        const_false()
    }
}

/// Two's-complement negation of a little-endian bit-vector.
/// Returns `(negated, carry_out)`; `carry_out` is discarded by most callers.
fn twos_neg(ctx: &BoolCtx, bits: &[BoolRef]) -> (Vec<BoolRef>, BoolRef) {
    let inv: Vec<BoolRef> = bits.iter().map(|&b| ctx.not(b)).collect();
    increment_if(ctx, &inv, const_true())
}

/// Ripple increment: `out = bits + (flag ? 1 : 0)`. Returns `(out, carry_out)`.
fn increment_if(ctx: &BoolCtx, bits: &[BoolRef], flag: BoolRef) -> (Vec<BoolRef>, BoolRef) {
    // Half-adder chain: `sum = b XOR 0 XOR c`, `carry = (b AND 0) OR (c AND (b OR 0))`.
    let mut out = Vec::with_capacity(bits.len());
    let mut carry = flag;
    for &b in bits {
        out.push(sum3(ctx, b, const_false(), carry));
        carry = carry3(ctx, b, const_false(), carry);
    }
    (out, carry)
}

/// Unsigned equality over zero-extended vectors.
fn eq_u(ctx: &BoolCtx, a: &[BoolRef], b: &[BoolRef]) -> BoolRef {
    let w = std::cmp::max(a.len(), b.len());
    let mut acc = const_true();
    for i in 0..w {
        acc = ctx.and(&[acc, iff(ctx, zbit(a, i), zbit(b, i))]);
    }
    acc
}

/// Unsigned strict less-than over zero-extended vectors.
fn ult_u(ctx: &BoolCtx, a: &[BoolRef], b: &[BoolRef]) -> BoolRef {
    let w = std::cmp::max(a.len(), b.len()).max(1);
    // MSB-first lexicographic compare: `lt = OR_i (a_i < b_i AND higher equal)`.
    let mut lt = const_false();
    let mut eq_so_far = const_true();
    for i in (0..w).rev() {
        let (ai, bi) = (zbit(a, i), zbit(b, i));
        // `ai < bi` iff `!ai AND bi`.
        let less_here = ctx.and(&[ctx.not(ai), bi]);
        lt = ctx.or(&[lt, ctx.and(&[eq_so_far, less_here])]);
        eq_so_far = ctx.and(&[eq_so_far, iff(ctx, ai, bi)]);
    }
    lt
}

/// Unsigned `<=` over zero-extended vectors.
fn ule_u(ctx: &BoolCtx, a: &[BoolRef], b: &[BoolRef]) -> BoolRef {
    ctx.not(ult_u(ctx, b, a))
}

/// Bit-length (priority) encoder: `0 -> 0`, else index of the highest set
/// bit plus one. Returned as an unsigned value in the minimum number of
/// bits that can represent `bits.len()`.
fn priority_len_bits(ctx: &BoolCtx, bits: &[BoolRef]) -> Vec<BoolRef> {
    let w = bits.len();
    let out_w = (usize::BITS - (w as u32).leading_zeros()).max(1) as usize;
    let mut len = const_u_bits(0, out_w);
    for (i, &bit) in bits.iter().enumerate() {
        let cand = const_u_bits((i + 1) as u128, out_w);
        for j in 0..out_w {
            len[j] = ctx.ite(bit, cand[j], len[j]);
        }
    }
    len
}

/// Round-to-nearest (ties-to-even) of an unsigned magnitude with a constant
/// drop: the `p`-bit field `mag[drop .. drop+p)` is incremented iff
/// `rest > half` / (`rest == half` and field odd), where `rest = mag[..drop]`
/// and `half = 2^(drop-1)`. Structurally: `above = top AND any_low`,
/// `tie = top AND NOT any_low`.
///
/// Returns `(field_rounded, carry_out)`; `carry_out` set means the field was
/// all ones and wrapped to zero (caller renormalizes to `1 << (p-1)` with
/// `e + 1`). Requires `drop >= 1` and `drop + p <= mag.len()`.
fn round_mag_const_drop(
    ctx: &BoolCtx,
    mag: &[BoolRef],
    drop: u32,
    p: u32,
) -> (Vec<BoolRef>, BoolRef) {
    let (d, p) = (drop as usize, p as usize);
    assert!(d >= 1 && d + p <= mag.len());
    let rest = &mag[..d];
    let field: Vec<BoolRef> = (0..p).map(|i| zbit(mag, d + i)).collect();
    let top = rest[d - 1];
    let low_any = if d > 1 { ctx.or(&rest[..d - 1]) } else { const_false() };
    let above = ctx.and(&[top, low_any]);
    let tie = ctx.and(&[top, ctx.not(low_any)]);
    let field_odd = field[0];
    let round_up = ctx.or(&[above, ctx.and(&[tie, field_odd])]);
    increment_if(ctx, &field, round_up)
}

impl IntCircuit {
    /// Exact (widening) addition: full `max(w1, w2) + 1` bits, no truncation,
    /// no fresh overflow. For §3 `T = m1<<d1 ± m2<<d2`.
    pub fn widen_add(&self, other: &IntCircuit) -> IntCircuit {
        let width = std::cmp::max(self.width(), other.width()) + 1;
        let mut out = Vec::with_capacity(width);
        let mut carry = const_false();
        for i in 0..width {
            let (v0, v1) = (self.bit(i), other.bit(i));
            out.push(sum3(&self.ctx, v0, v1, carry));
            carry = carry3(&self.ctx, v0, v1, carry);
        }
        let mut ret = IntCircuit::from_bits(out, &self.ctx);
        ret.tainted = self.tainted || other.tainted;
        ret.accum_overflow = self.ctx.or(&[self.accum_overflow, other.accum_overflow]);
        ret
    }

    /// Exact (widening) subtraction. See [`IntCircuit::widen_add`].
    pub fn widen_sub(&self, other: &IntCircuit) -> IntCircuit {
        let width = std::cmp::max(self.width(), other.width()) + 1;
        let mut out = Vec::with_capacity(width);
        let mut carry = const_true();
        for i in 0..width {
            let (v0, v1) = (self.bit(i), self.ctx.not(other.bit(i)));
            out.push(sum3(&self.ctx, v0, v1, carry));
            carry = carry3(&self.ctx, v0, v1, carry);
        }
        let mut ret = IntCircuit::from_bits(out, &self.ctx);
        ret.tainted = self.tainted || other.tainted;
        ret.accum_overflow = self.ctx.or(&[self.accum_overflow, other.accum_overflow]);
        ret
    }

    /// Exact (widening) multiplication: full `w1 + w2` bits, no truncation.
    /// For §4 `prod = m1 * m2`.
    pub fn widen_mul(&self, other: &IntCircuit) -> IntCircuit {
        let ret_width = self.width() + other.width();
        let mut mult = vec![const_false(); ret_width];

        let i_bit_0 = self.bit(0);
        for (j, slot) in mult.iter_mut().enumerate() {
            *slot = self.ctx.and(&[i_bit_0, other.bit(j)]);
        }

        let last = ret_width - 1;
        for i in 1..last {
            let i_bit = self.bit(i);
            let mut carry = const_false();
            for j in 0..ret_width - i {
                let prod = self.ctx.and(&[i_bit, other.bit(j)]);
                let old = mult[i + j];
                mult[i + j] = sum3(&self.ctx, old, prod, carry);
                carry = carry3(&self.ctx, old, prod, carry);
            }
        }

        let i_bit = self.bit(last);
        let mut carry = const_true();
        for j in 0..ret_width - last {
            let prod = self.ctx.and(&[i_bit, other.bit(j)]);
            let negated = self.ctx.not(prod);
            let old = mult[last + j];
            mult[last + j] = sum3(&self.ctx, old, negated, carry);
            carry = carry3(&self.ctx, old, negated, carry);
        }

        let mut ret = IntCircuit::from_bits(mult, &self.ctx);
        ret.tainted = self.tainted || other.tainted;
        ret.accum_overflow = self.ctx.or(&[self.accum_overflow, other.accum_overflow]);
        ret
    }

    /// Widening shift-left by a constant: `width + amount` bits, zero-filled.
    /// For `m << d` alignment (§3) and `m1 << guard` (§5). The widened value
    /// keeps two's-complement semantics (old sign bit moves up; the product
    /// `value * 2^amount` always fits in `width + amount` bits).
    pub fn shl_const(&self, amount: u32) -> IntCircuit {
        let amount = amount as usize;
        let mut out = vec![const_false(); self.width() + amount];
        for (i, &b) in self.bits.iter().enumerate() {
            out[i + amount] = b;
        }
        let mut ret = IntCircuit::from_bits(out, &self.ctx);
        ret.tainted = self.tainted;
        ret.accum_overflow = self.accum_overflow;
        ret
    }

    /// Fixed-width logical shift-right by a constant (zero fill).
    pub fn srl_const(&self, amount: u32, width: u32) -> IntCircuit {
        let (amount, width) = (amount as usize, width as usize);
        let ext = self.extend_bits(width);
        let mut out = Vec::with_capacity(width);
        for j in 0..width {
            out.push(if j + amount < width {
                ext[j + amount]
            } else {
                const_false()
            });
        }
        let mut ret = IntCircuit::from_bits(out, &self.ctx);
        ret.tainted = self.tainted;
        ret.accum_overflow = self.accum_overflow;
        ret
    }

    /// Split into `(magnitude_bits, negative)` where `magnitude_bits` is the
    /// unsigned `|self|` (zero-extended semantics, same width) and
    /// `negative` is the sign bit. `INT_MIN` wraps (documented; mepk
    /// mantissae are `p`-bit normalized with headroom, so unreachable).
    pub fn abs_to_mag(&self) -> (Vec<BoolRef>, BoolRef) {
        let neg = *self.bits.last().unwrap_or(&const_false());
        let (negated, _) = twos_neg(&self.ctx, &self.bits);
        let mag: Vec<BoolRef> = self
            .bits
            .iter()
            .zip(negated.iter())
            .map(|(&b, &n)| self.ctx.ite(neg, n, b))
            .collect();
        (mag, neg)
    }

    /// Reapply a sign: `neg ? -mag : mag` over unsigned magnitude bits of
    /// width `w`, returned as a `w`-bit two's-complement circuit.
    pub fn apply_sign(mag: &[BoolRef], neg: BoolRef, ctx: &BoolCtx) -> IntCircuit {
        let (negated, _) = twos_neg(ctx, mag);
        let bits: Vec<BoolRef> = mag
            .iter()
            .zip(negated.iter())
            .map(|(&b, &n)| ctx.ite(neg, n, b))
            .collect();
        IntCircuit::from_bits(bits, ctx)
    }

    /// Unsigned strict less-than (`self`, `other` read zero-extended).
    pub fn ult(&self, other: &IntCircuit) -> BoolRef {
        ult_u(&self.ctx, &self.bits, &other.bits)
    }

    /// Unsigned `<=` (zero-extended).
    pub fn ule(&self, other: &IntCircuit) -> BoolRef {
        ule_u(&self.ctx, &self.bits, &other.bits)
    }

    /// Signed maximum via `lte` + `choice`. See [`IntCircuit::choice`].
    pub fn max_c(&self, other: &IntCircuit) -> IntCircuit {
        let cond = other.lte(self);
        self.choice(cond, other)
    }

    /// Signed minimum via `lte` + `choice`.
    pub fn min_c(&self, other: &IntCircuit) -> IntCircuit {
        let cond = self.lte(other);
        self.choice(cond, other)
    }

    /// Bit-length of `|self|` as an unsigned circuit (priority encoder over
    /// the magnitude). `0 -> 0`.
    pub fn bit_len_c(&self) -> IntCircuit {
        let (mag, _) = self.abs_to_mag();
        let bits = priority_len_bits(&self.ctx, &mag);
        let mut ret = IntCircuit::from_bits(bits, &self.ctx);
        ret.tainted = self.tainted;
        ret.accum_overflow = self.accum_overflow;
        ret
    }

    /// Round-to-nearest (ties-to-even) of `|self|` with a constant drop to
    /// `p` bits. Returns `(field, carry_out)` per [`round_mag_const_drop`].
    /// Requires `drop >= 1` and `drop + p <= width`.
    pub fn round_mag_const_drop_c(&self, drop: u32, p: u32) -> (Vec<BoolRef>, BoolRef) {
        let (mag, _) = self.abs_to_mag();
        round_mag_const_drop(&self.ctx, &mag, drop, p)
    }

    /// Guard-bit scaled division with round-to-nearest:
    /// `q0 = (|m1| << guard) / |m2|` (truncated, widened) plus the
    /// ties-to-even rounding decision `round_up = (2*rem > den) OR
    /// (2*rem == den AND q0 odd)`. Signs are returned separately as
    /// `neg = sign(m1) XOR sign(m2)` for the caller to reapply.
    ///
    /// Returns `(q_wide, round_up, neg, div_by_zero)`. `q_wide` has
    /// `max(w1 + guard, w2) + 2` bits; the caller rounds it to `p` bits.
    /// `div_by_zero` is always active (UNSAT), mirroring [`IntCircuit::div`].
    pub fn div_nearest_wide(
        &self,
        other: &IntCircuit,
        guard: u32,
    ) -> (IntCircuit, BoolRef, BoolRef, BoolRef) {
        let (mag1, neg1) = self.abs_to_mag();
        let (mag2, neg2) = other.abs_to_mag();
        let neg = xor2(&self.ctx, neg1, neg2);
        // Zero-extend magnitudes with an extra 0 bit so they stay
        // non-negative under sign-extending accessors.
        let mut a_bits = mag1;
        a_bits.push(const_false());
        let mut b_bits = mag2;
        b_bits.push(const_false());
        let a = IntCircuit::from_bits(a_bits, &self.ctx);
        let b = IntCircuit::from_bits(b_bits, &self.ctx);
        let num = a.shl_const(guard);
        let w = (std::cmp::max(num.width(), b.width()) + 1) as u32;
        let q_bits = num.non_restoring_division(&b, true, w);
        let r_bits = num.non_restoring_division(&b, false, w);
        // `2*rem ? den` unsigned over zero-extended vectors.
        let mut twice_bits = vec![const_false(); r_bits.len() + 1];
        for (i, &bit) in r_bits.iter().enumerate() {
            twice_bits[i + 1] = bit;
        }
        let mut den_bits = b.bits.clone();
        while den_bits.len() < twice_bits.len() {
            den_bits.push(const_false());
        }
        let gt = ult_u(&self.ctx, &den_bits, &twice_bits);
        let eq = eq_u(&self.ctx, &twice_bits, &den_bits);
        let q_odd = q_bits[0];
        let round_up = self
            .ctx
            .or(&[gt, self.ctx.and(&[eq, q_odd])]);
        // Division-by-zero is UNSAT regardless of taint.
        let mut or_inputs = Vec::with_capacity(b.width());
        for i in 0..b.width() {
            or_inputs.push(b.bit(i));
        }
        let div_by_zero = self.ctx.not(self.ctx.or(&or_inputs));
        let mut ret = IntCircuit::from_bits(q_bits, &self.ctx);
        ret.tainted = self.tainted || other.tainted;
        ret.accum_overflow = self.ctx.or(&[
            self.accum_overflow,
            other.accum_overflow,
            div_by_zero,
        ]);
        (ret, round_up, neg, div_by_zero)
    }
}

/// Signed-MSB weight of an int atom for the BITS cast: the top atom
/// (`top = W - 1`) weighs `-2^top`, every other non-negative atom below
/// 63 weighs `+2^v`. Out-of-range values contribute nothing.
/// Single source shared by `fol.rs` (circuit) and `eval.rs` (model).
pub fn bit_weight(v: i64, top: i64) -> Option<i64> {
    if v == top && top >= 0 && top < 63 {
        Some(-1i64 << top)
    } else if (0..63).contains(&v) {
        Some(1i64 << v)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::bit_weight;

    #[test]
    fn msb_weight_table() {
        // W = 4: top atom 3 weighs -8, rest are powers of two.
        assert_eq!(bit_weight(3, 3), Some(-8));
        assert_eq!(bit_weight(2, 3), Some(4));
        assert_eq!(bit_weight(0, 3), Some(1));
        // Non-top values are unaffected by `top`.
        assert_eq!(bit_weight(2, 5), Some(4));
        // Out of range contributes nothing.
        assert_eq!(bit_weight(63, 63), None);
        assert_eq!(bit_weight(-1, 3), None);
    }
}
