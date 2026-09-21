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
