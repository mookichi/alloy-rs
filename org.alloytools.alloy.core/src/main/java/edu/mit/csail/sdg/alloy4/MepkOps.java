package edu.mit.csail.sdg.alloy4;

import java.math.BigInteger;

/**
 * Reference (oracle) implementation of the (m, e, p, k) error-tracking
 * floating-point format from mepk_formal.md.
 *
 * <p>
 * Each value carries centre {@code c = m * 2^lsb} with {@code lsb = e - p + 1}
 * and guaranteed radius {@code R = 2^(e - p + k)}, i.e. soundness
 * {@code |x - c| <= R}. All k-propagation rules are derived from the triangle
 * inequality plus Lemma 1 (rounding) and Lemma 2 (n-term exponent packing)
 * only.
 *
 * <p>
 * This class is the concrete-evaluator counterpart to
 * {@code models/util/mepk.als}, which states the same rules as solver-backed
 * Alloy constraints over exponents. The Alloy side pins the sound error
 * exponent {@code k'}; this class additionally computes the exact rounded
 * centre ({@link #roundToPrecision}) via round-to-nearest on BigIntegers.
 */
public final class MepkOps {

    private MepkOps() {}

    /** Immutable (m, e, p, k) tuple. Invariant: p &gt; 0. */
    public record Mepk(BigInteger m, int e, int p, int k) {
        public Mepk {
            if (p <= 0)
                throw new IllegalArgumentException("p must be > 0");
            java.util.Objects.requireNonNull(m);
        }

        /** Weight of the least significant bit: {@code lsb = e - p + 1}. */
        public int lsb() {
            return e - p + 1;
        }

        /** Exponent of the error radius: {@code R = 2^(e - p + k)}. */
        public int radiusExp() {
            return e - p + k;
        }

        /** CEGAR budget: {@code tau = p - k - g} (theory §7). */
        public int tau(int g) {
            return p - k - g;
        }

        public boolean divGuard() {
            return k < p;
        }

        public boolean precisionLost(int g) {
            return k >= p || tau(g) <= 0;
        }
    }

    /** Result of {@link #roundToPrecision}: normalized mantissa + MSB exponent. */
    public record Rounded(BigInteger m, int e) {}

    /** {@code combine_k(A, B) = max(A - B, 0) + 1} (theory §2). */
    public static int combineK(int a, int b) {
        return Math.max(a - b, 0) + 1;
    }

    /**
     * Round-to-nearest integer {@code raw} at scale {@code rawLsb} to a
     * {@code p}-bit normalized mantissa. Rounding error is at most
     * {@code 2^(e' - p)} (Lemma 1). Zero maps to {@code (0, rawLsb + p - 1)}.
     */
    public static Rounded roundToPrecision(BigInteger raw, int rawLsb, int p) {
        if (p <= 0)
            throw new IllegalArgumentException("p must be > 0");
        if (raw.signum() == 0)
            return new Rounded(BigInteger.ZERO, rawLsb + p - 1);
        boolean neg = raw.signum() < 0;
        BigInteger mag = raw.abs();
        int bitLen = mag.bitLength();
        int e = rawLsb + bitLen - 1;
        int lsbNew;
        BigInteger mNew;
        if (bitLen <= p) {
            // Zero-fill only, no rounding error.
            mNew = mag.shiftLeft(p - bitLen);
            lsbNew = e - p + 1;
        } else {
            int drop = bitLen - p;
            BigInteger kept = mag.shiftRight(drop);
            BigInteger rest = mag.subtract(kept.shiftLeft(drop));
            BigInteger half = BigInteger.ONE.shiftLeft(drop - 1);
            int cmp = rest.compareTo(half);
            if (cmp > 0 || (cmp == 0 && kept.testBit(0))) {
                kept = kept.add(BigInteger.ONE);
                if (kept.bitLength() > p) {
                    // Carry out: renormalize (e.g. 1111 + 1 -> 10000).
                    kept = kept.shiftRight(1);
                    e += 1;
                }
            }
            mNew = neg ? kept.negate() : kept;
            lsbNew = e - p + 1;
            return new Rounded(mNew, e);
        }
        if (neg)
            mNew = mNew.negate();
        return new Rounded(mNew, e);
    }

    /** Addition / subtraction (§3). {@code sign} is +1 (add) or -1 (sub). */
    public static Mepk addSub(Mepk x1, Mepk x2, int sign) {
        if (sign != 1 && sign != -1)
            throw new IllegalArgumentException("sign must be +1 or -1");
        int ell = Math.min(x1.lsb(), x2.lsb());
        int d1 = x1.lsb() - ell;
        int d2 = x2.lsb() - ell;
        BigInteger total = x1.m().shiftLeft(d1)
                .add(x2.m().multiply(BigInteger.valueOf(sign)).shiftLeft(d2));
        int pNew = Math.min(x1.p(), x2.p());
        Rounded r = roundToPrecision(total, ell, pNew);
        int a = ell + Math.max(x1.k() + d1, x2.k() + d2);
        int b = r.e() - pNew;
        return new Mepk(r.m(), r.e(), pNew, combineK(a, b));
    }

    /** Multiplication (§4). */
    public static Mepk mul(Mepk x1, Mepk x2) {
        int pNew = Math.min(x1.p(), x2.p());
        BigInteger prod = x1.m().multiply(x2.m());
        Rounded r = roundToPrecision(prod, x1.lsb() + x2.lsb(), pNew);
        int t1 = x1.k() - x1.p() + 1;
        int t2 = x2.k() - x2.p() + 1;
        int t3 = (x1.k() + x2.k()) - (x1.p() + x2.p());
        int c = x1.e() + x2.e() + Math.max(Math.max(t1, t2), t3) + 2;
        int b = r.e() - pNew;
        return new Mepk(r.m(), r.e(), pNew, combineK(c, b));
    }

    /**
     * Division (§5). Requires {@code k2 < p2}; otherwise throws
     * {@link DivisionUndefinedException} since no finite bound can absorb a
     * denominator interval that may span zero. The Alloy library instead maps
     * this to UNSAT via {@code divGuard}.
     */
    public static Mepk div(Mepk x1, Mepk x2) {
        if (!x2.divGuard())
            throw new DivisionUndefinedException("denominator has k2 >= p2");
        int pNew = Math.min(x1.p(), x2.p());
        int guard = pNew + 4;
        // Scaled integer division with round-to-nearest on the guard bits.
        BigInteger num = x1.m().shiftLeft(guard);
        BigInteger[] qr = num.divideAndRemainder(x2.m().abs());
        BigInteger q = qr[0];
        BigInteger rem = qr[1];
        BigInteger twice = rem.shiftLeft(1);
        int cmp = twice.compareTo(x2.m().abs());
        if (cmp > 0 || (cmp == 0 && q.testBit(0)))
            q = q.add(BigInteger.ONE);
        if (x1.m().signum() * x2.m().signum() < 0)
            q = q.negate();
        int qLsb = x1.lsb() - x2.lsb() - guard;
        Rounded r = roundToPrecision(q, qLsb, pNew);
        int t = Math.max(x1.k() - x1.p(), x2.k() - x2.p());
        int d = (x1.e() - x2.e()) + t + 3;
        int b = r.e() - pNew;
        return new Mepk(r.m(), r.e(), pNew, combineK(d, b));
    }

    /** Thrown when the §5 division precondition {@code k2 < p2} is violated. */
    public static final class DivisionUndefinedException extends RuntimeException {
        public DivisionUndefinedException(String msg) {
            super(msg);
        }
    }
}
