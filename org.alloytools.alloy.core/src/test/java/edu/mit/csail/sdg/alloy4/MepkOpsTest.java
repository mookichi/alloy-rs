package edu.mit.csail.sdg.alloy4;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.math.BigInteger;
import java.util.Random;

import org.junit.Test;

import edu.mit.csail.sdg.alloy4.MepkOps.DivisionUndefinedException;
import edu.mit.csail.sdg.alloy4.MepkOps.Mepk;
import edu.mit.csail.sdg.alloy4.MepkOps.Rounded;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

/**
 * Tests for the (m, e, p, k) error-tracking format: the {@link MepkOps} Java
 * oracle (concrete evaluation) and the {@code util/mepk} Alloy library
 * (symbolic, solver-backed constraints).
 */
public class MepkOpsTest {

    private static Mepk v(long m, int e, int p, int k) {
        return new Mepk(BigInteger.valueOf(m), e, p, k);
    }

    @Test
    public void combineK() {
        assertEquals(1, MepkOps.combineK(3, 5));
        assertEquals(1, MepkOps.combineK(5, 5));
        assertEquals(4, MepkOps.combineK(8, 5));
        // 2^A + 2^B <= 2^(B + combineK(A,B)) on a grid (exponent-level check).
        for (int a = -4; a <= 8; a++)
            for (int b = -4; b <= 8; b++) {
                int kk = MepkOps.combineK(a, b);
                assertTrue(kk >= 1);
                assertTrue(b + kk >= a);
            }
    }

    @Test
    public void roundToPrecisionExactWhenShort() {
        // bitLen <= p: zero-fill, no rounding error.
        Rounded r = MepkOps.roundToPrecision(BigInteger.valueOf(5), 0, 8);
        assertEquals(BigInteger.valueOf(5 << 5), r.m());
        assertEquals(2, r.e()); // MSB of 5 is 2^2; short mantissae are zero-filled
    }

    @Test
    public void roundToPrecisionNearest() {
        // 0b1111 (15) at lsb 0 -> p=3: keep 0b111, rest 0b1 = half -> ties-to-even -> 1000>>1? renormalize.
        Rounded r = MepkOps.roundToPrecision(BigInteger.valueOf(15), 0, 3);
        // 15 in 3 bits: candidates 14 (110+0?) — just check normalization + error bound.
        int bitLen = r.m().abs().bitLength();
        assertTrue(bitLen <= 3);
        // |raw*2^rawLsb - m'*2^lsb'| <= 2^(e'-p)
        BigInteger raw = BigInteger.valueOf(15);
        BigInteger centre = r.m().shiftLeft(r.e() - 3 + 1);
        BigInteger err = raw.subtract(centre).abs();
        assertTrue(err.compareTo(BigInteger.ONE.shiftLeft(r.e() - 3)) <= 0);
    }

    @Test
    public void roundToPrecisionFuzzErrorBound() {
        Random rnd = new Random(42);
        for (int i = 0; i < 2000; i++) {
            int p = 1 + rnd.nextInt(16);
            BigInteger raw = new BigInteger(40, rnd);
            if (rnd.nextBoolean())
                raw = raw.negate();
            int rawLsb = rnd.nextInt(11) - 5;
            Rounded r = MepkOps.roundToPrecision(raw, rawLsb, p);
            if (r.m().signum() != 0) {
                int bl = r.m().abs().bitLength();
                assertTrue("not normalized: " + r, bl == p);
            }
            // centre value = m' * 2^lsb'; orig = raw * 2^rawLsb
            BigInteger c = r.m().shiftLeft(r.e() - p + 1);
            BigInteger orig = raw.shiftLeft(rawLsb);
            // align: compare orig vs c directly (both absolute scale)
            BigInteger err = orig.subtract(c).abs();
            assertTrue("Lemma 1 violated: " + raw + " p=" + p,
                    err.compareTo(BigInteger.ONE.shiftLeft(r.e() - p)) <= 0);
        }
    }

    @Test
    public void addSubKRule() {
        Mepk x1 = v(100, 6, 8, 1);
        Mepk x2 = v(50, 5, 8, 2);
        Mepk s = MepkOps.addSub(x1, x2, 1);
        int ell = Math.min(x1.lsb(), x2.lsb());
        int a = ell + Math.max(x1.k() + (x1.lsb() - ell), x2.k() + (x2.lsb() - ell));
        int b = s.e() - s.p();
        assertEquals(Math.min(x1.p(), x2.p()), s.p());
        assertEquals(MepkOps.combineK(a, b), s.k());
        // centre must equal exact integer sum up to rounding <= 2^(e'-p).
        BigInteger exact = x1.m().shiftLeft(x1.lsb() - ell)
                .add(x2.m().shiftLeft(x2.lsb() - ell));
        BigInteger got = s.m().shiftLeft(s.e() - s.p() + 1 - ell);
        assertTrue(exact.subtract(got).abs()
                .compareTo(BigInteger.ONE.shiftLeft(s.e() - s.p())) <= 0);
    }

    @Test
    public void mulKRule() {
        Mepk x1 = v(127, 6, 8, 1);
        Mepk x2 = v(63, 5, 7, 2);
        Mepk r = MepkOps.mul(x1, x2);
        int t = Math.max(Math.max(x1.k() - x1.p() + 1, x2.k() - x2.p() + 1),
                (x1.k() + x2.k()) - (x1.p() + x2.p()));
        int c = x1.e() + x2.e() + t + 2;
        assertEquals(MepkOps.combineK(c, r.e() - r.p()), r.k());
    }

    @Test
    public void divNeedsGuard() {
        Mepk num = v(100, 6, 8, 1);
        Mepk badDen = v(50, 5, 4, 4); // k2 >= p2
        try {
            MepkOps.div(num, badDen);
            fail("expected DivisionUndefinedException");
        } catch (DivisionUndefinedException expected) {
        }
        Mepk okDen = v(50, 5, 8, 1);
        Mepk r = MepkOps.div(num, okDen);
        int t = Math.max(num.k() - num.p(), okDen.k() - okDen.p());
        int d = (num.e() - okDen.e()) + t + 3;
        assertEquals(MepkOps.combineK(d, r.e() - r.p()), r.k());
    }

    @Test
    public void tauAndRefine() {
        Mepk x = v(10, 3, 8, 7);
        assertEquals(8 - 7 - 0, x.tau(0));
        assertTrue(x.precisionLost(1)); // tau = 0 <= 0
        assertTrue(v(10, 3, 4, 4).precisionLost(0)); // k >= p
    }

    // ---- Alloy library side (symbolic) ----

    private static Module parseMepk() {
        // util modules resolve via the bundled models/ directory on classpath.
        Module world = CompUtil.parseEverything_fromString(edu.mit.csail.sdg.alloy4.A4Reporter.NOP,
                "open util/mepk as M\n" + "pred show { some x: M/Mepk | M/wellformed[x] }\n" + "run show for 3 but 4 Int\n");
        return world;
    }

    @Test
    public void mepkLibraryParses() {
        Module world = parseMepk();
        assertTrue(world.getAllReachableSigs().size() > 0);
    }

    @Test
    public void mepkAssertsHold() throws Exception {
        String model = "open util/mepk\n"
                + "check CombineKBounds for 3 but 5 Int\n"
                + "check DivGuardUnsat for 3 but 5 Int\n"
                + "check TauDetectsLoss for 3 but 5 Int\n";
        Module world = CompUtil.parseEverything_fromString(edu.mit.csail.sdg.alloy4.A4Reporter.NOP, model);
        A4Options options = new A4Options();
        // Exponent arithmetic is exact mathematics; the fixed-bitwidth Int
        // would otherwise wrap (e.g. plus[7,1] with 4-bit Int), so forbid
        // overflows like the "Forbid Overflows" analyzer option does.
        options.noOverflow = true;
        for (Command cmd : world.getAllCommands()) {
            A4Solution ans = TranslateAlloyToKodkod.execute_command(
                    edu.mit.csail.sdg.alloy4.A4Reporter.NOP,
                    world.getAllReachableSigs(), cmd, options);
            assertTrue("counterexample found for " + cmd.label + ": " + ans, !ans.satisfiable());
        }
    }
}
