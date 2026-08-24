package org.alloytools.solvers.natv.ipasir;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertThat;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

import org.junit.Assume;
import org.junit.BeforeClass;
import org.junit.Test;

import kodkod.engine.satlab.SATFactory;

/**
 * End-to-end tests over JNI for the Rust worker solver.
 */
public class IpasirWorkerTest {

    /**
     * Unit tests run against {@code target/classes}, which does not embed
     * the {@code native/} resources; point NativeCode at the repository
     * copy of the shared library instead. Skipped when it is not built.
     */
    @BeforeClass
    public static void locateNativeLibrary() {
        Path local = Paths.get("native/linux/amd64/liballoy_ipasir.so").toAbsolutePath();
        Path fromRoot = Paths.get("org.alloytools.pardinus.native/native/linux/amd64/liballoy_ipasir.so")
                             .toAbsolutePath();
        Path lib = Files.isRegularFile(local) ? local : fromRoot;
        Assume.assumeTrue("native library not built: " + lib, Files.isRegularFile(lib));
        System.setProperty("alloy.native.lib.alloy_ipasir", lib.toString());
    }

    private static SATFactory factory() {
        return new IpasirRef();
    }

    @Test
    public void factoryIsPresentAndIdMatches() {
        assertThat(factory().id(), org.hamcrest.Matchers.is("ipasir"));
        assertTrue(factory().isPresent());
    }

    private static IpasirWorker satInstance() {
        IpasirWorker s = new IpasirWorker();
        // (x1 v x2) ^ (!x1 v x3)
        s.addClause(new int[] {
                             1, 2
        });
        s.addClause(new int[] {
                             -1, 3
        });
        return s;
    }

    @Test
    public void syncSolveSatWithModel() {
        IpasirWorker s = satInstance();
        try {
            assertThat(s.numberOfClauses(), org.hamcrest.Matchers.is(2));
            assertTrue(s.solve());
            boolean x1 = s.valueOf(1), x2 = s.valueOf(2), x3 = s.valueOf(3);
            assertTrue(x1 || x2);
            assertTrue( !x1 || x3);
        } finally {
            s.free();
        }
    }

    @Test
    public void syncSolveUnsatAndIncremental() {
        IpasirWorker s = new IpasirWorker();
        try {
            s.addClause(new int[] {
                                 5
            });
            s.addClause(new int[] {
                                 -5
            });
            assertFalse(s.solve());

            // fresh instance stays incremental: clauses turn SAT into UNSAT
            IpasirWorker t = new IpasirWorker();
            try {
                t.addClause(new int[] {
                                     1, 2
                });
                assertTrue(t.solve());
                t.addClause(new int[] {
                                     -1
                });
                assertTrue(t.solve());
                t.addClause(new int[] {
                                     -2
                });
                assertFalse(t.solve());
            } finally {
                t.free();
            }
        } finally {
            s.free();
        }
    }

    @Test
    public void asyncPollWaitAndLiteralValue() {
        IpasirWorker s = satInstance();
        try {
            s.solveAsync();
            long deadline = System.nanoTime() + 10_000_000_000L; // 10s
            while (s.status() == IpasirWorker.STATUS_RUNNING) {
                if (System.nanoTime() > deadline)
                    fail("async solve did not finish within 10s");
                Thread.onSpinWait();
            }
            assertThat(s.waitSolution(), org.hamcrest.Matchers.is(IpasirWorker.STATUS_SAT));
            assertTrue(s.literalValue(1) || s.literalValue(2));
            assertTrue( !s.literalValue(1) || s.literalValue(3));
        } finally {
            s.free();
        }
    }

    @Test
    public void cancelInterruptsHardUnsatProblem() throws Exception {
        // pigeonhole PHP(n, n-1): unsatisfiable and slow enough to cancel
        int pigeons = 14, holes = pigeons - 1;
        int[][] clauses = php(pigeons, holes);

        IpasirWorker s = new IpasirWorker();
        try {
            for (int[] c : clauses)
                s.addClause(c);

            s.solveAsync();
            Thread.sleep(50); // let the search start
            s.cancel();

            long deadline = System.nanoTime() + 10_000_000_000L; // 10s
            while (s.status() == IpasirWorker.STATUS_RUNNING) {
                if (System.nanoTime() > deadline)
                    fail("cancel did not take effect within 10s");
                Thread.onSpinWait();
            }
            int result = s.waitSolution();
            assertTrue("expected interrupted (" + IpasirWorker.STATUS_UNKNOWN + ") or unsat ("
                       + IpasirWorker.STATUS_UNSAT + ") but got " + result,
                       result == IpasirWorker.STATUS_UNKNOWN || result == IpasirWorker.STATUS_UNSAT);
            assertFalse(s.literalValue(1));
        } finally {
            s.free();
        }
    }

    @Test
    public void freedSolverRejectsUse() {
        IpasirWorker s = new IpasirWorker();
        s.free();
        try {
            s.solve();
            fail("solve after free should throw IllegalStateException");
        } catch (IllegalStateException expected) {
            // expected
        }
        s.free(); // double free is a no-op
    }

    /** Generate pigeonhole principle clauses: n pigeons, n-1 holes. */
    private static int[][] php(int pigeons, int holes) {
        int count = pigeons + pigeons * holes * (pigeons - 1) / 2;
        int[][] out = new int[count][];
        int k = 0;
        for (int p = 0; p < pigeons; p++) {
            int[] all = new int[holes];
            for (int h = 0; h < holes; h++) {
                all[h] = phpVar(holes, p, h);
                for (int q = p + 1; q < pigeons; q++) {
                    out[k++] = new int[] {
                                         -phpVar(holes, p, h), -phpVar(holes, q, h)
                    };
                }
            }
            out[k++] = all;
        }
        assert k == count;
        return out;
    }

    /** DIMACS variable for pigeon {@code p} in hole {@code h}. */
    private static int phpVar(int holes, int p, int h) {
        return p * holes + h + 1;
    }
}
