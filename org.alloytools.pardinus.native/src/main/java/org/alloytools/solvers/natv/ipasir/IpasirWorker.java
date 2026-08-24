package org.alloytools.solvers.natv.ipasir;

import java.util.concurrent.atomic.AtomicBoolean;

import kodkod.engine.satlab.SATSolver;

/**
 * SAT solver backed by the Rust <em>alloy-ipasir</em> library (CaDiCaL or
 * Splr behind an IPASIR-style worker thread).
 *
 * In addition to the synchronous {@link SATSolver} contract, this solver
 * exposes a small asynchronous API: {@link #solveAsync()} submits a solve on
 * the native worker thread, {@link #status()} polls it,
 * {@link #waitSolution()} blocks for the result and {@link #cancel()}
 * requests interruption from any thread.
 */
public final class IpasirWorker implements SATSolver {

    /** Async status: solve still running. */
    public static final int STATUS_RUNNING = -1;
    /** Async status: satisfiable. */
    public static final int STATUS_SAT     = 10;
    /** Async status: unsatisfiable. */
    public static final int STATUS_UNSAT   = 20;
    /** Async status: interrupted or unknown. */
    public static final int STATUS_UNKNOWN = 0;

    private final long             peer;
    private Boolean                sat;
    private int                    clauses, vars;
    private final AtomicBoolean    freed = new AtomicBoolean();

    /**
     * Constructs a solver. The native library must have been loaded first
     * (done automatically by {@link IpasirRef#createSolver()}).
     */
    public IpasirWorker() {
        IpasirRef.ensureLoaded();
        this.peer = make();
        if (peer == 0L)
            throw new RuntimeException("alloy-ipasir: failed to spawn solver worker");
    }

    // ---------------------------------------------------------------------
    // asynchronous API
    // ---------------------------------------------------------------------

    /**
     * Submit a non-blocking solve on the native worker thread.
     */
    public void solveAsync() {
        valid();
        sat = null;
        solveAsync0(peer);
    }

    /**
     * Poll the running/finished async solve.
     *
     * @return {@link #STATUS_RUNNING}, {@link #STATUS_SAT},
     *         {@link #STATUS_UNSAT} or {@link #STATUS_UNKNOWN}
     */
    public int status() {
        valid();
        return status0(peer);
    }

    /**
     * Block until the submitted solve finishes.
     *
     * @return {@link #STATUS_SAT}, {@link #STATUS_UNSAT} or
     *         {@link #STATUS_UNKNOWN}
     */
    public int waitSolution() {
        valid();
        return waitSolution0(peer);
    }

    /**
     * Request interruption of a running solve from any thread; the result
     * then becomes {@link #STATUS_UNKNOWN}.
     */
    public void cancel() {
        valid();
        cancel0(peer);
    }

    /**
     * Value of a literal in the last SAT model, without requiring the
     * synchronous {@link #solve()} path (usable after
     * {@link #waitSolution()}).
     *
     * @param lit a non-zero literal in DIMACS notation
     * @return true if the literal is satisfied by the model
     */
    public boolean literalValue(int lit) {
        valid();
        if (lit == 0 || status0(peer) != STATUS_SAT)
            return false;
        return valueOf(peer, lit);
    }

    // ---------------------------------------------------------------------
    // SATSolver
    // ---------------------------------------------------------------------

    @Override
    public int numberOfVariables() {
        valid();
        return vars;
    }

    @Override
    public int numberOfClauses() {
        valid();
        return clauses;
    }

    @Override
    public void addVariables(int numVars) {
        valid();
        if (numVars < 0)
            throw new IllegalArgumentException("vars < 0: " + numVars);
        vars += numVars;
        addVariables(peer, numVars);
    }

    @Override
    public boolean addClause(int[] lits) {
        valid();
        if (addClause(peer, lits)) {
            clauses++;
            return true;
        }
        return false;
    }

    @Override
    public boolean solve() {
        valid();
        if (Boolean.FALSE.equals(sat))
            return false;
        sat = solve(peer);
        return sat;
    }

    @Override
    public boolean valueOf(int variable) {
        valid();
        if (!Boolean.TRUE.equals(sat))
            throw new IllegalStateException("no satisfiable model available");
        return valueOf(peer, variable);
    }

    @Override
    public void free() {
        if (freed.compareAndSet(false, true))
            free(peer);
    }

    private void valid() {
        if (freed.get())
            throw new IllegalStateException("this solver is already freed");
    }

    @Override
    public String toString() {
        return "ipasir(worker)";
    }

    // ---------------------------------------------------------------------
    // native bindings
    // ---------------------------------------------------------------------

    private static native long make();

    private native void free(long peer);

    private native void addVariables(long peer, int n);

    private native boolean addClause(long peer, int[] lits);

    private native boolean solve(long peer);

    private native boolean valueOf(long peer, int lit);

    private native void solveAsync0(long peer);

    private native int status0(long peer);

    private native int waitSolution0(long peer);

    private native void cancel0(long peer);
}
