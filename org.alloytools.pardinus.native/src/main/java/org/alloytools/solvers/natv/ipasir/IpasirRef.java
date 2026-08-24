package org.alloytools.solvers.natv.ipasir;

import java.io.File;
import java.util.Optional;

import aQute.bnd.annotation.spi.ServiceProvider;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.satlab.SATSolver;
import kodkod.solvers.api.NativeCode;

/**
 * SATFactory for the Rust <em>alloy-ipasir</em> solver: an incremental
 * IPASIR-style worker (CaDiCaL by default, Splr as pure-Rust fallback) with
 * an asynchronous solve/cancel API.
 */
@ServiceProvider(SATFactory.class)
public class IpasirRef extends SATFactory {

    private static final long serialVersionUID = 1L;

    private static final String[] LIBRARIES = {
                                              "alloy_ipasir"
    };

    private static volatile boolean loaded = false;

    /**
     * Load the native library exactly once per VM. Loading twice throws
     * UnsatisfiedLinkError, so a repeat attempt is treated as success.
     */
    static synchronized void ensureLoaded() {
        if (loaded)
            return;
        RuntimeException failure = null;
        for (String library : LIBRARIES) {
            Optional<File> libFile = NativeCode.platform.getLibrary(library);
            if (!libFile.isPresent()) {
                throw new RuntimeException("alloy-ipasir native library not found: " + library);
            }
            try {
                System.load(libFile.get().getAbsolutePath());
            } catch (UnsatisfiedLinkError e) {
                // Already loaded in this classloader: fine.
                String msg = String.valueOf(e.getMessage());
                if (!msg.contains("already loaded")) {
                    failure = new RuntimeException(msg, e);
                    break;
                }
            }
        }
        if (failure != null)
            throw failure;
        loaded = true;
    }

    @Override
    public String id() {
        return "ipasir";
    }

    @Override
    public String[] getLibraries() {
        return LIBRARIES.clone();
    }

    @Override
    public boolean incremental() {
        return true;
    }

    @Override
    public String type() {
        return "jni";
    }

    @Override
    public Optional<String> getDescription() {
        return Optional.of(
                "alloy-ipasir is a Rust worker-thread SAT backend implementing the IPASIR "
                        + "incremental interface. It runs CaDiCaL by default (ALLOY_SAT_BACKEND=splr "
                        + "selects the pure-Rust Splr). Solves execute on a dedicated native thread and "
                        + "can be polled or cancelled asynchronously via IpasirWorker.");
    }

    @Override
    public boolean isPresent() {
        try {
            ensureLoaded();
        } catch (RuntimeException e) {
            return false;
        }
        return super.isPresent();
    }

    @Override
    public SATSolver createSolver() {
        ensureLoaded();
        return new IpasirWorker();
    }
}
