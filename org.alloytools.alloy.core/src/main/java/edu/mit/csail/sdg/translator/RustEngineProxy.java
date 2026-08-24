package edu.mit.csail.sdg.translator;

import java.io.File;
import java.util.Optional;

import kodkod.solvers.api.NativeCode;

/**
 * JNI bridge to liballoy_engine (--engine rust, alloy-sat-rs Iter 10).
 *
 * The native library is located through {@link NativeCode} (system property
 * "-Dalloy.native.lib.alloy_engine=&lt;path&gt;" takes priority, then
 * java.library.path / app.dir / bundled resources).
 */
public final class RustEngineProxy {

    /** Result of the last load attempt, null while not yet attempted. */
    private static String  loadError;
    private static boolean loaded;

    private RustEngineProxy() {}

    /**
     * Loads liballoy_engine once; subsequent calls are cheap.
     *
     * @return true if the library is loaded and the native method is usable
     */
    public static synchronized boolean isAvailable() {
        if (loaded || loadError != null)
            return loaded;
        Optional<File> lib = NativeCode.platform.getLibrary("alloy_engine");
        if (!lib.isPresent()) {
            loadError = "liballoy_engine not found; build it with "
                    + "'cargo build --release -p alloy-engine-rs --features jni' and pass "
                    + "-Dalloy.native.lib.alloy_engine=<path-to-liballoy_engine.so>";
            return false;
        }
        try {
            System.load(lib.get().getAbsolutePath());
            loaded = true;
        } catch (UnsatisfiedLinkError e) {
            loadError = "failed to load " + lib.get() + ": " + e.getMessage();
        }
        return loaded;
    }

    /** Reason this proxy is unavailable, or null if available/not yet tried. */
    public static synchronized String unavailableReason() {
        return loadError;
    }

    private static native byte[] solveNative(byte[] problem);

    /**
     * Solves one ARE1 problem buffer; returns the raw answer buffer.
     *
     * @throws UnsatisfiedLinkError if the library could not be loaded
     */
    public static byte[] solve(byte[] problem) {
        if (!isAvailable())
            throw new UnsatisfiedLinkError(loadError);
        return solveNative(problem);
    }
}
