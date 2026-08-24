//! alloy-ipasir: an [IPASIR](https://github.com/biotomas/ipasir)-compatible
//! incremental SAT solver interface backed by pluggable Rust solver
//! implementations (CaDiCaL bindings and Splr).
//!
//! Every session owns a dedicated *worker thread*; the backend never crosses
//! threads. Two C APIs are exported:
//!
//! - the synchronous IPASIR standard (`ipasir_*`) for maximum compatibility,
//!   which forwards to the worker internally, and
//! - an asynchronous worker API (`alloy_worker_*`) where solve runs on the
//!   worker and can be polled or cancelled from any host thread.
//!
//! Safety contracts of the exported FFI functions follow the standard IPASIR
//! conventions (see include/ipasir.h); null handles are tolerated.

#![allow(clippy::missing_safety_doc)]

mod backend;
#[cfg(feature = "cadical")]
mod cadical_backend;
#[cfg(feature = "jni")]
mod jni;
#[cfg(feature = "splr")]
mod splr_backend;
mod worker;

use std::ffi::{c_char, c_int, c_void};
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::thread;
use std::time::Duration;

use worker::Worker;

/// Return code for a satisfiable formula.
pub const IPASIR_SAT: c_int = 10;
/// Return code for an unsatisfiable formula.
pub const IPASIR_UNSAT: c_int = 20;
/// Return code when solving was interrupted or no result is available.
pub const IPASIR_INTERRUPTED: c_int = 0;

type TerminateFn = extern "C" fn(state: *mut c_void) -> c_int;

/// A solver session: one worker thread plus facade bookkeeping.
pub struct Session {
    worker: Worker,
    /// Literals of the clause currently being assembled via `ipasir_add`.
    pending_clause: Vec<c_int>,
    /// Assumptions accumulated since the last solve.
    assumptions: Vec<c_int>,
    terminate: Option<(TerminateFn, *mut c_void)>,
}

impl Session {
    pub fn new() -> Result<Self, String> {
        Ok(Session {
            worker: Worker::spawn()?,
            pending_clause: Vec::new(),
            assumptions: Vec::new(),
            terminate: None,
        })
    }

    pub fn backend_name(&self) -> &'static str {
        self.worker.name()
    }

    pub fn supports_assumptions(&self) -> bool {
        self.worker.supports_assumptions()
    }

    /// Add a whole clause at once.
    pub fn add_clause(&mut self, lits: &[c_int]) {
        self.worker.add_clause(lits.to_vec());
    }

    /// Add one literal to the pending clause; use `0` to terminate it.
    pub fn add_literal(&mut self, lit_or_zero: c_int) {
        if lit_or_zero == 0 {
            let clause = std::mem::take(&mut self.pending_clause);
            self.add_clause(&clause);
        } else {
            self.pending_clause.push(lit_or_zero);
        }
    }

    pub fn assume(&mut self, lit: c_int) {
        if lit != 0 && lit != i32::MIN {
            self.assumptions.push(lit);
        }
    }

    /// Blocking solve. Returns [`IPASIR_SAT`], [`IPASIR_UNSAT`] or
    /// [`IPASIR_INTERRUPTED`].
    ///
    /// If a terminate callback is registered it is polled while solving and
    /// triggers cancellation through the shared token.
    pub fn solve(&mut self) -> c_int {
        let assumptions = std::mem::take(&mut self.assumptions);
        if self.host_requests_stop() {
            return IPASIR_INTERRUPTED;
        }
        self.worker.start_solve(assumptions);
        if self.terminate.is_some() {
            // Poll the host callback so legacy IPASIR clients can interrupt
            // long-running solves with bounded latency.
            while self.worker.status() == worker::STATUS_RUNNING {
                if self.host_requests_stop() {
                    self.worker.cancel();
                    break;
                }
                thread::sleep(Duration::from_micros(200));
            }
        }
        self.worker.wait()
    }

    /// Value of `lit` after SAT: `lit` / `-lit`, or 0 when undefined.
    pub fn value(&self, lit: c_int) -> c_int {
        self.worker.value_of(lit)
    }

    /// Whether `lit` was a *failed* assumption in the last UNSAT solve, i.e.
    /// whether it belongs to the (not necessarily minimal) unsatisfiable core
    /// reported by the backend. `false` unless the last result was UNSAT.
    pub fn failed(&self, lit: c_int) -> bool {
        self.worker.failed_of(lit)
    }

    /// The failed assumptions of the last UNSAT solve as a literal list.
    pub fn failed_core(&self) -> Vec<c_int> {
        self.worker.failed_core()
    }

    pub fn set_terminate(&mut self, terminate: TerminateFn, state: *mut c_void) {
        self.terminate = Some((terminate, state));
    }

    pub fn clear_terminate(&mut self) {
        self.terminate = None;
    }

    fn host_requests_stop(&self) -> bool {
        match self.terminate {
            Some((f, state)) => f(state) != 0,
            None => false,
        }
    }
}

/// Run `f`, converting any Rust panic into a safe failure return so panics
/// never unwind across the C boundary.
fn guard<R: Default>(f: impl FnOnce() -> R) -> R {
    catch_unwind(AssertUnwindSafe(f)).unwrap_or_default()
}

// ---------------------------------------------------------------------------
// IPASIR C ABI (synchronous facade over the worker)
// ---------------------------------------------------------------------------

/// Returns the name and version of this solver implementation.
#[no_mangle]
pub extern "C" fn ipasir_signature() -> *const c_char {
    static SIGNATURE: std::sync::OnceLock<std::ffi::CString> = std::sync::OnceLock::new();
    let mut text = String::from("alloy-ipasir");
    #[cfg(feature = "cadical")]
    text.push_str(" cadical");
    #[cfg(feature = "splr")]
    text.push_str(" splr");
    SIGNATURE
        .get_or_init(|| std::ffi::CString::new(text).unwrap_or_default())
        .as_ptr()
}

/// Creates a new solver instance (and its worker thread).
///
/// The returned handle must be released with [`ipasir_release`].
#[no_mangle]
pub extern "C" fn ipasir_init() -> *mut Session {
    guard(|| match Session::new() {
        Ok(s) => Box::into_raw(Box::new(s)),
        Err(_) => std::ptr::null_mut(),
    })
}

/// Releases the solver instance. Passing a null pointer is a no-op.
#[no_mangle]
pub unsafe extern "C" fn ipasir_release(solver: *mut Session) {
    guard(|| {
        if !solver.is_null() {
            drop(Box::from_raw(solver));
        }
    })
}

/// Adds the given literal to the current clause; `0` terminates the clause.
#[no_mangle]
pub unsafe extern "C" fn ipasir_add(solver: *mut Session, lit_or_zero: c_int) {
    guard(|| {
        let Some(session) = solver.as_mut() else {
            return;
        };
        if lit_or_zero != i32::MIN {
            session.add_literal(lit_or_zero);
        }
    })
}

/// Adds the given literal as an assumption for the next `ipasir_solve`.
#[no_mangle]
pub unsafe extern "C" fn ipasir_assume(solver: *mut Session, lit: c_int) {
    guard(|| {
        let Some(session) = solver.as_mut() else {
            return;
        };
        session.assume(lit);
    })
}

/// Searches for a satisfying assignment (blocking).
///
/// Returns [`IPASIR_SAT`] (10), [`IPASIR_UNSAT`] (20) or
/// [`IPASIR_INTERRUPTED`] (0).
#[no_mangle]
pub unsafe extern "C" fn ipasir_solve(solver: *mut Session) -> c_int {
    guard(|| match solver.as_mut() {
        Some(session) => session.solve(),
        None => IPASIR_INTERRUPTED,
    })
}

/// Returns the value of the literal in the last SAT model: `lit` or `-lit`.
#[no_mangle]
pub unsafe extern "C" fn ipasir_val(solver: *mut Session, lit: c_int) -> c_int {
    guard(|| match solver.as_ref() {
        Some(session) if session.last_result_was_sat() => session.value(lit),
        _ => 0,
    })
}

/// Returns 1 if the assumption literal was *failed* in the last UNSAT solve
/// (it belongs to the reported unsatisfiable core), 0 otherwise.
#[no_mangle]
pub unsafe extern "C" fn ipasir_failed(solver: *mut Session, lit: c_int) -> c_int {
    guard(|| match solver.as_ref() {
        Some(session) if session.last_result_was_unsat() && session.failed(lit) => 1,
        _ => 0,
    })
}

/// Registers a termination callback polled during `ipasir_solve`.
#[no_mangle]
pub unsafe extern "C" fn ipasir_set_terminate(
    solver: *mut Session,
    state: *mut c_void,
    terminate: Option<extern "C" fn(state: *mut c_void) -> c_int>,
) {
    guard(|| {
        let Some(session) = solver.as_mut() else {
            return;
        };
        match terminate {
            Some(f) => session.set_terminate(f, state),
            None => session.clear_terminate(),
        }
    })
}

/// Registers a learned-clause callback. Currently ignored (optional part of
/// the IPASIR standard); provided for ABI completeness.
#[no_mangle]
pub unsafe extern "C" fn ipasir_set_learn(
    _solver: *mut Session,
    _state: *mut c_void,
    _max_length: c_int,
    _learn: Option<extern "C" fn(state: *mut c_void, clause: *const c_int)>,
) {
    // Optional interface; not implemented yet.
}

impl Session {
    fn last_result_was_sat(&self) -> bool {
        self.worker.status() == IPASIR_SAT
    }

    fn last_result_was_unsat(&self) -> bool {
        self.worker.status() == IPASIR_UNSAT
    }
}

// ---------------------------------------------------------------------------
// alloy_worker_* C ABI (asynchronous)
// ---------------------------------------------------------------------------

/// Spawns a new worker. Returns null if no backend is available.
#[no_mangle]
pub extern "C" fn alloy_worker_init() -> *mut Worker {
    guard(|| match Worker::spawn() {
        Ok(w) => Box::into_raw(Box::new(w)),
        Err(_) => std::ptr::null_mut(),
    })
}

/// Releases the worker and joins its thread. Null is a no-op.
#[no_mangle]
pub unsafe extern "C" fn alloy_worker_release(worker: *mut Worker) {
    guard(|| {
        if !worker.is_null() {
            drop(Box::from_raw(worker));
        }
    })
}

/// Queues one clause (literals without terminator; length may be 0 for the
/// empty clause). Asynchronous and order-preserving with respect to solves.
#[no_mangle]
pub unsafe extern "C" fn alloy_worker_add(worker: *mut Worker, lits: *const c_int, len: usize) {
    guard(|| {
        let Some(worker) = worker.as_ref() else {
            return;
        };
        if len > 0 && lits.is_null() {
            return;
        }
        let slice = std::slice::from_raw_parts(lits, len);
        // Filter the undefined literal defensively.
        let lits: Vec<c_int> = slice.iter().copied().filter(|&l| l != i32::MIN).collect();
        worker.add_clause(lits);
    })
}

/// Starts an asynchronous solve. Use [`alloy_worker_status`] /
/// [`alloy_worker_wait`] to observe the result.
#[no_mangle]
pub unsafe extern "C" fn alloy_worker_solve(worker: *mut Worker) {
    guard(|| {
        let Some(worker) = worker.as_ref() else {
            return;
        };
        let assumptions = worker.take_pending_assumptions();
        worker.start_solve(assumptions);
    })
}

/// Adds the literal as an assumption for the next [`alloy_worker_solve`].
#[no_mangle]
pub unsafe extern "C" fn alloy_worker_assume(worker: *mut Worker, lit: c_int) {
    guard(|| {
        if let Some(worker) = worker.as_ref() {
            worker.assume(lit);
        }
    })
}

/// Requests interruption of the running solve from any thread.
#[no_mangle]
pub unsafe extern "C" fn alloy_worker_cancel(worker: *mut Worker) {
    guard(|| {
        let Some(worker) = worker.as_ref() else {
            return;
        };
        worker.cancel();
    })
}

/// Non-blocking status: [`STATUS_RUNNING_C`] (-1) while running, otherwise
/// 10 / 20 / 0.
#[no_mangle]
pub unsafe extern "C" fn alloy_worker_status(worker: *mut Worker) -> c_int {
    guard(|| match worker.as_ref() {
        Some(worker) => worker.status(),
        None => 0,
    })
}

/// Blocks until the running solve finishes; returns its status.
#[no_mangle]
pub unsafe extern "C" fn alloy_worker_wait(worker: *mut Worker) -> c_int {
    guard(|| match worker.as_ref() {
        Some(worker) => worker.wait(),
        None => 0,
    })
}

/// Value of `lit` in the last SAT model (`lit` / `-lit`; 0 when undefined).
#[no_mangle]
pub unsafe extern "C" fn alloy_worker_val(worker: *mut Worker, lit: c_int) -> c_int {
    guard(|| match worker.as_ref() {
        Some(worker) => worker.value_of(lit),
        None => 0,
    })
}

/// 1 if `lit` was a failed assumption in the last UNSAT solve, else 0.
#[no_mangle]
pub unsafe extern "C" fn alloy_worker_failed(worker: *mut Worker, lit: c_int) -> c_int {
    guard(|| match worker.as_ref() {
        Some(worker) if worker.failed_of(lit) => 1,
        _ => 0,
    })
}

/// Status value meaning "solve still running".
pub const STATUS_RUNNING_C: c_int = -1;

/// Returns a short description of the active backend (stable `'static'`
/// pointer for the lifetime of the process).
#[no_mangle]
pub unsafe extern "C" fn alloy_worker_backend(worker: *mut Worker) -> *const c_char {
    fn cstr(name: &'static str) -> *const c_char {
        static CACHE: std::sync::Mutex<Vec<(&'static str, std::ffi::CString)>> =
            std::sync::Mutex::new(Vec::new());
        let mut cache = CACHE.lock().unwrap();
        if let Some((_, s)) = cache.iter().find(|(n, _)| *n == name) {
            return s.as_ptr();
        }
        let entry = (name, std::ffi::CString::new(name).unwrap_or_default());
        let ptr = entry.1.as_ptr();
        cache.push(entry);
        ptr
    }
    guard(|| match worker.as_ref() {
        Some(worker) => cstr(worker.name()),
        None => cstr("none"),
    })
}
