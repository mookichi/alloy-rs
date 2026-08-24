//! Integration tests for the asynchronous `alloy_worker_*` C ABI.

use libloading::Library;
use std::ffi::{c_char, c_int, c_void};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

type InitFn = unsafe extern "C" fn() -> *mut c_void;
type ReleaseFn = unsafe extern "C" fn(*mut c_void);
type AddFn = unsafe extern "C" fn(*mut c_void, *const c_int, usize);
type SolveFn = unsafe extern "C" fn(*mut c_void);
type CancelFn = unsafe extern "C" fn(*mut c_void);
type StatusFn = unsafe extern "C" fn(*mut c_void) -> c_int;
type ValFn = unsafe extern "C" fn(*mut c_void, c_int) -> c_int;
type BackendFn = unsafe extern "C" fn(*mut c_void) -> *const c_char;

struct Api {
    _lib: Library,
    init: InitFn,
    release: ReleaseFn,
    add: AddFn,
    solve: SolveFn,
    cancel: CancelFn,
    status: StatusFn,
    wait: StatusFn,
    val: ValFn,
    backend: BackendFn,
}

unsafe fn api() -> Api {
    let manifest = env!("CARGO_MANIFEST_DIR");
    let target = std::path::Path::new(manifest).join("../target/debug");
    #[cfg(target_os = "linux")]
    let name = "liballoy_ipasir.so";
    #[cfg(target_os = "macos")]
    let name = "liballoy_ipasir.dylib";
    #[cfg(target_os = "windows")]
    let name = "alloy_ipasir.dll";
    let lib = Library::new(target.join(name)).expect("failed to load cdylib");
    Api {
        init: *lib.get(b"alloy_worker_init").unwrap(),
        release: *lib.get(b"alloy_worker_release").unwrap(),
        add: *lib.get(b"alloy_worker_add").unwrap(),
        solve: *lib.get(b"alloy_worker_solve").unwrap(),
        cancel: *lib.get(b"alloy_worker_cancel").unwrap(),
        status: *lib.get(b"alloy_worker_status").unwrap(),
        wait: *lib.get(b"alloy_worker_wait").unwrap(),
        val: *lib.get(b"alloy_worker_val").unwrap(),
        backend: *lib.get(b"alloy_worker_backend").unwrap(),
        _lib: lib,
    }
}

fn clause(api: &Api, s: *mut c_void, lits: &[c_int]) {
    unsafe { (api.add)(s, lits.as_ptr(), lits.len()) };
}

#[test]
fn async_solve_and_snapshot_values() {
    unsafe {
        let api = api();
        let s = (api.init)();
        assert!(!s.is_null());

        let sig = std::ffi::CStr::from_ptr((api.backend)(s)).to_str().unwrap();
        assert!(!sig.is_empty());

        // (x1 ∨ x2) ∧ (¬x1 ∨ x3)
        clause(&api, s, &[1, 2]);
        clause(&api, s, &[-1, 3]);

        (api.solve)(s);
        let mut spins = 0;
        while (api.status)(s) == -1 {
            std::thread::sleep(Duration::from_micros(100));
            spins += 1;
            assert!(spins < 1_000_000, "solve never finished");
        }
        assert_eq!((api.status)(s), 10);
        assert_eq!((api.wait)(s), 10);

        // Model snapshot must satisfy both clauses.
        let v1 = (api.val)(s, 1);
        let v2 = (api.val)(s, 2);
        let v3 = (api.val)(s, 3);
        assert!(v1 == 1 || v2 == 2);
        assert!(v1 == -1 || v3 == 3);

        (api.release)(s);
    }
}

#[test]
fn empty_clause_reports_unsat() {
    unsafe {
        let api = api();
        let s = (api.init)();
        clause(&api, s, &[]);
        (api.solve)(s);
        assert_eq!((api.wait)(s), 20);
        (api.release)(s);
    }
}

#[test]
fn cancel_interrupts_running_solve() {
    // Pigeonhole principle: n pigeons into n-1 holes is UNSAT and hard
    // enough that a fresh solve cannot complete before we cancel it.
    let pigeons = 14usize;
    let holes = pigeons - 1;
    let var = |p: usize, h: usize| (p * holes + h + 1) as c_int;

    unsafe {
        let api = api();
        let s = (api.init)();

        for p in 0..pigeons {
            let mut all: Vec<c_int> = Vec::with_capacity(holes + 1);
            for h in 0..holes {
                all.push(var(p, h));
                for q in (p + 1)..pigeons {
                    clause(&api, s, &[-var(p, h), -var(q, h)]);
                }
            }
            clause(&api, s, &all);
        }

        (api.solve)(s);
        std::thread::sleep(Duration::from_millis(50));
        (api.cancel)(s);
        let r = (api.wait)(s);
        assert!(
            r == 0 || r == 20,
            "expected interrupted (0) or unfinished UNSAT (20), got {r}"
        );

        (api.release)(s);
    }
}

#[test]
fn workers_are_independent() {
    unsafe {
        let api = api();
        let a = (api.init)();
        let b = (api.init)();

        // Worker A: satisfiable.
        clause(&api, a, &[1]);
        // Worker B: unsatisfiable.
        clause(&api, b, &[2]);
        clause(&api, b, &[-2]);

        (api.solve)(a);
        (api.solve)(b);
        assert_eq!((api.wait)(a), 10);
        assert_eq!((api.wait)(b), 20);

        (api.release)(a);
        (api.release)(b);
    }
}

#[test]
fn release_joins_promptly_from_another_thread() {
    // Freeing while idle must join the worker thread without hanging.
    let deadline = Instant::now() + Duration::from_secs(10);
    let counter = Arc::new(AtomicUsize::new(0));
    let mut handles = Vec::new();
    for _ in 0..4 {
        let counter = Arc::clone(&counter);
        handles.push(std::thread::spawn(move || unsafe {
            let api = api();
            let s = (api.init)();
            clause(&api, s, &[1, 2]);
            (api.solve)(s);
            let r = (api.wait)(s);
            (api.release)(s);
            counter.fetch_add(r as usize, Ordering::SeqCst);
        }));
    }
    for h in handles {
        h.join().unwrap();
    }
    assert!(Instant::now() < deadline);
}
