//! Integration test that loads the built cdylib via `dlopen`/`LoadLibrary`
//! and exercises the real exported IPASIR symbols, validating the C ABI
//! contract that foreign consumers (e.g. the Java JNI wrapper) rely on.

use libloading::Library;
use std::ffi::{c_char, c_int, c_void};

type SignatureFn = unsafe extern "C" fn() -> *const c_char;
type InitFn = unsafe extern "C" fn() -> *mut c_void;
type ReleaseFn = unsafe extern "C" fn(*mut c_void);
type AddFn = unsafe extern "C" fn(*mut c_void, c_int);
type SolveFn = unsafe extern "C" fn(*mut c_void) -> c_int;
type ValFn = unsafe extern "C" fn(*mut c_void, c_int) -> c_int;
type AssumeFn = unsafe extern "C" fn(*mut c_void, c_int);
type FailedFn = unsafe extern "C" fn(*mut c_void, c_int) -> c_int;
type SetTerminateFn = unsafe extern "C" fn(
    *mut c_void,
    *mut c_void,
    Option<unsafe extern "C" fn(*mut c_void) -> c_int>,
);

fn library_path() -> String {
    let manifest = env!("CARGO_MANIFEST_DIR");
    let target = std::path::Path::new(manifest).join("../target/debug");
    #[cfg(target_os = "linux")]
    let name = "liballoy_ipasir.so";
    #[cfg(target_os = "macos")]
    let name = "liballoy_ipasir.dylib";
    #[cfg(target_os = "windows")]
    let name = "alloy_ipasir.dll";
    target.join(name).to_string_lossy().into_owned()
}

struct Api {
    _lib: Library, // keep loaded
    signature: SignatureFn,
    init: InitFn,
    release: ReleaseFn,
    add: AddFn,
    assume: AssumeFn,
    solve: SolveFn,
    val: ValFn,
    failed: FailedFn,
    set_terminate: SetTerminateFn,
}

unsafe fn api() -> Api {
    let lib = Library::new(library_path()).expect("failed to load cdylib");
    let api = Api {
        signature: *lib.get(b"ipasir_signature").unwrap(),
        init: *lib.get(b"ipasir_init").unwrap(),
        release: *lib.get(b"ipasir_release").unwrap(),
        add: *lib.get(b"ipasir_add").unwrap(),
        assume: *lib.get(b"ipasir_assume").unwrap(),
        solve: *lib.get(b"ipasir_solve").unwrap(),
        val: *lib.get(b"ipasir_val").unwrap(),
        failed: *lib.get(b"ipasir_failed").unwrap(),
        set_terminate: *lib.get(b"ipasir_set_terminate").unwrap(),
        _lib: lib,
    };
    api
}

#[test]
fn exports_ipasir_abi() {
    unsafe {
        let api = api();
        let sig = std::ffi::CStr::from_ptr((api.signature)())
            .to_str()
            .unwrap();
        assert!(sig.starts_with("alloy-ipasir"), "{sig}");

        let s = (api.init)();
        assert!(!s.is_null());

        // (x1 or x2) and (!x1 or x3)
        (api.add)(s, 1);
        (api.add)(s, 2);
        (api.add)(s, 0);
        (api.add)(s, -1);
        (api.add)(s, 3);
        (api.add)(s, 0);
        assert_eq!((api.solve)(s), 10);

        let v1 = (api.val)(s, 1);
        let v2 = (api.val)(s, 2);
        let v3 = (api.val)(s, 3);
        assert!(v1 == 1 || v2 == 2);
        assert!(v1 == -1 || v3 == 3);

        (api.release)(s);
    }
}

#[test]
fn unsat_through_c_abi() {
    unsafe {
        let api = api();
        let s = (api.init)();
        (api.add)(s, 5);
        (api.add)(s, 0);
        (api.add)(s, -5);
        (api.add)(s, 0);
        assert_eq!((api.solve)(s), 20);
        (api.release)(s);
    }
}

#[test]
fn assumptions_through_c_abi() {
    if std::env::var("ALLOY_SAT_BACKEND").as_deref() == Ok("splr") {
        return; // splr does not support assumptions
    }
    unsafe {
        let api = api();
        let s = (api.init)();
        (api.add)(s, 7);
        (api.add)(s, 0);
        (api.assume)(s, -7);
        assert_eq!((api.solve)(s), 20);
        // ipasir_failed reports the conflicting assumption.
        assert_eq!((api.failed)(s, -7), 1);
        assert_eq!((api.failed)(s, 7), 0);
        // Assumptions reset after solve; failed state is gone too.
        assert_eq!((api.solve)(s), 10);
        assert_eq!((api.failed)(s, -7), 0);
        (api.release)(s);
    }
}

#[test]
fn terminate_callback_interrupts_solve() {
    unsafe extern "C" fn always_abort(_state: *mut c_void) -> c_int {
        1
    }
    unsafe {
        let api = api();
        let s = (api.init)();
        (api.add)(s, 1);
        (api.add)(s, 0);
        (api.set_terminate)(s, std::ptr::null_mut(), Some(always_abort));
        assert_eq!((api.solve)(s), 0);
        (api.release)(s);
    }
}
