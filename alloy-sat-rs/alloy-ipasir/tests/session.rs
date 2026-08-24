use alloy_ipasir::{Session, IPASIR_SAT, IPASIR_UNSAT};

fn sat_session() -> Session {
    Session::new().expect("backend available")
}

#[test]
fn signature_names_backend() {
    let s = sat_session();
    assert!(!s.backend_name().is_empty());
}

#[test]
fn simple_sat_and_model() {
    let mut s = sat_session();
    s.add_clause(&[1, 2]);
    s.add_clause(&[-1, 3]);
    assert_eq!(s.solve(), IPASIR_SAT);
    // Model must satisfy both clauses.
    let v1 = s.value(1) > 0;
    let v2 = s.value(2) > 0;
    let v3 = s.value(3) > 0;
    assert!(v1 || v2);
    assert!(!v1 || v3);
}

#[test]
fn trivial_unsat() {
    let mut s = sat_session();
    s.add_clause(&[1]);
    s.add_clause(&[-1]);
    assert_eq!(s.solve(), IPASIR_UNSAT);
}

#[test]
fn empty_clause_is_unsat() {
    let mut s = sat_session();
    s.add_clause(&[]);
    assert_eq!(s.solve(), IPASIR_UNSAT);
}

#[test]
fn incremental_addition_can_turn_unsat() {
    let mut s = sat_session();
    s.add_clause(&[1, 2]);
    assert_eq!(s.solve(), IPASIR_SAT);
    s.add_clause(&[-1]);
    assert_eq!(s.solve(), IPASIR_SAT);
    assert!(s.value(1) < 0);
    s.add_clause(&[-2]);
    assert_eq!(s.solve(), IPASIR_UNSAT);
}

#[test]
fn assumptions_with_cadical() {
    // Assumptions require backend support; splr rejects them.
    if std::env::var("ALLOY_SAT_BACKEND").as_deref() == Ok("splr") {
        return;
    }
    let mut s = sat_session();
    if !s.supports_assumptions() {
        return;
    }
    s.add_clause(&[1]);
    s.assume(-1);
    assert_eq!(s.solve(), IPASIR_UNSAT);
    // Assumptions are reset after solve.
    assert_eq!(s.solve(), IPASIR_SAT);
}

#[test]
fn termination_request_interrupts_solve() {
    extern "C" fn always_abort(_state: *mut std::ffi::c_void) -> i32 {
        1
    }
    let mut s = sat_session();
    s.set_terminate(always_abort, std::ptr::null_mut());
    assert_eq!(s.solve(), 0);
}
