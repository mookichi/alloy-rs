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
    // The assumption is in the core: it conflicts with the unit clause.
    assert!(s.failed(-1));
    assert_eq!(s.failed_core(), vec![-1]);
    // Assumptions are reset after solve.
    assert_eq!(s.solve(), IPASIR_SAT);
    assert!(!s.failed(-1));
    assert!(s.failed_core().is_empty());
}

#[test]
fn failed_assumptions_form_a_core() {
    // Clauses: (1) (2) (3). Assuming -1, -2 and 4 is UNSAT. The backend's
    // failed set must be a genuine unsatisfiable core: a subset of the
    // assumptions which is UNSAT on its own (it need not contain every
    // logically conflicting assumption).
    if std::env::var("ALLOY_SAT_BACKEND").as_deref() == Ok("splr") {
        return;
    }
    let mut s = sat_session();
    if !s.supports_assumptions() {
        return;
    }
    s.add_clause(&[1]);
    s.add_clause(&[2]);
    s.add_clause(&[3]);
    s.assume(-1);
    s.assume(-2);
    s.assume(4);
    assert_eq!(s.solve(), IPASIR_UNSAT);
    let core = s.failed_core();
    assert!(!core.is_empty(), "expected a non-empty core");
    assert!(core.iter().all(|&l| l == -1 || l == -2 || l == 4));
    assert!(!s.failed(4));
    // Re-solving under exactly the reported core must still be UNSAT.
    for &l in &core {
        s.assume(l);
    }
    assert_eq!(s.solve(), IPASIR_UNSAT);
    // Here every member of {-1,-2} conflicts on its own, so assuming only
    // the non-failed literal 4 restores satisfiability.
    s.assume(4);
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
