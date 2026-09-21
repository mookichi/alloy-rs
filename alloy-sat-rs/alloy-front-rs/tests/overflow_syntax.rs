//! `some Overflow { F }` / `no Overflow { F }` search-mode markers.

use alloy_front_rs::{parse_module, run, run_command, solve};

fn build(src: &str) -> alloy_front_rs::Cnf {
    let m = parse_module(src).expect("parse");
    run(&m, 0).expect("build")
}

#[test]
fn some_overflow_finds_dirty_model() {
    let cnf = build(
        "sig X in Signed {}\nfact pin { X = {0, 1, 2} }\nrun { some Overflow { X * X = -15 } } for 4 Int",
    );
    assert!(solve(&cnf).expect("solve").is_some());
}

#[test]
fn some_overflow_clean_only_is_unsat() {
    // Only overflow-free models exist: CEGAR exhausts to UNSAT.
    let cnf = build(
        "sig X in Signed {}\nfact pin { X = {0, 1, 2} }\nrun { some Overflow { X * {0} = 7 } } for 4 Int",
    );
    assert!(solve(&cnf).expect("solve").is_none());
}

#[test]
fn no_overflow_rejects_dirty_model() {
    let cnf = build(
        "sig X in Signed {}\nfact pin { X = {0, 1, 2} }\nrun { no Overflow { X * X = -15 } } for 4 Int",
    );
    assert!(solve(&cnf).expect("solve").is_none());
}

#[test]
fn no_overflow_keeps_clean_model() {
    let cnf = build(
        "sig X in Signed {}\nfact pin { X = {0, 1, 2} }\nrun { no Overflow { X * {0} = 7 } } for 4 Int",
    );
    assert!(solve(&cnf).expect("solve").is_some());
}

#[test]
fn bar_form_works() {
    let cnf = build(
        "sig X in Signed {}\nfact pin { X = {0, 1, 2} }\nrun { some Overflow | X * X = -15 } for 4 Int",
    );
    assert!(solve(&cnf).expect("solve").is_some());
}

#[test]
fn nested_marker_is_rejected() {
    let m = parse_module(
        "sig X in Signed {}\nrun { some y: X | some Overflow { y = y } } for 4 Int",
    )
    .expect("parse");
    assert!(run(&m, 0).is_err(), "nested marker must be rejected");
}

#[test]
fn negated_marker_is_rejected() {
    let m = parse_module(
        "sig X in Signed {}\nrun { not some Overflow { some X } } for 4 Int",
    )
    .expect("parse");
    assert!(run(&m, 0).is_err(), "negated marker must be rejected");
}

#[test]
fn some_overflow_in_check_is_rejected() {
    let m = parse_module(
        "sig X in Signed {}\nassert a { some X }\ncheck { some Overflow { some X } } for 4 Int",
    )
    .expect("parse");
    let err = alloy_front_rs::check(&m, 0).expect_err("check+some must be rejected");
    assert!(err.to_string().contains("only allowed in `run`"), "{err}");
}

#[test]
fn some_overflow_temporal_is_rejected() {
    let m = parse_module(
        "sig X in Signed {}\nrun { some Overflow { some X } } for 4 steps",
    )
    .expect("parse");
    assert!(run(&m, 0).is_err(), "temporal some-Overflow must be rejected");
}

#[test]
fn opt_two_phase_falls_back_to_wrapping() {
    use alloy_front_rs::run_opt_command_with;
    // `minimize X` with X > 0 and X*X < 0: only wrapping models exist.
    let m = parse_module(
        "sig X in Signed {}\nfact { X > 0 }\nfact { X * X < 0 }\nfact { minimize X }\nrun {} for 4 Int",
    )
    .expect("parse");
    let gated = run_opt_command_with(&m, 0, true).expect("gated opt runs");
    assert!(!gated.satisfiable, "no overflow-free optimum");
    let wrapping = run_opt_command_with(&m, 0, false).expect("wrapping opt runs");
    assert!(wrapping.satisfiable, "wrapping optimum exists");
    // Minimum positive bitmask whose square wraps negative at E=5:
    // X = {2} reads 4, 16 truncates to -16.
    assert_eq!(wrapping.cost, Some(4));
}

#[test]
fn run_command_rejects_some_overflow_loudly() {
    // The batch (`als`) path cannot run the CEGAR search: reject instead
    // of silently degrading to a prohibited search.
    let m = parse_module(
        "sig X in Signed {}\nfact pin { X = {0, 1, 2} }\nrun { some Overflow { X * X = -15 } } for 4 Int",
    )
    .expect("parse");
    let err = run_command(&m, 0).expect_err("als path must reject some-Overflow");
    assert!(err.to_string().contains("some Overflow"), "{err}");
}

#[test]
fn run_command_accepts_no_overflow() {
    // `no Overflow` coincides with the default prohibited search.
    let m = parse_module(
        "sig X in Signed {}\nfact pin { X = {0, 1, 2} }\nrun { no Overflow { X * {0} = 7 } } for 4 Int",
    )
    .expect("parse");
    let sol = run_command(&m, 0).expect("no-marker runs anywhere");
    assert!(sol.satisfiable);
}
