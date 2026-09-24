//! EReal-aware solution display (`display::format_instance`,
//! `display::format_query_value`): decoded per-atom lines replace raw lane
//! tuples; ghost lanes on non-member atoms are hidden.

use alloy_front_rs::display::{decode_ereal, format_instance, format_query_value};
use alloy_front_rs::snippet::{query_value, QueryValue};
use alloy_front_rs::{parse_module, run, solve};

fn solve_first(src: &str) -> alloy_front_rs::Instance {
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("run");
    solve(&cnf)
        .expect("solve")
        .expect("expected SAT with instance")
}

#[test]
fn member_lanes_decode_and_raw_lanes_hidden() {
    let inst = solve_first(
        "one sig x extends EReal {}\nfact { setEReal[x, 0.5] }\nrun {} for 2 EReal",
    );
    let s = format_instance(&inst);
    assert!(s.contains("EReal$0 = 0.5"), "decoded line missing: {s}");
    assert!(!s.contains("EReal.m"), "raw lanes leaked: {s}");
    assert!(!s.contains("EReal.e"), "raw lanes leaked: {s}");
    assert!(!s.contains("EReal.p"), "raw lanes leaked: {s}");
    assert!(!s.contains("EReal.k"), "raw lanes leaked: {s}");
    // The decoded map only covers solved-extent members.
    let dec = decode_ereal(&inst).expect("decode");
    assert_eq!(dec.len(), 1, "expected exactly the member atom: {s}");
}

#[test]
fn no_lanes_keeps_legacy_shape() {
    let inst = solve_first("sig A {}\npred p { some A }\nrun p for 2");
    let s = format_instance(&inst);
    assert_eq!(s, format!("{}", inst), "non-EReal output must be byte-identical");
    assert!(decode_ereal(&inst).is_none());
}

#[test]
fn query_value_decodes_named_sig() {
    let src = "one sig x extends EReal {}\nfact { setEReal[x, 2.5] }\nrun {} for 2 EReal";
    let inst = solve_first(src);
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("run");
    let scope = &m.commands[0].scope;
    let v = query_value(&m, scope, &cnf, "x", &inst).expect("query");
    let line = format_query_value(&inst, &v);
    assert!(line.starts_with("{EReal$0 = 2.5"), "got: {line}");
    // Integer and boolean shapes.
    let v = query_value(&m, scope, &cnf, "#x", &inst).expect("query");
    assert_eq!(format_query_value(&inst, &v), "1");
    let v = query_value(&m, scope, &cnf, "no x", &inst).expect("query");
    assert_eq!(v, QueryValue::Bool(false));
    // Garbage still errors (relational parse error surfaces).
    assert!(query_value(&m, scope, &cnf, "x = = x", &inst).is_err());
}

#[test]
fn query_stable_across_rebuilt_cnfs() {
    // Relation IDs are insertion-ordered per lowering, so an independently
    // rebuilt Cnf may assign `x` a different ID than the solved instance's
    // pool (observed: solve-pool 0 vs rebuild-pool 1, hitting empty `Step`).
    // Queries must resolve through the instance pool regardless. Dummy sigs
    // amplify pool-order divergence; the loop makes accidental alignment
    // across all iterations vanishingly unlikely pre-fix.
    let src = "one sig x extends EReal {}\nsig A {}\nsig B {}\nsig C {}\nfact { setEReal[x, 2.5] }\nrun {} for 3 EReal";
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("run");
    let inst = solve(&cnf).expect("solve").expect("SAT");
    let scope = &m.commands[0].scope;
    for _ in 0..20 {
        let cnf2 = run(&m, 0).expect("run");
        for (expr, want) in [
            ("no x", QueryValue::Bool(false)),
            ("some x", QueryValue::Bool(true)),
        ] {
            let v = query_value(&m, scope, &cnf2, expr, &inst).expect("query");
            assert_eq!(v, want, "unstable query {expr}");
        }
        let v = query_value(&m, scope, &cnf2, "#x", &inst).expect("query");
        assert_eq!(v, QueryValue::Int(1), "unstable #x");
    }
}
