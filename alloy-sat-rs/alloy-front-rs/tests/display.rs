//! Real/EReal-aware solution display (`display::format_instance`,
//! `display::format_query_value`): a value is a set of lane bits, so it
//! gains its real-number (or interval) reading alongside the raw set. The
//! type domains and the lane sigs themselves stay raw.

use alloy_front_rs::display::{decode_bitset, format_instance, format_query_value};
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
fn ereal_bitset_reads_as_an_interval() {
    // An `EReal` value is its lane-bit set, so it reads as the interval
    // `c ± R` (a set with `p`/`k` bits) rather than as a bare centre.
    let inst = solve_first("sig x in EReal {}\nfact { setEReal[x, 0.5] }\nrun {}");
    let s = format_instance(&inst);
    assert!(s.contains("x->"), "raw set line missing: {s}");
    assert!(
        s.contains("[m=8 e=-1 p=4 k=0]"),
        "EReal interval reading missing: {s}"
    );
    // There is no lane relation to hide any more.
    assert!(!s.contains("EReal.p"), "raw lanes leaked: {s}");
    assert!(!s.contains("Real.m"), "raw lanes leaked: {s}");
}

#[test]
fn no_lanes_keeps_legacy_shape() {
    let inst = solve_first("sig A {}\npred p { some A }\nrun p for 2");
    let s = format_instance(&inst);
    assert_eq!(s, format!("{}", inst), "non-Real output must be byte-identical");
}

#[test]
fn query_value_decodes_named_sig() {
    // A value is the set of its lane bits, so the sig holds a set (not a
    // single value atom): 2.5 is (m=10, e=1, p=4, k=0) = 4 set bits.
    let src = "sig x in EReal {}\nfact { setEReal[x, 2.5] }\nrun {}";
    let inst = solve_first(src);
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("run");
    let scope = &m.commands[0].scope;
    let v = query_value(&m, scope, &cnf, "x", &inst).expect("query");
    let line = format_query_value(&inst, &v);
    assert!(line.contains("[m=10 e=1 p=4 k=0]"), "got: {line}");
    // Integer and boolean shapes.
    let v = query_value(&m, scope, &cnf, "#x", &inst).expect("query");
    assert_eq!(format_query_value(&inst, &v), "4");
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
    let src = "sig x in EReal {}\nsig A {}\nsig B {}\nsig C {}\nfact { setEReal[x, 2.5] }\nrun {}";
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
        assert_eq!(v, QueryValue::Int(4), "unstable #x");
    }
}

#[test]
fn flat_bitset_appends_real_reading() {
    // Reported case: `X->{...bits...}` gains `= 0.5 [m=1 e=-1]`.
    let inst = solve_first("sig X in Real {}\nfact { setReal[X, 0.5] }\nrun {}");
    let s = format_instance(&inst);
    assert!(s.contains("X->"), "raw set line missing: {s}");
    assert!(s.contains("= 0.5 [m=1 e=-1]"), "real reading missing: {s}");
}

#[test]
fn flat_bitset_query_value_appends_reading() {
    let src = "sig X in Real {}\nfact { setReal[X, 0.5] }\nrun {}";
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("run");
    let inst = solve(&cnf).expect("solve").expect("SAT");
    let scope = &m.commands[0].scope;
    let v = query_value(&m, scope, &cnf, "X", &inst).expect("query");
    let line = format_query_value(&inst, &v);
    assert!(line.contains("= 0.5 [m=1 e=-1]"), "got: {line}");
    // Direct decode: single bits decode, empty/mixed stay raw (None).
    let u = inst.universe();
    let mi = u.index("M$0").unwrap() as u32;
    assert!(decode_bitset(u, &[mi]).is_some());
    assert_eq!(decode_bitset(u, &[]), None);
}

#[test]
fn ints_section_lists_int_atoms() {
    // The solved instance carries the builtin-Int int layer, so the
    // `ints:` section shows entries (`:eval`/`:solve` display parity
    // with `:query Int`).
    let inst = solve_first("sig A {}\nrun {} for 8 Int");
    assert_eq!(inst.int_tuples().count(), 8);
    let s = format_instance(&inst);
    assert!(s.contains(" 0->[[0]]"), "got: {s}");
    assert!(s.contains(" 7->[[7]]"), "got: {s}");
}

#[test]
fn unmentioned_real_leaves_no_shells() {
    // Like `Int` when unused, an unmentioned `Real` binds nothing: no
    // empty `Real`/`$M`/… shells in bounds or display.
    let inst = solve_first("sig A {}\nrun {}");
    let s = format_instance(&inst);
    assert!(!s.contains("Real"), "got: {s}");
    assert!(!s.contains("$M"), "got: {s}");
    assert!(!s.contains("$E"), "got: {s}");
    assert_eq!(inst.int_tuples().count(), 0);
}
