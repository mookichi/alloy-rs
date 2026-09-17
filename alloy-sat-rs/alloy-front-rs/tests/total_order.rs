//! `totalOrder[S, S.next]`: pin the binary links (i.e. `S<:next`) to the
//! canonical chain over the sig's atoms (Java `pred/totalOrder` symmetry
//! breaking). Note this fixes the 2-ary link set (`S<:next`), not the
//! 1-ary join image (`S.next`, the set of targets).

use alloy_front_rs::{parse_module, run, solve};
use std::collections::HashSet;

fn solved(src: &str) -> alloy_front_rs::Instance {
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("run builds Cnf");
    solve(&cnf).expect("solve").expect("SAT")
}

fn chain_src(extra: &str) -> String {
    format!(
        "module t\n\
         sig A {{ next: lone A }}\n\
         fact {{ no a: A | a.next = a }}\n\
         fact {{ one a: A | no a.next }}\n\
         fact {{ one a: A | no next.a and a.*next = A }}\n\
         {extra}\n\
         run {{ #A = 5 }} for 5"
    )
}

#[test]
fn total_order_pins_canonical_chain() {
    let inst = solved(&chain_src("fact { totalOrder[A, A.next] }"));
    let n = inst.universe().size() as i64;
    let a_rel = inst.find_relation_by_name("A").expect("A in instance");
    let a_ts = inst.tuples(a_rel).unwrap();
    let mut atoms: Vec<i64> = a_ts.index_view().iter().map(|i| i % n).collect();
    atoms.sort_unstable();
    assert_eq!(atoms.len(), 5);
    let expected: HashSet<i64> = atoms.windows(2).map(|w| w[0] * n + w[1]).collect();
    let f_rel = inst.find_relation_by_name("A.next").expect("A.next in instance");
    let f_ts = inst.tuples(f_rel).unwrap();
    let actual: HashSet<i64> = f_ts.index_view().iter().collect();
    assert_eq!(actual, expected, "A<:next must be the canonical chain");
}

#[test]
fn total_order_domain_restrict_form_pins_chain() {
    let inst = solved(&chain_src("fact { totalOrder[A, A<:next] }"));
    let n = inst.universe().size() as i64;
    let a_rel = inst.find_relation_by_name("A").expect("A in instance");
    let a_ts = inst.tuples(a_rel).unwrap();
    let mut atoms: Vec<i64> = a_ts.index_view().iter().map(|i| i % n).collect();
    atoms.sort_unstable();
    assert_eq!(atoms.len(), 5);
    let expected: HashSet<i64> = atoms.windows(2).map(|w| w[0] * n + w[1]).collect();
    let f_rel = inst.find_relation_by_name("A.next").expect("A.next in instance");
    let actual: HashSet<i64> = inst.tuples(f_rel).unwrap().index_view().iter().collect();
    assert_eq!(actual, expected, "A<:next must be the canonical chain");
}

#[test]
fn total_order_bare_field_form_pins_chain() {
    let inst = solved(&chain_src("fact { totalOrder[A, next] }"));
    let n = inst.universe().size() as i64;
    let a_rel = inst.find_relation_by_name("A").expect("A in instance");
    let a_ts = inst.tuples(a_rel).unwrap();
    let mut atoms: Vec<i64> = a_ts.index_view().iter().map(|i| i % n).collect();
    atoms.sort_unstable();
    assert_eq!(atoms.len(), 5);
    let expected: HashSet<i64> = atoms.windows(2).map(|w| w[0] * n + w[1]).collect();
    let f_rel = inst.find_relation_by_name("A.next").expect("A.next in instance");
    let actual: HashSet<i64> = inst.tuples(f_rel).unwrap().index_view().iter().collect();
    assert_eq!(actual, expected, "A<:next must be the canonical chain");
}

#[test]
fn total_order_arity_error() {
    let m = parse_module("module t\nsig A { next: lone A }\nrun { totalOrder[A] } for 3").unwrap();
    assert!(run(&m, 0).is_err(), "totalOrder needs 2 args");
}

#[test]
fn total_order_unknown_field_error() {
    let m = parse_module("module t\nsig A { next: lone A }\nrun { totalOrder[A, A.foo] } for 3").unwrap();
    assert!(run(&m, 0).is_err(), "unknown field must error");
}
