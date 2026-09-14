//! Field multiplicity + typing regressions.
//!
//! - `f: lone/one/some B` constrains each owner row (not the inverse).
//! - Field tuples stay inside the current `Owner -> Type` extent
//!   (no dangling tuples); an empty range forces an empty field.

use alloy_front_rs::{parse_module, query, run, solve, validate};
use std::collections::{HashMap, HashSet};

/// Row -> count and full range set of a binary field in an instance.
fn rows_and_range(
    inst: &alloy_front_rs::Instance,
    rel: &str,
) -> (HashMap<i64, usize>, HashSet<i64>) {
    let n = inst.universe().size() as i64;
    let r = inst.find_relation_by_name(rel).expect("field in instance");
    let ts = inst.tuples(r).unwrap();
    assert_eq!(ts.arity(), 2);
    let mut rows: HashMap<i64, usize> = HashMap::new();
    let mut range: HashSet<i64> = HashSet::new();
    for i in ts.index_view().iter() {
        *rows.entry(i / n).or_default() += 1;
        range.insert(i % n);
    }
    (rows, range)
}

fn range_atoms(inst: &alloy_front_rs::Instance, sig: &str) -> HashSet<i64> {
    let n = inst.universe().size() as i64;
    let r = inst.find_relation_by_name(sig).expect("sig in instance");
    let ts = inst.tuples(r).unwrap();
    assert_eq!(ts.arity(), 1);
    ts.index_view().iter().map(|i| i % n).collect()
}

fn solved(src: &str) -> (alloy_front_rs::Module, alloy_front_rs::Cnf, alloy_front_rs::Instance) {
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("run builds Cnf");
    let inst = solve(&cnf).expect("solve").expect("SAT");
    assert!(validate(&cnf, &inst).is_some(), "solution validates");
    (m, cnf, inst)
}

#[test]
fn lone_enforced_per_row_and_no_dangling() {
    let (m, cnf, inst) = solved(
        "module t\nsig A { f: lone B }\nsig B {}\npred ok { some A.f }\nrun ok for 3",
    );
    let (rows, range) = rows_and_range(&inst, "A.f");
    assert!(!rows.is_empty(), "some A.f needs tuples");
    for (row, c) in &rows {
        assert!(*c <= 1, "lone violated at row {row}: {c}");
    }
    let b = range_atoms(&inst, "B");
    assert!(!b.is_empty(), "nonempty f needs nonempty B");
    for t in &range {
        assert!(b.contains(t), "dangling tuple targets {t}");
    }
    // Same through the query path.
    let scope = &m.commands[0].scope;
    let (arity, _) = query(&m, scope, &cnf, "A.f", &inst).expect("query");
    assert_eq!(arity, 1);
}

#[test]
fn empty_range_forces_empty_field() {
    // B empty + f nonempty (dangling) must be UNSAT.
    let src = "module t\nsig A { f: lone B }\nsig B {}\nfact { no B }\npred ok { some A.f }\nrun ok for 3";
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("run builds Cnf");
    assert!(
        solve(&cnf).expect("solve").is_none(),
        "dangling model must be UNSAT"
    );
}

#[test]
fn one_enforced_per_row() {
    let (_, _, inst) = solved(
        "module t\nsig A { f: one B }\nsig B {}\npred ok { some A }\nrun ok for exactly 2",
    );
    let (rows, range) = rows_and_range(&inst, "A.f");
    let a: HashSet<i64> = range_atoms(&inst, "A");
    for atom in &a {
        assert_eq!(
            rows.get(atom).copied().unwrap_or(0),
            1,
            "one violated at row {atom}"
        );
    }
    let b = range_atoms(&inst, "B");
    for t in &range {
        assert!(b.contains(t), "dangling tuple targets {t}");
    }
}

#[test]
fn some_vacuous_over_empty_owner() {
    // No owner atoms: the per-row constraint is vacuous, still SAT.
    let src = "module t\nsig A { f: some B }\nsig B {}\nfact { no A }\nrun {} for 3";
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("run builds Cnf");
    let inst = solve(&cnf).expect("solve").expect("SAT");
    let (rows, _) = rows_and_range(&inst, "A.f");
    assert!(rows.is_empty(), "empty owner forces empty field");
    assert!(validate(&cnf, &inst).is_some());
}

#[test]
fn excess_tuples_unsat() {
    // 3 A-atoms with lone rows hold at most 3 tuples.
    let src = "module t\nsig A { f: lone B }\nsig B {}\npred tooMany { #(A.f) > 3 }\nrun tooMany for 3";
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("run builds Cnf");
    assert!(
        solve(&cnf).expect("solve").is_none(),
        "lone rows cap total tuples"
    );
}

#[test]
fn ternary_trailing_some_enforced() {
    // P9: each (book, n) row must be nonempty; with T empty this is UNSAT.
    let src = "module t\nsig Book { addr: N -> some T }\nsig N {}\nsig T {}\nfact { some Book and some N and no T }\nrun {} for 3";
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("run builds Cnf");
    assert!(
        solve(&cnf).expect("solve").is_none(),
        "ternary trailing some must be enforced (P9)"
    );
}

#[test]
fn ternary_trailing_some_sat_when_fitting() {
    // Same shape, satisfiable: every (book, n) row gets a T.
    let src = "module t\nsig Book { addr: N -> some T }\nsig N {}\nsig T {}\npred ok { some Book.addr }\nrun ok for 2";
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("run builds Cnf");
    let inst = solve(&cnf).expect("solve").expect("SAT");
    assert!(validate(&cnf, &inst).is_some());
    // every (book, n) prefix row is nonempty in the value column
    let n = inst.universe().size() as i64;
    let rb = inst.find_relation_by_name("Book").expect("Book");
    let rn = inst.find_relation_by_name("N").expect("N");
    let ra = inst.find_relation_by_name("Book.addr").expect("addr");
    let books: Vec<i64> = inst.tuples(rb).unwrap().index_view().iter().collect();
    let ns: Vec<i64> = inst.tuples(rn).unwrap().index_view().iter().collect();
    let ats = inst.tuples(ra).unwrap();
    assert!(!books.is_empty() && !ns.is_empty());
    for b in &books {
        for nn in &ns {
            let hit = ats.index_view().iter().any(|i| i / (n * n) == *b && (i / n) % n == *nn);
            assert!(hit, "ternary row ({b},{nn}) must be nonempty");
        }
    }
}

#[test]
fn ternary_trailing_lone_enforced() {
    // `N -> lone T`: at most one T per (book, n); forcing two is UNSAT.
    let src = "module t\nsig Book { addr: N -> lone T }\nsig N {}\nsig T {}\npred two { some b: Book, n: N | #(b.addr[n]) > 1 }\nrun two for 2";
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("run builds Cnf");
    assert!(
        solve(&cnf).expect("solve").is_none(),
        "ternary trailing lone must be enforced"
    );
}

#[test]
fn leading_lone_enforced_per_last() {
    // `f: A lone -> B` in O: per (owner, B) pair the preimage is lone.
    // Full field over one O/B forces a 2-preimage -> UNSAT.
    let src = "module t\nsig O { f: A lone -> B }\nsig A {}\nsig B {}\nfact { one O and one B and O.f = O -> A -> B }\nrun {} for exactly 2 A";
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("run builds Cnf");
    assert!(
        solve(&cnf).expect("solve").is_none(),
        "leading lone must be enforced"
    );
}

#[test]
fn leading_lone_fitting() {
    let src = "module t\nsig O { f: A lone -> B }\nsig A {}\nsig B {}\nfact { one O and one B }\npred ok { #(O.f) = 1 }\nrun ok for exactly 2 A";
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("run builds Cnf");
    let inst = solve(&cnf).expect("solve").expect("SAT");
    assert!(validate(&cnf, &inst).is_some());
}

#[test]
fn both_sides_enforced() {
    // `f: A some -> lone B`: trailing lone per row AND leading some per (owner, B).
    // Empty field violates the leading some -> UNSAT.
    let src = "module t\nsig O { f: A some -> lone B }\nsig A {}\nsig B {}\nfact { one O and one B and no O.f }\nrun {} for 2";
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("run builds Cnf");
    assert!(
        solve(&cnf).expect("solve").is_none(),
        "leading some must be enforced"
    );
}

#[test]
fn both_sides_fitting() {
    let src = "module t\nsig O { f: A some -> lone B }\nsig A {}\nsig B {}\nfact { one O and one B }\npred ok { #(O.f) = 1 }\nrun ok for exactly 2 A";
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("run builds Cnf");
    let inst = solve(&cnf).expect("solve").expect("SAT");
    assert!(validate(&cnf, &inst).is_some());
}

#[test]
fn leading_position_mult_rejected_like_java() {
    // Java parity: `m A -> B` (marking before the first segment) is a type
    // error; the marking must follow its segment (`A m -> B`).
    for bad in [
        "module t\nsig O { f: lone A -> B }\nsig A {}\nsig B {}\nrun {} for 2",
        "module t\nsig O { f: one A -> B }\nsig A {}\nsig B {}\nrun {} for 2",
        "module t\nsig O { f: some A -> B }\nsig A {}\nsig B {}\nrun {} for 2",
    ] {
        assert!(
            parse_module(bad).is_err(),
            "leading-position marking must be rejected: {bad}"
        );
    }
}

#[test]
fn middle_marker_single_pair_fitting() {
    // Middle-column markings (`A -> lone B -> C`) quantify suffix pairs:
    // a single pair per (owner, A) row solves and validates.
    let src = "module t\nsig O { f: A -> lone B -> C }\nsig A {}\nsig B {}\nsig C {}\nfact { #(O.f) = 1 }\nrun {} for 1";
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("run builds Cnf");
    let inst = solve(&cnf).expect("solve").expect("SAT");
    assert!(validate(&cnf, &inst).is_some());
}

#[test]
fn middle_pairs_enforced() {
    // `f: A -> lone B -> C` in O: per (owner, A) row the (B x C) pairs are lone.
    // Two pairs sharing (o, a) -> UNSAT (Java-verified).
    let src = "module t\nsig O { f: A -> lone B -> C }\nsig A {}\nsig B {}\nsig C {}\nfact { one O and one A and #B = 2 and #(O.f) = 2 }\nrun {} for 3";
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("run builds Cnf");
    assert!(
        solve(&cnf).expect("solve").is_none(),
        "middle lone must constrain suffix pairs"
    );
}

#[test]
fn middle_pairs_fitting() {
    // Same shape, one pair per (o, a): SAT and validates.
    let src = "module t\nsig O { f: A -> lone B -> C }\nsig A {}\nsig B {}\nsig C {}\nfact { one O and one A }\npred ok { #(O.f) = 1 }\nrun ok for 3";
    let m = parse_module(src).expect("parse");
    let cnf = run(&m, 0).expect("run builds Cnf");
    let inst = solve(&cnf).expect("solve").expect("SAT");
    assert!(validate(&cnf, &inst).is_some());
}
