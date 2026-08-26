use alloy_front_rs::{parse_module, run_command};

fn outcome(src: &str, cmd: usize) -> String {
    let m = parse_module(src).unwrap();
    match run_command(&m, cmd) {
        Ok(s) => if s.satisfiable { "SAT" } else { "UNSAT" }.into(),
        Err(e) => format!("error: {e}"),
    }
}

#[test]
fn ordering_basic() {
    let src = r#"
        module t
        open util/ordering[S] as ord
        sig S {}
        pred p { one ord/first }
        run p for exactly 3
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn ordering_next_is_function() {
    let src = r#"
        module t
        open util/ordering[S] as ord
        sig S {}
        pred p { all s: S | lone s.(ord/next) }
        run p for exactly 3
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn ordering_lte() {
    let src = r#"
        module t
        open util/ordering[S] as ord
        sig S {}
        pred p { ord/lte[ord/first, ord/first] }
        run p for exactly 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn ordering_prevs_nexts() {
    let src = r#"
        module t
        open util/ordering[S] as ord
        sig S {}
        pred p {
            no ord/prevs[ord/first]
            some ord/nexts[ord/first]
        }
        run p for exactly 3
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn ordering_last() {
    let src = r#"
        module t
        open util/ordering[S] as ord
        sig S {}
        pred p {
            ord/first != ord/last
            no ord/nexts[ord/last]
        }
        run p for exactly 2
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn ordering_total_order_unsat() {
    // With exactly 1 atom, first == last, so first != last is unsat
    let src = r#"
        module t
        open util/ordering[S] as ord
        sig S {}
        pred p { ord/first != ord/last }
        run p for exactly 1
    "#;
    assert_eq!(outcome(src, 0), "UNSAT");
}

#[test]
fn ordering_larger() {
    let src = r#"
        module t
        open util/ordering[S] as ord
        sig S {}
        pred p {
            some ord/larger[ord/first, ord/last]
        }
        run p for exactly 3
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}

#[test]
fn ordering_smaller() {
    let src = r#"
        module t
        open util/ordering[S] as ord
        sig S {}
        pred p {
            some ord/smaller[ord/first, ord/last]
        }
        run p for exactly 3
    "#;
    assert_eq!(outcome(src, 0), "SAT");
}
