use alloy_front_rs::parse_module;

#[test]
fn open_with_exactly_param() {
    let src = r#"
        module test
        open util/ordering[exactly Time] as to
        sig Time {}
    "#;
    let m = parse_module(src).unwrap();
    assert_eq!(m.opens.len(), 1);
    assert_eq!(m.opens[0].path, "util/ordering");
    assert_eq!(m.opens[0].alias, "to");
    assert_eq!(m.opens[0].params.len(), 1);
    match &m.opens[0].params[0] {
        alloy_front_rs::OpenParam::Exactly(n) => assert_eq!(n, "Time"),
        _ => panic!("expected Exactly"),
    }
}

#[test]
fn open_with_set_param() {
    let src = r#"
        module test
        open util/ordering[Key] as ko
        sig Key {}
    "#;
    let m = parse_module(src).unwrap();
    assert_eq!(m.opens.len(), 1);
    assert_eq!(m.opens[0].params.len(), 1);
    match &m.opens[0].params[0] {
        alloy_front_rs::OpenParam::Set(n) => assert_eq!(n, "Key"),
        _ => panic!("expected Set"),
    }
}

#[test]
fn open_without_params() {
    let src = r#"
        module test
        open util/seqr as sr
    "#;
    let m = parse_module(src).unwrap();
    assert_eq!(m.opens.len(), 1);
    assert_eq!(m.opens[0].params.len(), 0);
}

#[test]
fn multiple_opens() {
    let src = r#"
        module test
        open util/ordering[exactly Time] as to
        open util/ordering[Key] as ko
        sig Time {}
        sig Key {}
    "#;
    let m = parse_module(src).unwrap();
    assert_eq!(m.opens.len(), 2);
    assert_eq!(m.opens[0].alias, "to");
    assert_eq!(m.opens[1].alias, "ko");
}
