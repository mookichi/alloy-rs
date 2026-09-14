//! Fuzz-found OOM regression: `$` started an identifier but could not
//! continue it, so the lexer emitted empty tokens forever. These inputs
//! must terminate (clean Err, not a hang).
use alloy_front_rs::parse_module;

#[test]
fn dollar_inputs_terminate() {
    for src in [
        "B$",
        "B$\n",
        "B$\n{ q f } for 2\n",
        "si/g Ae B$ \n{ qol\x00\x00\x00\x12f } for 2\n",
        "A$0",
        "$",
        "$$$",
        "$foo bar",
    ] {
        let _ = parse_module(src);
    }
    // And specifically: clean rejection, not a hang.
    assert!(parse_module("B$\n{ q f } for 2\n").is_err());
}

#[test]
fn overlong_int_literal_saturates() {
    // Fuzz-found panic: 24-digit literal overflowed i64 in the lexer.
    let _ = parse_module("s{ 999999999999999999999999+s");
    let _ = parse_module("run {} for 99999999999999999999999");
}
