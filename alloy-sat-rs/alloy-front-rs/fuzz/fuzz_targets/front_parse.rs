#![no_main]

//! Raw-input fuzz: the lexer/parser must never panic. Any byte string is
//! either accepted or cleanly rejected with `FrontError`.

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let Ok(text) = std::str::from_utf8(data) else {
        return;
    };
    // Cap input size so pathological inputs stay fast.
    if text.len() > 4096 {
        return;
    }
    let _ = alloy_front_rs::parse_module(text);
});
