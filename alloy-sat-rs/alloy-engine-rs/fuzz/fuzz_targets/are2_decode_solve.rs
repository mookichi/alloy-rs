#![no_main]

//! Invariant: the ARE2 wire decoder and solver must accept arbitrary input
//! bytes without panicking. Decoding may fail (Err) and solving may answer
//! UNSAT/ERROR, but neither may abort the process. For inputs that decode
//! AND solve to SAT, the answer body must be well-formed (per-relation
//! tuple counts followed by that many zigzag indices).

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    // Only exercise v2-shaped inputs so budget is spent on the decoder's
    // real surface instead of early magic rejection.
    if data.len() < 4 {
        return;
    }
    let mut buf = Vec::with_capacity(data.len() + 4);
    buf.extend_from_slice(b"ARE2");
    buf.extend_from_slice(data);

    match alloy_engine::decode_problem(&buf) {
        Err(_) => return,
        Ok(mut problem) => {
            let answer = alloy_engine::solve_problem(&mut problem);
            assert!(answer.len() >= 4, "answer shorter than magic");
            let magic = &answer[..4];
            if magic == b"ASAT" {
                // body: per-relation varint count + zigzag indices
                let mut pos = 4usize;
                let read_var = |pos: &mut usize| -> u64 {
                    let mut out = 0u64;
                    let mut shift = 0;
                    loop {
                        let b = answer[*pos];
                        *pos += 1;
                        out |= u64::from(b & 0x7f) << shift;
                        if b & 0x80 == 0 {
                            return out;
                        }
                        shift += 7;
                    }
                };
                for _ in 0..problem.relation_ids.len() {
                    let n = read_var(&mut pos) as usize;
                    for _ in 0..n {
                        read_var(&mut pos);
                    }
                }
            }
        }
    }
});
