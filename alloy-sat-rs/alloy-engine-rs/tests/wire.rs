//! Wire-format roundtrip tests: encode a small problem with the same
//! layout the Java serializer emits, decode + solve it through the engine.

use alloy_engine::*;

#[allow(dead_code)]
struct W(Vec<u8>);

impl W {
    fn new() -> W {
        W(b"ARE1".to_vec())
    }
    fn b(&mut self, v: u8) -> &mut Self {
        self.0.push(v);
        self
    }
    fn s(&mut self, v: &str) -> &mut Self {
        let b = v.as_bytes();
        self.0.extend_from_slice(&(b.len() as u16).to_le_bytes());
        self.0.extend_from_slice(b);
        self
    }
    fn var(&mut self, mut v: u64) -> &mut Self {
        loop {
            let byte = (v & 0x7f) as u8;
            v >>= 7;
            if v == 0 {
                self.0.push(byte);
                break;
            }
            self.0.push(byte | 0x80);
        }
        self
    }
    #[allow(dead_code)]
    fn sv(&mut self, v: i64) -> &mut Self {
        let z = ((v << 1) ^ (v >> 63)) as u64;
        self.var(z)
    }
    fn id(&mut self, v: u32) -> &mut Self {
        self.var(v as u64)
    }
}

/// x1 ∨ x2 over atoms {a,b}: rel p ⊆ {a,b}, formula = some p.
#[test]
fn sat_problem_roundtrip() {
    let mut w = W::new();
    w.b(4); // bitwidth
    w.var(2).s("a").s("b"); // atoms
                            // one relation "p", arity 1, lower empty, upper both atoms
    w.var(1).s("p").b(1).var(0).var(2).sv(0).sv(1);
    w.var(0); // no variables
              // nodes: [0]=EConst(Univ)?? simpler: ERel(p)=node0; F node1=Mult(Some,node0)
    w.var(2)
        .var(32)
        .id(0) // expr: relation p
        .var(6)
        .b(0)
        .id(0); // formula: some (p)
    w.id(1); // root
    let problem = w.0.clone();

    let decoded = decode_problem(&problem).expect("decode");
    assert_eq!(decoded.relation_names, vec!["p"]);

    let answer = solve_wire(&problem);
    assert_eq!(&answer[..4], ANSWER_SAT);
    // one relation follows with >=1 tuple.
    assert!(answer.len() > 5);
}

/// ARE2 with the want_core flag: UNSAT answers list culprit conjunct node
/// positions ("AUNC" magic).
#[test]
fn are2_unsat_core() {
    let mut w = W::v2();
    w.b(4); // bitwidth
    w.b(8); // options: want_core(bit3), mode=none
    w.var(1); // max_threads
    w.var(2).s("a").s("b");
    w.var(1).s("p").b(1).var(0).var(2).sv(0).sv(1);
    w.var(0);
    // nodes: 0=Rel p; 1=some p; 2=not(some p); 3=and[1,2]
    w.var(4)
        .var(32)
        .id(0)
        .var(6)
        .b(0)
        .id(0) // some p
        .var(1)
        .id(1) // not (some p)
        .var(2)
        .b(0)
        .var(2)
        .id(1)
        .id(2); // and of 2 children
    w.id(3);

    let decoded = decode_problem(&w.0).expect("decode");
    assert!(decoded.options.want_core);

    let answer = solve_wire(&w.0);
    assert_eq!(&answer[..4], ANSWER_UNSAT_CORE);
    // Minimal core = both conjuncts: each one alone is satisfiable
    // (`some p` vs `not (some p)`), only their conjunction conflicts.
    assert_eq!(answer[4], 2); // two culprits
    assert_eq!(&answer[5..7], &[1, 2]); // nodes of `some p` and `not (some p)`
}

/// some p ∧ no p must be UNSAT.
#[test]
fn unsat_problem_roundtrip() {
    let mut w = W::new();
    w.b(4);
    w.var(2).s("a").s("b");
    w.var(1).s("p").b(1).var(0).var(2).sv(0).sv(1);
    w.var(0);
    // nodes: 0=Rel p; 1=some p; 2=not(some p); 3=and[1,2]
    w.var(4)
        .var(32)
        .id(0)
        .var(6)
        .b(0)
        .id(0) // some p
        .var(1)
        .id(1) // not (some p)
        .var(2)
        .b(0)
        .var(2)
        .id(1)
        .id(2); // and of 2 children
    w.id(3);

    let answer = solve_wire(&w.0);
    assert_eq!(&answer[..4], ANSWER_UNSAT);
}

// ---------------------------------------------------------------------------
// ARE2 (Iter 11): solver options + dynamic decomposition trailer
// ---------------------------------------------------------------------------

impl W {
    fn v2() -> W {
        W(b"ARE2".to_vec())
    }
}

/// ARE2 with skolemize flag decodes into WireOptions and solves.
#[test]
fn are2_options_roundtrip() {
    let mut w = W::v2();
    w.b(4); // bitwidth
    w.b(1); // options: skolemize=true, mode=none
    w.var(1); // max_threads
    w.var(2).s("a").s("b");
    // two variable relations so skolemization has something to do:
    // formula = some p && some q  (both ⊆ {a,b})
    w.var(2)
        .s("p")
        .b(1)
        .var(0)
        .var(2)
        .sv(0)
        .sv(1)
        .s("q")
        .b(1)
        .var(0)
        .var(2)
        .sv(0)
        .sv(1);
    w.var(0);
    // nodes: 0=Rel p, 1=Rel q, 2=some p, 3=some q, 4=and[2,3]
    w.var(5)
        .var(32)
        .id(0)
        .var(32)
        .id(1)
        .var(6)
        .b(0)
        .id(0)
        .var(6)
        .b(0)
        .id(1)
        .var(2)
        .b(0)
        .var(2)
        .id(2)
        .id(3);
    w.id(4);

    let decoded = decode_problem(&w.0).expect("decode");
    assert!(decoded.options.skolemize);
    assert_eq!(decoded.options.decompose, Decompose::None);
    assert_eq!(decoded.options.max_threads, 1);
    let answer = solve_wire(&w.0);
    assert_eq!(&answer[..4], ANSWER_SAT);
}

/// Dynamic decomposition: partial `s` is solved in stage 1 and anchored;
/// symbolic upper bound of `d` resolves to stage-1's value of `s`.
#[test]
fn are2_dynamic_symbolic_bound() {
    let mut w = W::v2();
    w.b(4); // bitwidth
    w.b((3 << 1) as u8); // options: skolemize=false, mode=Dynamic(3)
    w.var(1); // max_threads (unused for dynamic)
    w.var(2).s("a").s("b");
    // rel s: variable (∅..{a,b}); rel d: variable (∅..{a,b})
    w.var(2)
        .s("s")
        .b(1)
        .var(0)
        .var(2)
        .sv(0)
        .sv(1)
        .s("d")
        .b(1)
        .var(0)
        .var(2)
        .sv(0)
        .sv(1);
    w.var(0);
    // nodes: 0=Rel s, 1=Rel d, 2=some s, 3=some d, 4=d in s (subset), 5=and[2,3,4]
    w.var(6)
        .var(32)
        .id(0)
        .var(32)
        .id(1)
        .var(6)
        .b(0)
        .id(0)
        .var(6)
        .b(0)
        .id(1)
        .var(3)
        .b(0)
        .id(1)
        .id(0) // subset(d, s): op0=SUBSET, l=node1(d), r=node0(s)
        .var(2)
        .b(0)
        .var(3)
        .id(2)
        .id(3)
        .id(4);
    w.id(5);
    // trailer: partials=[s]; symbound (d, upper, node0=Rel s)
    w.var(1).id(0);
    w.var(1).id(1).b(1).id(0);

    let decoded = decode_problem(&w.0).expect("decode");
    assert_eq!(decoded.options.decompose, Decompose::Dynamic);
    assert_eq!(decoded.partials, vec![0]);
    assert_eq!(decoded.symbounds.len(), 1);

    let answer = solve_wire(&w.0);
    if &answer[..4] != ANSWER_SAT {
        let msg = if &answer[..4] == ANSWER_ERR && answer.len() >= 6 {
            String::from_utf8_lossy(&answer[6..]).into_owned()
        } else {
            format!("{:?}", &answer[..answer.len().min(24)])
        };
        panic!("dynamic solve should be SAT: {msg}");
    }
    // Parse ASAT: per-relation tuple counts; d's model must be a subset of
    // the single stage-1 value chosen for s (|d| <= |s| <= 1).
    let body = &answer[4..];
    let mut pos = 0usize;
    fn read_var(body: &[u8], pos: &mut usize) -> u64 {
        let mut out = 0u64;
        let mut shift = 0;
        loop {
            let b = body[*pos];
            *pos += 1;
            out |= u64::from(b & 0x7f) << shift;
            if b & 0x80 == 0 {
                return out;
            }
            shift += 7;
        }
    }
    let n_s = read_var(body, &mut pos);
    for _ in 0..n_s {
        read_var(body, &mut pos); // skip zigzag tuple indices
    }
    let n_d = read_var(body, &mut pos);
    assert!(n_d <= 1, "symbolic upper bound forces |d| <= 1, got {n_d}");
}
