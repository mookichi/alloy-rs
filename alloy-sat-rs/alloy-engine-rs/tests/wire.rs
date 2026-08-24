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
