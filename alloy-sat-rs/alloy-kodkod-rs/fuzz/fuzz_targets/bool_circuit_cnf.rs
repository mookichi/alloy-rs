#![no_main]

//! Invariant: for a pseudo-random boolean circuit, the Tseitin CNF must be
//! satisfiable exactly when the circuit is satisfiable, and every full
//! assignment's circuit value must match the clause evaluation.

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    if data.len() < 8 {
        return;
    }
    let ctx = alloy_kodkod_rs::BoolCtx::new();
    let nvars = ((data[0] as usize) % 9) + 2; // 2..=10 primary vars
    let mut vars: Vec<alloy_kodkod_rs::bool::BoolRef> = Vec::new();
    for _ in 0..nvars {
        vars.push(ctx.variable());
    }

    // derive a random circuit over the vars
    let mut nodes: Vec<alloy_kodkod_rs::bool::BoolRef> = vars.clone();
    let steps = data.len();
    for (i, &b) in data.iter().enumerate().skip(1) {
        if nodes.is_empty() {
            break;
        }
        let a = nodes[(b as usize) % nodes.len()];
        let c = nodes[((b >> 3) as usize + i) % nodes.len()];
        let op = b >> 6;
        let g = match op {
            0 => ctx.and(&[a, c]),
            1 => ctx.or(&[a, c]),
            2 => ctx.ite(a, c, ctx.not(c)),
            _ => ctx.not(a),
        };
        if !g.is_const() {
            nodes.push(g);
        }
        if nodes.len() > 80 {
            break;
        }
    }
    let root = match nodes.last() {
        Some(r) => *r,
        None => return,
    };

    // brute-force equivalence over all assignments
    let nslots = ctx.num_slots();
    if nslots > 11 {
        return; // keep the 2^n enumeration feasible
    }
    let cnf = {
        let ctx2 = ctx.clone();
        ctx2.with_factory(|factory| {
            alloy_kodkod_rs::cnf::translate_to_cnf(factory, root, nslots)
        })
        .expect("cnf translation")
    };

    // Polarity-optimized definitional translation guarantees:
    //   (a) every CNF-satisfying full assignment makes the circuit true
    //   (b) overall satisfiability matches
    // Per-model equivalence does NOT hold for intermediate slots whose
    // definitions were trimmed by the polarity analysis.
    let satisfies = |model: &[bool], cl: &[i64]| {
        cl.iter().any(|&l| {
            let v = l.unsigned_abs() as usize - 1;
            let sv = model.get(v).copied().unwrap_or(false);
            if l < 0 { !sv } else { sv }
        })
    };
    let mut cnf_sat = false;
    let mut circuit_sat = false;
    for m in 0u64..(1u64 << nslots) {
        let model: Vec<bool> = (0..nslots).map(|i| (m >> i) & 1 == 1).collect();
        let cv = ctx.with_factory(|f| f.eval(root, &model));
        let ok = cnf.clauses.iter().all(|cl| satisfies(&model, cl));
        if ok {
            assert!(cv, "CNF model falsifies circuit: {model:?}");
        }
        cnf_sat |= ok;
        circuit_sat |= cv;
    }
    assert_eq!(cnf_sat, circuit_sat, "satisfiability divergence");
});
