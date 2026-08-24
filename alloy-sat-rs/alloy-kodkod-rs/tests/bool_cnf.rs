use alloy_kodkod_rs::bool::{const_false, const_true, BoolFactory, BoolRef};
use alloy_kodkod_rs::cnf::{translate_into_solver, translate_to_cnf};
use alloy_kodkod_rs::sat::{RecordingSolver, SatSolver};

struct Lcg(u64);

impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 33
    }

    fn below(&mut self, n: u64) -> usize {
        (self.next() % n) as usize
    }
}

fn random_circuit(rng: &mut Lcg, f: &mut BoolFactory, nvars: usize, depth: u32) -> BoolRef {
    if depth == 0 {
        return BoolRef(rng.below(nvars as u64) as i32 + 1);
    }
    match rng.below(6) {
        0 => {
            let a = [random_circuit(rng, f, nvars, depth - 1)];
            f.not(a[0])
        }
        1 | 2 => {
            let kids: Vec<BoolRef> = (0..2 + rng.below(3))
                .map(|_| random_circuit(rng, f, nvars, depth - 1))
                .collect();
            f.and(&kids)
        }
        3 | 4 => {
            let kids: Vec<BoolRef> = (0..2 + rng.below(3))
                .map(|_| random_circuit(rng, f, nvars, depth - 1))
                .collect();
            f.or(&kids)
        }
        _ => {
            let c = random_circuit(rng, f, nvars, depth - 1);
            let t = random_circuit(rng, f, nvars, depth - 1);
            let e = random_circuit(rng, f, nvars, depth - 1);
            f.ite(c, t, e)
        }
    }
}

fn circuit_satisfiable(f: &BoolFactory, root: BoolRef, nvars: usize) -> bool {
    for mask in 0u128..(1u128 << nvars) {
        let model: Vec<bool> = (0..nvars).map(|i| (mask >> i) & 1 == 1).collect();
        if f.eval(root, &model) {
            return true;
        }
    }
    false
}

fn first_circuit_model(f: &BoolFactory, root: BoolRef, nvars: usize) -> Option<Vec<bool>> {
    for mask in 0u128..(1u128 << nvars) {
        let model: Vec<bool> = (0..nvars).map(|i| (mask >> i) & 1 == 1).collect();
        if f.eval(root, &model) {
            return Some(model);
        }
    }
    None
}

fn gate_values(f: &BoolFactory, r: BoolRef, model: &mut Vec<Option<bool>>) {
    if r.is_const() || (model.len() >= r.slot() as usize && model[r.slot() as usize - 1].is_some())
    {
        return;
    }
    while model.len() < r.slot() as usize {
        model.push(None);
    }
    match f.node(r).unwrap().clone() {
        alloy_kodkod_rs::bool::BoolNode::Var => {
            model[r.slot() as usize - 1] = Some(model[r.slot() as usize - 1].unwrap_or(false))
        }
        alloy_kodkod_rs::bool::BoolNode::And(kids) => {
            for k in &kids {
                gate_values(f, *k, model);
            }
            model[r.slot() as usize - 1] = Some(
                kids.iter()
                    .all(|&k| model[k.slot() as usize - 1].unwrap() == k.sign()),
            );
        }
        alloy_kodkod_rs::bool::BoolNode::Or(kids) => {
            for k in &kids {
                gate_values(f, *k, model);
            }
            model[r.slot() as usize - 1] = Some(
                kids.iter()
                    .any(|&k| model[k.slot() as usize - 1].unwrap() == k.sign()),
            );
        }
        alloy_kodkod_rs::bool::BoolNode::Ite { c, t, e } => {
            gate_values(f, c, model);
            gate_values(f, t, model);
            gate_values(f, e, model);
            let cv = model[c.slot() as usize - 1].unwrap() == c.sign();
            let chosen = if cv { t } else { e };
            model[r.slot() as usize - 1] =
                Some(model[chosen.slot() as usize - 1].unwrap() == chosen.sign());
        }
    }
}

fn clause_satisfied(clause: &[i64], values: &[Option<bool>]) -> bool {
    clause.iter().any(|&l| {
        let v = values[l.unsigned_abs() as usize - 1];
        v.map(|b| b == (l > 0)).unwrap_or(false)
    })
}

#[test]
fn factory_folding_matches_java_semantics() {
    let mut f = BoolFactory::new();
    let x = f.variable();
    assert_eq!(f.and(&[x, const_true()]), x);
    assert_eq!(f.or(&[x, const_false()]), x);
    assert_eq!(f.and(&[x, const_false()]), const_false());
    assert_eq!(f.or(&[x, const_true()]), const_true());
    assert_eq!(f.not(f.not(x)), x);
    assert_eq!(f.and(&[]), const_true());
    assert_eq!(f.or(&[]), const_false());
    assert_eq!(f.ite(const_true(), x, const_false()), x);
}

#[test]
fn gate_caching_shares_slots_commutatively() {
    let mut f = BoolFactory::new();
    let x = f.variable();
    let y = f.variable();
    let g1 = f.and(&[x, y]);
    let g2 = f.and(&[y, x]);
    assert_eq!(g1, g2);
    assert_eq!(f.num_slots(), 3);

    let i1 = f.ite(x, y, f.not(y));
    let i2 = f.ite(x, y, f.not(y));
    assert_eq!(i1, i2);
}

#[test]
fn constant_roots_translate_to_trivial_cnfs() {
    let f = BoolFactory::new();
    let sat = translate_to_cnf(&f, const_true(), 0).unwrap();
    assert_eq!(sat.clauses.len(), 0);
    let unsat = translate_to_cnf(&f, const_false(), 3).unwrap();
    assert_eq!(unsat.clauses, vec![Vec::<i64>::new()]);
}

#[test]
fn simple_and_translation_clauses_exact() {
    let mut f = BoolFactory::new();
    let x = f.variable();
    let y = f.variable();
    let root = f.and(&[x, y]);
    let cnf = translate_to_cnf(&f, root, 2).unwrap();
    assert_eq!(cnf.num_vars, 3);
    assert_eq!(
        {
            let mut c = cnf.clauses.clone();
            c.sort();
            c
        },
        vec![vec![1], vec![2]]
    );
}

#[test]
fn ite_gate_negative_polarity_only_emits_three_plus_unit() {
    let mut f = BoolFactory::new();
    let i = f.variable();
    let t = f.variable();
    let e = f.variable();
    let ite = f.ite(i, t, e);
    let root = f.not(ite);
    let cnf = translate_to_cnf(&f, root, 3).unwrap();
    assert_eq!(cnf.clauses.len(), 4);
}

#[test]
fn translation_equivalent_fuzz() {
    let mut rng = Lcg(0xC0FFEE);
    for case in 0..40 {
        let nvars = 1 + case % 5;
        let mut f = BoolFactory::new();
        for _ in 0..nvars {
            f.variable();
        }
        let root = random_circuit(&mut rng, &mut f, nvars, 4);

        let expected_sat = circuit_satisfiable(&f, root, nvars);

        let cnf = translate_to_cnf(&f, root, nvars).unwrap();

        if let Some(primary) = first_circuit_model(&f, root, nvars) {
            let mut values: Vec<Option<bool>> = primary.iter().map(|&b| Some(b)).collect();
            while values.len() < cnf.num_vars {
                values.push(None);
            }
            gate_values(&f, root, &mut values);
            for c in &cnf.clauses {
                assert!(
                    clause_satisfied(c, &values),
                    "case {}: clause {:?} violated by gate model {:?}",
                    case,
                    c,
                    values
                );
            }
        }

        if cnf.num_vars <= 20 {
            let mut solver = RecordingSolver::new();
            translate_into_solver(&mut solver, &f, root, nvars).unwrap();
            let actual_sat = solver.solve();
            assert_eq!(expected_sat, actual_sat, "case {}", case);

            if expected_sat {
                let model: Vec<bool> = (1..=nvars as i64).map(|v| solver.value_of(v)).collect();
                for var in 1..=nvars as i64 {
                    assert_eq!(
                        f.eval(BoolRef(var as i32), &model),
                        solver.value_of(var),
                        "case {} var {}",
                        case,
                        var
                    );
                }
            }
        }
    }
}

#[test]
fn top_level_and_uses_unit_clauses_path() {
    let mut f = BoolFactory::new();
    let x = f.variable();
    let y = f.variable();
    let z = f.variable();
    let inner = f.or(&[x, y]);
    let root = f.and(&[inner, z]);

    let cnf = translate_to_cnf(&f, root, 3).unwrap();
    assert!(cnf.clauses.contains(&vec![3]));
    assert!(cnf.clauses.contains(&vec![1, 2, -(inner.0 as i64)]));

    let mut solver = RecordingSolver::new();
    translate_into_solver(&mut solver, &f, root, 3).unwrap();
    assert!(solver.solve());
}
