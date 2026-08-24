use alloy_kodkod_rs::bounds::Bounds;
use alloy_kodkod_rs::relation::RelationPool;
use alloy_kodkod_rs::tuple::Tuple;
use alloy_kodkod_rs::tupleset::TupleSet;
use alloy_kodkod_rs::universe::Universe;
use std::sync::Arc;

fn unary(u: &Arc<Universe>, atoms: &[&str]) -> TupleSet {
    let mut s = TupleSet::new(u, 1).unwrap();
    for a in atoms {
        let t = Tuple::from_atoms(u, &[a]).unwrap();
        s.insert(&t).unwrap();
    }
    s
}

fn pairs(u: &Arc<Universe>, pred: impl Fn(usize, usize) -> bool) -> TupleSet {
    let n = u.size();
    let mut s = TupleSet::new(u, 2).unwrap();
    for i in 0..n {
        for j in 0..n {
            if pred(i, j) {
                let idx = (i as i64) * n as i64 + j as i64;
                s.insert_index(idx);
            }
        }
    }
    s
}

fn main() {
    let u = Universe::new(["N0", "N1", "N2", "N3", "N4"]).unwrap();
    let pool = Arc::new(RelationPool::new());

    let node = pool.intern("Node", 1);
    let next = pool.intern("next", 2);
    pool.set_skolem(pool.intern("$ringSeed", 1), true);

    let mut b = Bounds::new(&u, &pool);
    let nodes = ["N0", "N1", "N2", "N3", "N4"];
    b.bound_exactly(node, &unary(&u, &nodes)).unwrap();

    let upper = pairs(&u, |_, _| true);
    let lower = pairs(&u, |i, j| j == i + 1 && j < u.size());
    b.bound(next, &lower, &upper).unwrap();

    println!("== ring.als equivalent bounds ==");
    println!("{}", b);

    let mut inst = alloy_kodkod_rs::instance::Instance::new(&u, &pool);
    let cycle = pairs(&u, |i, j| j == (i + 1) % u.size());
    inst.add(next, &cycle).unwrap();
    println!("== one concrete instance ==");
    println!("{}", inst);
}
