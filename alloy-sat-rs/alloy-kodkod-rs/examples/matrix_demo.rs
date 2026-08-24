use alloy_kodkod_rs::dimensions::Dimensions;
use alloy_kodkod_rs::{BoolCtx, BooleanMatrix};

fn print_table(name: &str, m: &BooleanMatrix, var_names: &[&str]) {
    println!("-- {name} --");
    let cap = m.dims().capacity();
    for mask in 0u32..1u32 << var_names.len() {
        let model: Vec<bool> = (0..var_names.len()).map(|i| (mask >> i) & 1 == 1).collect();
        let row: Vec<String> = (0..cap)
            .map(|i| match m.get(i) {
                Some(v) => {
                    if m.ctx().eval(v, &model) {
                        "T".into()
                    } else {
                        "F".into()
                    }
                }
                None => ".".into(),
            })
            .collect();
        let assign: Vec<&str> = var_names
            .iter()
            .zip(&model)
            .map(|(n, &b)| if b { n } else { "_" })
            .collect();
        println!("  {:?} -> {:?}", assign, row);
    }
}

fn main() {
    let ctx = BoolCtx::new();
    let x = ctx.variable();
    let y = ctx.variable();

    let dims = Dimensions::square(2, 2).unwrap();
    let mut a = BooleanMatrix::new(dims.clone(), &ctx);
    let mut b = BooleanMatrix::new(dims.clone(), &ctx);
    a.set(0, x).unwrap();
    a.set(3, y).unwrap();
    b.set(0, y).unwrap();
    b.set(1, x).unwrap();

    println!("cells: A[0]=x A[3]=y  B[0]=y B[1]=x  ('.' = absent/false)");
    print_table("A AND B", &a.and(&b).unwrap(), &["x", "y"]);
    print_table("A OR B", &a.or(&b).unwrap(), &["x", "y"]);
    print_table("NOT A", &a.not(), &["x", "y"]);

    let t = a.transpose().unwrap();
    println!("\ntranspose(A) dims={:?} -> indices swapped:", [2usize, 2]);
    for i in 0..4 {
        if t.get(i).is_some() {
            println!("  T[{i}] present");
        }
    }

    let cross = a.cross(&b).unwrap();
    println!(
        "\ncross(A,B) dims={:?} density={} (FALSE-conjunctions skipped)",
        [2usize, 2, 2, 2],
        cross.density()
    );
}
