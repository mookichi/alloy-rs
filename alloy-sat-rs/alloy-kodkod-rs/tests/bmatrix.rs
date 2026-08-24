use alloy_kodkod_rs::bmatrix::{BooleanMatrix, MatrixError};
use alloy_kodkod_rs::bool::BoolRef;
use alloy_kodkod_rs::dimensions::{Dimensions, DimsError};
use alloy_kodkod_rs::BoolCtx;

fn dense_oracle(a: &[bool], b: &[bool], op: impl Fn(bool, bool) -> bool) -> Vec<bool> {
    a.iter().zip(b).map(|(&x, &y)| op(x, y)).collect()
}

#[test]
fn dimensions_validation_and_shape_algebra() {
    assert!(matches!(
        Dimensions::square(0, 2),
        Err(DimsError::InvalidSize(0))
    ));
    assert!(matches!(Dimensions::square(3, 0), Err(DimsError::Empty)));
    assert!(matches!(
        Dimensions::rectangular(&[2, 0]),
        Err(DimsError::InvalidSize(0))
    ));

    let a = Dimensions::rectangular(&[2, 3]).unwrap();
    let b = Dimensions::rectangular(&[3, 4]).unwrap();
    assert_eq!(
        a.dot(&b).unwrap(),
        Dimensions::rectangular(&[2, 4]).unwrap()
    );
    assert_eq!(a.capacity(), 6);
    assert_eq!(
        a.cross(&b).unwrap(),
        Dimensions::rectangular(&[2, 3, 3, 4]).unwrap()
    );

    let sq = Dimensions::square(3, 3).unwrap();
    assert!(sq.is_square());
    assert!(!a.is_square());
    assert_eq!(
        a.transpose().unwrap(),
        Dimensions::rectangular(&[3, 2]).unwrap()
    );
    assert!(matches!(
        sq.transpose(),
        Err(DimsError::TransposeNeeds2D(3))
    ));
    assert!(matches!(
        a.dot(&Dimensions::rectangular(&[5, 5]).unwrap()),
        Err(DimsError::DotMismatch { left: 3, right: 5 })
    ));
}

#[test]
fn flat_vector_conversion_is_row_major_like_java() {
    let d = Dimensions::rectangular(&[2, 3, 4]).unwrap();
    for i in 0..d.capacity() {
        let v = d.vector_of(i).unwrap();
        assert_eq!(d.flat_of(&v).unwrap(), i);
    }
    let v = d.vector_of(23).unwrap();
    assert_eq!(v, vec![1, 2, 3]);
    assert_eq!(d.flat_of(&[1, 2, 3]), Some(23));
    assert!(!d.validate_flat(d.capacity()));
    assert!(!d.validate_vector(&[0, 0, 9]));
}

#[test]
fn not_fills_absent_with_true() {
    let ctx = BoolCtx::new();
    let x = ctx.variable();
    let mut m = BooleanMatrix::new(Dimensions::square(2, 2).unwrap(), &ctx);
    m.set(0, x).unwrap();

    let neg = m.not();
    assert_eq!(neg.density(), 4);

    let model = [false];
    assert_eq!(neg.eval_dense(&model), vec![true, true, true, true]);

    let model = [true];
    assert_eq!(neg.eval_dense(&model), vec![false, true, true, true]);
}

#[test]
fn and_or_match_dense_semantics() {
    let ctx = BoolCtx::new();
    let vars: Vec<BoolRef> = (0..6).map(|_| ctx.variable()).collect();

    let dims = Dimensions::square(2, 2).unwrap();
    let mut a = BooleanMatrix::new(dims.clone(), &ctx);
    let mut b = BooleanMatrix::new(dims.clone(), &ctx);
    a.set(0, vars[0]).unwrap();
    a.set(1, vars[1]).unwrap();
    b.set(1, vars[2]).unwrap();
    b.set(2, vars[3]).unwrap();
    b.set(3, vars[4]).unwrap();

    let conj = a.and(&b).unwrap();
    let disj = a.or(&b).unwrap();

    for bit in 0u32..32 {
        let model: Vec<bool> = (0..5).map(|i| (bit >> i) & 1 == 1).collect();
        let ea = a.eval_dense(&model);
        let eb = b.eval_dense(&model);

        let want_and = dense_oracle(&ea, &eb, |x, y| x && y);
        let want_or = dense_oracle(&ea, &eb, |x, y| x || y);

        assert_eq!(conj.eval_dense(&model), want_and);
        assert_eq!(disj.eval_dense(&model), want_or);
    }
}

#[test]
fn choice_ite_composes_position_wise() {
    let ctx = BoolCtx::new();
    let cond = ctx.variable();
    let t = ctx.variable();
    let e = ctx.variable();

    let dims = Dimensions::square(2, 2).unwrap();
    let mut then_m = BooleanMatrix::new(dims.clone(), &ctx);
    let mut else_m = BooleanMatrix::new(dims.clone(), &ctx);
    then_m.set(0, t).unwrap();
    else_m.set(3, e).unwrap();

    let chosen = then_m.choice(cond, &else_m).unwrap();
    assert_eq!(chosen.density(), 2);

    for bit in 0u32..8 {
        let model: Vec<bool> = (0..3).map(|i| (bit >> i) & 1 == 1).collect();
        let (c, tv, ev) = (model[0], model[1], model[2]);
        let dense = chosen.eval_dense(&model);
        assert_eq!(dense[0], if c { tv } else { false });
        assert_eq!(dense[3], if c { false } else { ev });
    }

    let shortcut_true = then_m
        .choice(alloy_kodkod_rs::bool::const_true(), &else_m)
        .unwrap();
    assert_eq!(shortcut_true.density(), then_m.density());
}

#[test]
fn cross_product_conjoins_cells_and_skips_false() {
    let ctx = BoolCtx::new();
    let x = ctx.variable();
    let y = ctx.variable();

    let mut a = BooleanMatrix::new(Dimensions::square(2, 1).unwrap(), &ctx);
    let mut b = BooleanMatrix::new(Dimensions::square(2, 1).unwrap(), &ctx);
    a.set(0, x).unwrap();
    b.set(0, y).unwrap();
    b.set(1, ctx.or(&[y, ctx.not(y)])).unwrap();

    let cross = a.cross(&b).unwrap();
    assert_eq!(cross.dims(), &Dimensions::square(2, 2).unwrap());
    assert_eq!(cross.density(), 2);

    for xb in [false, true] {
        for yb in [false, true] {
            let model = [xb, yb];
            let dense = cross.eval_dense(&model);
            assert_eq!(dense[0], xb && yb);
            assert_eq!(dense[1], xb);
            assert!(!dense[2]);
            assert!(!dense[3]);
        }
    }
}

#[test]
fn transpose_swaps_rectangular_indices() {
    let ctx = BoolCtx::new();
    let v: Vec<BoolRef> = (0..6).map(|_| ctx.variable()).collect();
    let mut m = BooleanMatrix::new(Dimensions::rectangular(&[2, 3]).unwrap(), &ctx);
    for (i, &r) in v.iter().enumerate() {
        m.set(i, r).unwrap();
    }
    let t = m.transpose().unwrap();
    assert_eq!(t.dims(), &Dimensions::rectangular(&[3, 2]).unwrap());
    for i in 0..6usize {
        let swapped = (i % 3) * 2 + i / 3;
        assert_eq!(t.get(swapped), m.get(i));
    }
}

#[test]
fn dimension_and_index_mismatches_error() {
    let ctx = BoolCtx::new();
    let a = BooleanMatrix::new(Dimensions::square(2, 2).unwrap(), &ctx);
    let b = BooleanMatrix::new(Dimensions::square(3, 2).unwrap(), &ctx);
    assert!(matches!(a.and(&b), Err(MatrixError::DimMismatch)));

    let mut solo = BooleanMatrix::new(Dimensions::square(2, 1).unwrap(), &ctx);
    assert!(matches!(
        solo.set(9, ctx.variable()),
        Err(MatrixError::BadIndex(9))
    ));
}
