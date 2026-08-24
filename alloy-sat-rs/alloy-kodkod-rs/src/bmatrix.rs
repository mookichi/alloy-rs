use std::cell::RefCell;
use std::collections::BTreeMap;
use std::rc::Rc;

use crate::bool::{const_false, const_true, BoolFactory, BoolRef};
use crate::dimensions::{Dimensions, DimsError};

#[derive(Clone)]
pub struct BoolCtx {
    factory: Rc<RefCell<BoolFactory>>,
}

impl std::fmt::Debug for BoolCtx {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BoolCtx")
            .field("slots", &self.factory.borrow().num_slots())
            .finish()
    }
}

impl Default for BoolCtx {
    fn default() -> Self {
        Self::new()
    }
}

impl BoolCtx {
    pub fn new() -> BoolCtx {
        BoolCtx {
            factory: Rc::new(RefCell::new(BoolFactory::new())),
        }
    }

    pub fn variable(&self) -> BoolRef {
        self.factory.borrow_mut().variable()
    }

    pub fn and(&self, inputs: &[BoolRef]) -> BoolRef {
        self.factory.borrow_mut().and(inputs)
    }

    pub fn or(&self, inputs: &[BoolRef]) -> BoolRef {
        self.factory.borrow_mut().or(inputs)
    }

    pub fn not(&self, r: BoolRef) -> BoolRef {
        self.factory.borrow().not(r)
    }

    pub fn ite(&self, c: BoolRef, t: BoolRef, e: BoolRef) -> BoolRef {
        self.factory.borrow_mut().ite(c, t, e)
    }

    pub fn eval(&self, r: BoolRef, model: &[bool]) -> bool {
        self.factory.borrow().eval(r, model)
    }

    pub fn with_factory<T>(&self, f: impl FnOnce(&BoolFactory) -> T) -> T {
        f(&self.factory.borrow())
    }

    pub fn is_true(&self, r: BoolRef) -> bool {
        r == const_true()
    }

    pub fn is_false(&self, r: BoolRef) -> bool {
        r == const_false()
    }

    pub fn num_slots(&self) -> usize {
        self.factory.borrow().num_slots()
    }
}

#[derive(Debug, thiserror::Error)]
pub enum MatrixError {
    #[error("incompatible dimensions")]
    DimMismatch,
    #[error("operation needs a 2-dimensional matrix")]
    Not2D,
    #[error("index {0} out of range")]
    BadIndex(u64),
}

#[derive(Clone, Debug)]
pub struct BooleanMatrix {
    dims: Dimensions,
    ctx: BoolCtx,
    cells: BTreeMap<usize, BoolRef>,
}

impl BooleanMatrix {
    pub fn new(dims: Dimensions, ctx: &BoolCtx) -> BooleanMatrix {
        BooleanMatrix {
            dims,
            ctx: ctx.clone(),
            cells: BTreeMap::new(),
        }
    }

    pub fn dims(&self) -> &Dimensions {
        &self.dims
    }

    pub fn ctx(&self) -> &BoolCtx {
        &self.ctx
    }

    pub fn density(&self) -> usize {
        self.cells.len()
    }

    pub fn set(&mut self, index: usize, value: BoolRef) -> Result<(), MatrixError> {
        if !self.dims.validate_flat(index) {
            return Err(MatrixError::BadIndex(index as u64));
        }
        self.cells.insert(index, value);
        Ok(())
    }

    pub fn get(&self, index: usize) -> Option<BoolRef> {
        self.cells.get(&index).copied()
    }

    pub fn iter(&self) -> impl Iterator<Item = (usize, BoolRef)> + '_ {
        self.cells.iter().map(|(&k, &v)| (k, v))
    }

    pub fn not(&self) -> BooleanMatrix {
        let mut neg = BooleanMatrix::new(self.dims.clone(), &self.ctx);
        for i in 0..self.dims.capacity() {
            match self.get(i) {
                None => {
                    neg.cells.insert(i, const_true());
                }
                Some(v) => {
                    if v != const_true() {
                        neg.cells.insert(i, self.ctx.not(v));
                    }
                }
            }
        }
        neg
    }

    fn check_same_dims(&self, other: &BooleanMatrix) -> Result<(), MatrixError> {
        if self.dims != other.dims {
            return Err(MatrixError::DimMismatch);
        }
        Ok(())
    }

    pub fn and(&self, other: &BooleanMatrix) -> Result<BooleanMatrix, MatrixError> {
        self.check_same_dims(other)?;
        let mut ret = BooleanMatrix::new(self.dims.clone(), &self.ctx);
        if self.cells.is_empty() || other.cells.is_empty() {
            return Ok(ret);
        }
        for (&i, &v0) in &self.cells {
            if let Some(v1) = other.get(i) {
                let conj = self.ctx.and(&[v0, v1]);
                ret.cells.insert(i, conj);
            }
        }
        Ok(ret)
    }

    pub fn or(&self, other: &BooleanMatrix) -> Result<BooleanMatrix, MatrixError> {
        self.check_same_dims(other)?;
        if self.cells.is_empty() {
            return Ok(other.clone());
        }
        if other.cells.is_empty() {
            return Ok(self.clone());
        }
        let mut ret = BooleanMatrix::new(self.dims.clone(), &self.ctx);
        for (&i, &v0) in &self.cells {
            match other.get(i) {
                None => {
                    ret.cells.insert(i, v0);
                }
                Some(v1) => {
                    ret.cells.insert(i, self.ctx.or(&[v0, v1]));
                }
            }
        }
        for (&i, &v1) in &other.cells {
            if !self.cells.contains_key(&i) {
                ret.cells.insert(i, v1);
            }
        }
        Ok(ret)
    }

    pub fn choice(
        &self,
        condition: BoolRef,
        other: &BooleanMatrix,
    ) -> Result<BooleanMatrix, MatrixError> {
        self.check_same_dims(other)?;
        if condition == const_true() {
            return Ok(self.clone());
        }
        if condition == const_false() {
            return Ok(other.clone());
        }
        let mut ret = BooleanMatrix::new(self.dims.clone(), &self.ctx);
        for (&i, &v0) in &self.cells {
            match other.get(i) {
                None => {
                    ret.cells.insert(i, self.ctx.and(&[condition, v0]));
                }
                Some(v1) => {
                    ret.cells.insert(i, self.ctx.ite(condition, v0, v1));
                }
            }
        }
        for (&i, &v1) in &other.cells {
            if !self.cells.contains_key(&i) {
                ret.cells
                    .insert(i, self.ctx.and(&[self.ctx.not(condition), v1]));
            }
        }
        Ok(ret)
    }

    pub fn cross(&self, other: &BooleanMatrix) -> Result<BooleanMatrix, MatrixError> {
        let dims = self
            .dims
            .cross(&other.dims)
            .map_err(|_: DimsError| MatrixError::Not2D)?;
        let mut ret = BooleanMatrix::new(dims, &self.ctx);
        let ocap = other.dims.capacity();
        for (&i, &v0) in &self.cells {
            let base = ocap * i;
            for (&j, &v1) in &other.cells {
                let conj = self.ctx.and(&[v0, v1]);
                if conj != const_false() {
                    ret.cells.insert(base + j, conj);
                }
            }
        }
        Ok(ret)
    }

    pub fn transpose(&self) -> Result<BooleanMatrix, MatrixError> {
        let rows = self.dims.dimension(0).ok_or(MatrixError::Not2D)? as usize;
        let cols = self.dims.dimension(1).ok_or(MatrixError::Not2D)? as usize;
        let dims = self.dims.transpose().map_err(|_| MatrixError::Not2D)?;
        let mut ret = BooleanMatrix::new(dims, &self.ctx);
        for (&i, &v) in &self.cells {
            let swapped = (i % cols) * rows + i / cols;
            ret.cells.insert(swapped, v);
        }
        Ok(ret)
    }

    pub fn join(&self, other: &BooleanMatrix) -> Result<BooleanMatrix, MatrixError> {
        let an = self.dims.num_dimensions();
        let bn = other.dims.num_dimensions();
        if an == 0 || bn == 0 {
            return Err(MatrixError::Not2D);
        }
        let l = self.dims.dimension(an - 1).ok_or(MatrixError::Not2D)?;
        if l != other.dims.dimension(0).unwrap_or(l + 1) {
            return Err(MatrixError::DimMismatch);
        }
        let l = l as usize;
        let b_rest = other.dims.capacity() / l;
        let mut joined: Vec<u32> = (0..an - 1).filter_map(|k| self.dims.dimension(k)).collect();
        for k in 1..bn {
            joined.push(other.dims.dimension(k).ok_or(MatrixError::Not2D)?);
        }
        let dims = Dimensions::rectangular(&joined).map_err(|_| MatrixError::Not2D)?;

        let mut acc: BTreeMap<usize, Vec<BoolRef>> = BTreeMap::new();
        for (&i, &v0) in &self.cells {
            let prefix = i / l;
            let last = i % l;
            for (&j, &v1) in &other.cells {
                if j / b_rest != last {
                    continue;
                }
                let conj = self.ctx.and(&[v0, v1]);
                if conj != const_false() {
                    acc.entry(prefix * b_rest + j % b_rest)
                        .or_default()
                        .push(conj);
                }
            }
        }
        let mut ret = BooleanMatrix::new(dims, &self.ctx);
        for (idx, terms) in acc {
            ret.cells.insert(idx, self.ctx.or(&terms));
        }
        Ok(ret)
    }

    pub fn override_values(&self, other: &BooleanMatrix) -> Result<BooleanMatrix, MatrixError> {
        self.check_same_dims(other)?;
        if other.cells.is_empty() {
            return Ok(self.clone());
        }
        let mut ret = BooleanMatrix::new(self.dims.clone(), &self.ctx);
        ret.cells.extend(other.cells.iter().map(|(&k, &v)| (k, v)));
        let row_length = self.dims.capacity() / self.dims.dimension(0).unwrap_or(1) as usize;
        let mut current_row: Option<usize> = None;
        let mut row_val = const_true();
        for (&i, &v) in &self.cells {
            let row = i / row_length;
            if current_row != Some(row) {
                current_row = Some(row);
                let start = row * row_length;
                let end = start + row_length;
                let mut terms = Vec::new();
                for j in start..end {
                    if let Some(oj) = other.get(j) {
                        terms.push(oj);
                    }
                }
                row_val = self.ctx.not(self.ctx.or(&terms));
            }
            let base = ret.get(i).unwrap_or(const_false());
            let merged = self.ctx.or(&[base, self.ctx.and(&[v, row_val])]);
            ret.cells.insert(i, merged);
        }
        Ok(ret)
    }

    pub fn closure_transitive(&self) -> Result<BooleanMatrix, MatrixError> {
        if self.dims.num_dimensions() != 2 || !self.dims.is_square() {
            return Err(MatrixError::Not2D);
        }
        let n = self.dims.dimension(0).unwrap_or(1) as usize;
        let mut acc = self.clone();
        let mut cur = self.clone();
        for _ in 1..n {
            cur = cur.join(&cur)?;
            acc = acc.or(&cur)?;
        }
        Ok(acc)
    }

    pub fn eval_dense(&self, model: &[bool]) -> Vec<bool> {
        self.ctx.with_factory(|factory| {
            let mut memo: Vec<Option<bool>> = Vec::new();
            (0..self.dims.capacity())
                .map(|i| {
                    self.get(i)
                        .map(|v| factory.eval_memo(v, model, &mut memo))
                        .unwrap_or(false)
                })
                .collect()
        })
    }
}
