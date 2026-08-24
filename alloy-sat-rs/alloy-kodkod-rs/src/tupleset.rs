use crate::intset::{Int, IntSet};
use crate::tuple::Tuple;
use crate::universe::Universe;
use std::sync::Arc;

#[derive(Debug, thiserror::Error)]
#[error("capacity exceeded")]
pub struct CapacityError(pub ());

pub(crate) fn pow_checked(base: Int, exp: u32) -> Result<Int, CapacityError> {
    let mut result: Int = 1;
    for _ in 0..exp {
        result = result.checked_mul(base).ok_or(CapacityError(()))?;
    }
    Ok(result)
}

pub(crate) fn check_capacity(base: Int, arity: u32) -> Result<Int, CapacityError> {
    if arity == 0 || base < 1 {
        return Err(CapacityError(()));
    }
    pow_checked(base, arity)
}

#[derive(Clone, Debug)]
pub struct TupleSet {
    universe: Arc<Universe>,
    arity: u32,
    tuples: IntSet,
}

impl TupleSet {
    pub(crate) fn with_capacity_set(
        universe: Arc<Universe>,
        arity: u32,
        tuples: IntSet,
    ) -> TupleSet {
        TupleSet {
            universe,
            arity,
            tuples,
        }
    }

    pub fn new(universe: &Arc<Universe>, arity: u32) -> Result<TupleSet, CapacityError> {
        let base = universe.size() as Int;
        check_capacity(base, arity)?;
        Ok(TupleSet::with_capacity_set(
            Arc::clone(universe),
            arity,
            IntSet::new(),
        ))
    }

    pub fn universe(&self) -> &Arc<Universe> {
        &self.universe
    }

    pub fn arity(&self) -> u32 {
        self.arity
    }

    pub fn capacity(&self) -> Result<Int, CapacityError> {
        check_capacity(self.universe.size() as Int, self.arity)
    }

    pub fn index_view(&self) -> &IntSet {
        &self.tuples
    }

    pub fn from_indices(
        universe: &Arc<Universe>,
        arity: u32,
        indices: IntSet,
    ) -> Result<TupleSet, CapacityError> {
        let base = check_capacity(universe.size() as Int, arity)?;
        if let Some(max) = indices.max() {
            if max >= base {
                return Err(CapacityError(()));
            }
        }
        Ok(TupleSet::with_capacity_set(
            Arc::clone(universe),
            arity,
            indices,
        ))
    }

    pub fn dims_vector(&self, index: usize) -> Option<Vec<u32>> {
        let dims =
            crate::dimensions::Dimensions::square(self.universe.size() as u32, self.arity).ok()?;
        dims.vector_of(index)
    }

    pub fn len(&self) -> usize {
        self.tuples.len()
    }

    pub fn is_empty(&self) -> bool {
        self.tuples.is_empty()
    }

    pub fn contains_index(&self, index: Int) -> bool {
        self.tuples.contains(index)
    }

    pub fn contains(&self, tuple: &Tuple) -> bool {
        self.arity == tuple.arity()
            && self.universe.same(tuple.universe())
            && self.tuples.contains(tuple.index())
    }

    pub fn covers(&self, other: &TupleSet) -> bool {
        self.arity == other.arity
            && self.universe.same(&other.universe)
            && self.tuples.contains_all(other.index_view())
    }

    pub fn insert_index(&mut self, index: Int) -> bool {
        self.tuples.insert(index)
    }

    pub fn insert(&mut self, tuple: &Tuple) -> Result<bool, ArityMismatch> {
        self.check_same(tuple)?;
        Ok(self.tuples.insert(tuple.index()))
    }

    pub fn remove(&mut self, tuple: &Tuple) -> Result<bool, ArityMismatch> {
        self.check_same(tuple)?;
        Ok(self.tuples.remove(tuple.index()))
    }

    pub fn product(&self, other: &TupleSet) -> Result<TupleSet, ProductError> {
        if !self.universe.same(&other.universe) {
            return Err(ProductError::DifferentUniverses);
        }
        let m_capacity = other.capacity().map_err(|_| ProductError::Overflow)?;
        let mut tuples = IntSet::new();
        if !other.is_empty() {
            for i0 in self.tuples.iter() {
                let scaled = i0.checked_mul(m_capacity).ok_or(ProductError::Overflow)?;
                for i1 in other.tuples.iter() {
                    let idx = scaled.checked_add(i1).ok_or(ProductError::Overflow)?;
                    tuples.insert(idx);
                }
            }
        }
        Ok(TupleSet::with_capacity_set(
            Arc::clone(&self.universe),
            self.arity + other.arity,
            tuples,
        ))
    }

    pub fn project(&self, dimension: u32) -> Result<TupleSet, ProjectError> {
        if dimension >= self.arity {
            return Err(ProjectError::BadDimension(dimension));
        }
        let base = self.universe.size() as Int;
        let div = crate::tuple::pow(base, self.arity - 1 - dimension);
        let mut projection = IntSet::new();
        for idx in self.tuples.iter() {
            projection.insert((idx / div % base) as u32 as Int);
        }
        Ok(TupleSet::with_capacity_set(
            Arc::clone(&self.universe),
            1,
            projection,
        ))
    }

    pub fn range(
        universe: &Arc<Universe>,
        from: &Tuple,
        to: &Tuple,
    ) -> Result<TupleSet, RangeError> {
        if from.arity() != to.arity() {
            return Err(RangeError::ArityMismatch);
        }
        if !universe.same(from.universe()) || !universe.same(to.universe()) {
            return Err(RangeError::DifferentUniverses);
        }
        if from.index() > to.index() {
            return Err(RangeError::Inverted);
        }
        let arity = from.arity();
        let mut set = TupleSet::new(universe, arity).map_err(|_| RangeError::Capacity)?;
        for idx in from.index()..=to.index() {
            set.insert_index(idx);
        }
        Ok(set)
    }

    fn check_same(&self, tuple: &Tuple) -> Result<(), ArityMismatch> {
        if self.arity != tuple.arity() {
            return Err(ArityMismatch);
        }
        Ok(())
    }
}

impl PartialEq for TupleSet {
    fn eq(&self, other: &Self) -> bool {
        self.arity == other.arity
            && self.universe.same(&other.universe)
            && self.tuples == other.tuples
    }
}

impl Eq for TupleSet {}

impl std::fmt::Display for TupleSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("[")?;
        for (i, idx) in self.tuples.iter().enumerate() {
            if i > 0 {
                f.write_str(", ")?;
            }
            let t = Tuple::new(Arc::clone(&self.universe), self.arity, idx);
            write!(f, "{}", t)?;
        }
        f.write_str("]")
    }
}

#[derive(Debug, thiserror::Error)]
#[error("arity mismatch")]
pub struct ArityMismatch;

#[derive(Debug, thiserror::Error)]
pub enum ProductError {
    #[error("tuple set universes differ")]
    DifferentUniverses,
    #[error("product overflow")]
    Overflow,
}

#[derive(Debug, thiserror::Error)]
pub enum ProjectError {
    #[error("dimension {0} out of range")]
    BadDimension(u32),
}

#[derive(Debug, thiserror::Error)]
pub enum RangeError {
    #[error("arity mismatch")]
    ArityMismatch,
    #[error("universes differ")]
    DifferentUniverses,
    #[error("from.index > to.index")]
    Inverted,
    #[error("capacity exceeded")]
    Capacity,
}
