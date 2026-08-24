use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;

use crate::intset::IntSet;
use crate::relation::{RelationId, RelationPool};
use crate::tupleset::TupleSet;
use crate::universe::Universe;

#[derive(Debug, Clone)]
struct RelBound {
    lower: TupleSet,
    upper: TupleSet,
}

#[derive(Debug, thiserror::Error)]
pub enum BoundsError {
    #[error("bound arity mismatch: relation {relation} vs bound {bound}")]
    ArityMismatch { relation: u32, bound: u32 },
    #[error("bound belongs to a different universe")]
    WrongUniverse,
    #[error("lower bound is not contained in the upper bound")]
    LowerNotInUpper,
    #[error("integer bound must be unary but got arity {0}")]
    IntBoundNotUnary(u32),
    #[error("integer bound must hold exactly one tuple but got {0}")]
    IntBoundNotSingleton(usize),
}

#[derive(Debug)]
pub struct Bounds {
    universe: Arc<Universe>,
    pool: Arc<RelationPool>,
    order: Vec<RelationId>,
    entries: HashMap<RelationId, RelBound>,
    intbounds: BTreeMap<i64, TupleSet>,
}

impl Bounds {
    pub fn new(universe: &Arc<Universe>, pool: &Arc<RelationPool>) -> Bounds {
        Bounds {
            universe: Arc::clone(universe),
            pool: Arc::clone(pool),
            order: Vec::new(),
            entries: HashMap::new(),
            intbounds: BTreeMap::new(),
        }
    }

    pub fn universe(&self) -> &Arc<Universe> {
        &self.universe
    }

    pub fn pool(&self) -> &Arc<RelationPool> {
        &self.pool
    }

    pub fn relations(&self) -> impl Iterator<Item = RelationId> + '_ {
        self.order.iter().copied()
    }

    pub fn skolems(&self) -> Vec<RelationId> {
        self.order
            .iter()
            .copied()
            .filter(|&r| self.pool.is_skolem(r))
            .collect()
    }

    pub fn ints(&self) -> IntSet {
        self.intbounds.keys().copied().collect()
    }

    pub fn lower_bound(&self, r: RelationId) -> Option<&TupleSet> {
        self.entries.get(&r).map(|b| &b.lower)
    }

    pub fn upper_bound(&self, r: RelationId) -> Option<&TupleSet> {
        self.entries.get(&r).map(|b| &b.upper)
    }

    pub fn bound_pair(&self, r: RelationId) -> Option<(&TupleSet, &TupleSet)> {
        self.entries.get(&r).map(|b| (&b.lower, &b.upper))
    }

    pub fn exact_int_bound(&self, i: i64) -> Option<&TupleSet> {
        self.intbounds.get(&i)
    }

    pub fn int_bounds(&self) -> impl Iterator<Item = (i64, &TupleSet)> {
        self.intbounds.iter().map(|(k, v)| (*k, v))
    }

    fn check_bound(&self, r: RelationId, bound: &TupleSet) -> Result<(), BoundsError> {
        let rel_arity = self.pool.arity(r);
        if rel_arity != bound.arity() {
            return Err(BoundsError::ArityMismatch {
                relation: rel_arity,
                bound: bound.arity(),
            });
        }
        if !bound.universe().same(&self.universe) {
            return Err(BoundsError::WrongUniverse);
        }
        Ok(())
    }

    fn store(&mut self, r: RelationId, lower: TupleSet, upper: TupleSet) {
        if !self.entries.contains_key(&r) {
            self.order.push(r);
        }
        self.entries.insert(r, RelBound { lower, upper });
    }

    pub fn bound_exactly(&mut self, r: RelationId, tuples: &TupleSet) -> Result<(), BoundsError> {
        self.check_bound(r, tuples)?;
        let both = tuples.clone();
        self.store(r, both.clone(), both);
        Ok(())
    }

    pub fn bound(
        &mut self,
        r: RelationId,
        lower: &TupleSet,
        upper: &TupleSet,
    ) -> Result<(), BoundsError> {
        self.check_bound(r, lower)?;
        self.check_bound(r, upper)?;
        if !upper.covers(lower) {
            return Err(BoundsError::LowerNotInUpper);
        }
        if upper.len() == lower.len() {
            return self.bound_exactly(r, lower);
        }
        self.store(r, lower.clone(), upper.clone());
        Ok(())
    }

    pub fn bound_upper(&mut self, r: RelationId, upper: &TupleSet) -> Result<(), BoundsError> {
        self.check_bound(r, upper)?;
        let lower = TupleSet::new(&self.universe, upper.arity()).map_err(|_| {
            BoundsError::ArityMismatch {
                relation: 0,
                bound: 0,
            }
        })?;
        self.store(r, lower, upper.clone());
        Ok(())
    }

    pub fn bound_exactly_int(&mut self, i: i64, tuples: &TupleSet) -> Result<(), BoundsError> {
        if tuples.arity() != 1 {
            return Err(BoundsError::IntBoundNotUnary(tuples.arity()));
        }
        if tuples.len() != 1 {
            return Err(BoundsError::IntBoundNotSingleton(tuples.len()));
        }
        if !tuples.universe().same(&self.universe) {
            return Err(BoundsError::WrongUniverse);
        }
        self.intbounds.insert(i, tuples.clone());
        Ok(())
    }

    pub fn unbind(&mut self, r: RelationId) -> bool {
        let removed = self.entries.remove(&r).is_some();
        if removed {
            self.order.retain(|&x| x != r);
        }
        removed
    }

    pub fn unbind_int(&mut self, i: i64) -> bool {
        self.intbounds.remove(&i).is_some()
    }
}

impl Clone for Bounds {
    fn clone(&self) -> Self {
        Bounds {
            universe: Arc::clone(&self.universe),
            pool: Arc::clone(&self.pool),
            order: self.order.clone(),
            entries: self.entries.clone(),
            intbounds: self.intbounds.clone(),
        }
    }
}

impl std::fmt::Display for Bounds {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("relation bounds:")?;
        for r in &self.order {
            let name = self.pool.name(*r);
            if let Some(b) = self.entries.get(r) {
                writeln!(f, "\n {}: [{}, {}]", name, b.lower, b.upper)?;
            }
        }
        write!(f, "\nint bounds:")?;
        for (i, ts) in &self.intbounds {
            write!(f, "\n {}->{}", i, ts)?;
        }
        Ok(())
    }
}
