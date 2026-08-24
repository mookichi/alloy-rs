use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;

use crate::intset::IntSet;
use crate::relation::{RelationId, RelationPool};
use crate::tupleset::TupleSet;
use crate::universe::Universe;

#[derive(Debug, thiserror::Error)]
pub enum InstanceError {
    #[error("tuple set belongs to a different universe")]
    WrongUniverse,
    #[error("relation arity {relation} does not match tuple set arity {bound}")]
    ArityMismatch { relation: u32, bound: u32 },
    #[error("integer tuple set must be unary but got arity {0}")]
    IntBoundNotUnary(u32),
    #[error("integer tuple set must hold exactly one tuple but got {0}")]
    IntBoundNotSingleton(usize),
}

#[derive(Debug)]
pub struct Instance {
    universe: Arc<Universe>,
    pool: Arc<RelationPool>,
    order: Vec<RelationId>,
    tuples: HashMap<RelationId, TupleSet>,
    ints: BTreeMap<i64, TupleSet>,
}

impl Instance {
    pub fn new(universe: &Arc<Universe>, pool: &Arc<RelationPool>) -> Instance {
        Instance {
            universe: Arc::clone(universe),
            pool: Arc::clone(pool),
            order: Vec::new(),
            tuples: HashMap::new(),
            ints: BTreeMap::new(),
        }
    }

    pub fn universe(&self) -> &Arc<Universe> {
        &self.universe
    }

    pub fn pool(&self) -> &Arc<RelationPool> {
        &self.pool
    }

    pub fn contains(&self, r: RelationId) -> bool {
        self.tuples.contains_key(&r)
    }

    pub fn contains_int(&self, i: i64) -> bool {
        self.ints.contains_key(&i)
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
        self.ints.keys().copied().collect()
    }

    pub fn add(&mut self, r: RelationId, s: &TupleSet) -> Result<(), InstanceError> {
        if !s.universe().same(&self.universe) {
            return Err(InstanceError::WrongUniverse);
        }
        let rel_arity = self.pool.arity(r);
        if rel_arity != s.arity() {
            return Err(InstanceError::ArityMismatch {
                relation: rel_arity,
                bound: s.arity(),
            });
        }
        if !self.tuples.contains_key(&r) {
            self.order.push(r);
        }
        self.tuples.insert(r, s.clone());
        Ok(())
    }

    pub fn add_int(&mut self, i: i64, s: &TupleSet) -> Result<(), InstanceError> {
        if !s.universe().same(&self.universe) {
            return Err(InstanceError::WrongUniverse);
        }
        if s.arity() != 1 {
            return Err(InstanceError::IntBoundNotUnary(s.arity()));
        }
        if s.len() != 1 {
            return Err(InstanceError::IntBoundNotSingleton(s.len()));
        }
        self.ints.insert(i, s.clone());
        Ok(())
    }

    pub fn tuples(&self, r: RelationId) -> Option<&TupleSet> {
        self.tuples.get(&r)
    }

    pub fn relation_tuples(&self) -> impl Iterator<Item = (RelationId, &TupleSet)> {
        self.order
            .iter()
            .filter_map(|r| self.tuples.get(r).map(|ts| (*r, ts)))
    }

    pub fn int_tuple(&self, i: i64) -> Option<&TupleSet> {
        self.ints.get(&i)
    }

    pub fn int_tuples(&self) -> impl Iterator<Item = (i64, &TupleSet)> {
        self.ints.iter().map(|(k, v)| (*k, v))
    }

    pub fn find_relation_by_name(&self, name: &str) -> Option<RelationId> {
        self.order
            .iter()
            .copied()
            .find(|&r| self.pool.name(r).as_ref() == name)
    }
}

impl Clone for Instance {
    fn clone(&self) -> Self {
        Instance {
            universe: Arc::clone(&self.universe),
            pool: Arc::clone(&self.pool),
            order: self.order.clone(),
            tuples: self.tuples.clone(),
            ints: self.ints.clone(),
        }
    }
}

impl std::fmt::Display for Instance {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("relations:")?;
        for (r, ts) in self.relation_tuples() {
            writeln!(f, "\n {}->{}", self.pool.name(r), ts)?;
        }
        write!(f, "\nints:")?;
        for (i, ts) in &self.ints {
            write!(f, "\n {}->{}", i, ts)?;
        }
        Ok(())
    }
}
