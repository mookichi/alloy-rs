use crate::intset::Int;
use crate::tupleset::{check_capacity, CapacityError};
use crate::universe::{Universe, UniverseError};
use std::sync::Arc;

#[derive(Clone, Debug)]
pub struct Tuple {
    universe: Arc<Universe>,
    arity: u32,
    index: Int,
}

#[derive(Debug, thiserror::Error)]
pub enum BuildError {
    #[error(transparent)]
    Capacity(#[from] CapacityError),
    #[error(transparent)]
    Universe(#[from] UniverseError),
    #[error("index overflow")]
    Overflow,
}

impl Tuple {
    pub(crate) fn new(universe: Arc<Universe>, arity: u32, index: Int) -> Tuple {
        Tuple {
            universe,
            arity,
            index,
        }
    }

    pub fn from_atoms(universe: &Arc<Universe>, atoms: &[&str]) -> Result<Tuple, BuildError> {
        let arity = atoms.len() as u32;
        let base = universe.size() as Int;
        check_capacity(base, arity)?;
        let mut index: Int = 0;
        for atom in atoms {
            let i = universe.index(atom)? as Int;
            index = index
                .checked_mul(base)
                .and_then(|v| v.checked_add(i))
                .ok_or(BuildError::Overflow)?;
        }
        Ok(Tuple::new(Arc::clone(universe), arity, index))
    }

    pub fn universe(&self) -> &Arc<Universe> {
        &self.universe
    }

    pub fn arity(&self) -> u32 {
        self.arity
    }

    pub fn index(&self) -> Int {
        self.index
    }

    pub fn atom_index(&self, i: u32) -> Result<u32, AtomIndexError> {
        if i >= self.arity {
            return Err(AtomIndexError(i));
        }
        let base = self.universe.size() as Int;
        let div = pow(base, self.arity - 1 - i);
        Ok((self.index / div % base) as u32)
    }

    pub fn atom(&self, i: u32) -> Result<String, AtomAccessError> {
        let idx = self.atom_index(i)?;
        match self.universe.atom(idx as usize) {
            Ok(a) => Ok(a.to_string()),
            Err(e) => Err(AtomAccessError::Universe(e)),
        }
    }

    pub fn contains(&self, atom: &str) -> bool {
        let Ok(target) = self.universe.index(atom) else {
            return false;
        };
        (0..self.arity).any(|i| self.atom_index(i).map(|d| d == target).unwrap_or(false))
    }

    pub fn product(&self, other: &Tuple) -> Result<Tuple, ProductError> {
        if !self.universe.same(&other.universe) {
            return Err(ProductError::DifferentUniverses);
        }
        let base = self.universe.size() as Int;
        let shift = pow(base, other.arity);
        let index = self
            .index
            .checked_mul(shift)
            .and_then(|v| v.checked_add(other.index))
            .ok_or(ProductError::Overflow)?;
        Ok(Tuple::new(
            Arc::clone(&self.universe),
            self.arity + other.arity,
            index,
        ))
    }
}

impl PartialEq for Tuple {
    fn eq(&self, other: &Self) -> bool {
        self.universe.same(&other.universe)
            && self.arity == other.arity
            && self.index == other.index
    }
}

impl Eq for Tuple {}

impl std::fmt::Display for Tuple {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        for i in 0..self.arity {
            if i > 0 {
                write!(f, ", ")?;
            }
            match self.atom(i) {
                Ok(a) => write!(f, "{}", a)?,
                Err(_) => write!(f, "?")?,
            }
        }
        write!(f, "]")
    }
}

pub(crate) fn pow(base: Int, exp: u32) -> Int {
    let mut result: Int = 1;
    let mut b = base;
    let mut e = exp;
    while e > 0 {
        if e & 1 == 1 {
            result *= b;
        }
        b *= b;
        e >>= 1;
    }
    result
}

#[derive(Debug, thiserror::Error)]
#[error("atom index {0} out of range")]
pub struct AtomIndexError(pub u32);

#[derive(Debug, thiserror::Error)]
pub enum AtomAccessError {
    #[error(transparent)]
    Index(#[from] AtomIndexError),
    #[error(transparent)]
    Universe(#[from] UniverseError),
}

#[derive(Debug, thiserror::Error)]
pub enum ProductError {
    #[error("tuple universes differ")]
    DifferentUniverses,
    #[error("tuple product overflow")]
    Overflow,
}
