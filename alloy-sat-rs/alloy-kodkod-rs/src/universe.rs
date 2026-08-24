use std::collections::HashMap;
use std::sync::Arc;

#[derive(Debug, thiserror::Error)]
pub enum UniverseError {
    #[error("cannot create an empty universe")]
    Empty,
    #[error("atom `{0}` appears multiple times")]
    Duplicate(String),
    #[error("no such atom in the universe: {0}")]
    NoSuchAtom(String),
    #[error("invalid universe index: {0}")]
    BadIndex(usize),
}

#[derive(Debug)]
pub struct Universe {
    atoms: Vec<Arc<str>>,
    indices: HashMap<Arc<str>, u32>,
}

impl Universe {
    pub fn new<I, S>(atoms: I) -> Result<Arc<Universe>, UniverseError>
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        let atoms: Vec<Arc<str>> = atoms.into_iter().map(|a| Arc::from(a.as_ref())).collect();
        if atoms.is_empty() {
            return Err(UniverseError::Empty);
        }
        let mut indices = HashMap::with_capacity(atoms.len());
        for (i, atom) in atoms.iter().enumerate() {
            if indices.contains_key(atom) {
                return Err(UniverseError::Duplicate(atom.to_string()));
            }
            indices.insert(Arc::clone(atom), i as u32);
        }
        Ok(Arc::new(Universe { atoms, indices }))
    }

    pub fn size(&self) -> usize {
        self.atoms.len()
    }

    pub fn contains(&self, atom: &str) -> bool {
        self.indices.contains_key(atom)
    }

    pub fn atom(&self, index: usize) -> Result<&Arc<str>, UniverseError> {
        self.atoms.get(index).ok_or(UniverseError::BadIndex(index))
    }

    pub fn index(&self, atom: &str) -> Result<u32, UniverseError> {
        self.indices
            .get(atom)
            .copied()
            .ok_or_else(|| UniverseError::NoSuchAtom(atom.to_string()))
    }

    pub fn iter(&self) -> impl Iterator<Item = &Arc<str>> {
        self.atoms.iter()
    }

    pub fn same(&self, other: &Universe) -> bool {
        std::ptr::eq(self, other)
    }
}
