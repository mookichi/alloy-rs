use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, RwLock};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct RelationId(pub u32);

#[derive(Debug)]
struct RelationData {
    name: Arc<str>,
    arity: u32,
    skolem: AtomicBool,
}

#[derive(Default, Debug)]
struct PoolInner {
    relations: Vec<RelationData>,
    index: HashMap<(String, u32), RelationId>,
}

#[derive(Default, Debug)]
pub struct RelationPool {
    inner: RwLock<PoolInner>,
}

impl RelationPool {
    pub fn new() -> RelationPool {
        RelationPool::default()
    }

    pub fn intern(&self, name: &str, arity: u32) -> RelationId {
        let key = (name.to_string(), arity);
        if let Some(id) = self.inner.read().unwrap().index.get(&key) {
            return *id;
        }
        let mut inner = self.inner.write().unwrap();
        if let Some(id) = inner.index.get(&key) {
            return *id;
        }
        let id = RelationId(inner.relations.len() as u32);
        inner.relations.push(RelationData {
            name: Arc::from(name),
            arity,
            skolem: AtomicBool::new(false),
        });
        inner.index.insert(key, id);
        id
    }

    pub fn name(&self, id: RelationId) -> Arc<str> {
        self.inner.read().unwrap().relations[id.0 as usize]
            .name
            .clone()
    }

    pub fn arity(&self, id: RelationId) -> u32 {
        self.inner.read().unwrap().relations[id.0 as usize].arity
    }

    pub fn set_skolem(&self, id: RelationId, value: bool) {
        self.inner.read().unwrap().relations[id.0 as usize]
            .skolem
            .store(value, Ordering::Relaxed);
    }

    pub fn is_skolem(&self, id: RelationId) -> bool {
        self.inner.read().unwrap().relations[id.0 as usize]
            .skolem
            .load(Ordering::Relaxed)
    }
}
