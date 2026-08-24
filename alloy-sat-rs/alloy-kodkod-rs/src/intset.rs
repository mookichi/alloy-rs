use std::cmp::Ordering;

pub type Int = i64;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct IntSet {
    items: Vec<Int>,
}

impl IntSet {
    pub fn new() -> Self {
        IntSet { items: Vec::new() }
    }

    pub fn len(&self) -> usize {
        self.items.len()
    }

    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    pub fn contains(&self, value: Int) -> bool {
        self.items.binary_search(&value).is_ok()
    }

    pub fn insert(&mut self, value: Int) -> bool {
        match self.items.binary_search(&value) {
            Ok(_) => false,
            Err(pos) => {
                self.items.insert(pos, value);
                true
            }
        }
    }

    pub fn remove(&mut self, value: Int) -> bool {
        match self.items.binary_search(&value) {
            Ok(pos) => {
                self.items.remove(pos);
                true
            }
            Err(_) => false,
        }
    }

    pub fn min(&self) -> Option<Int> {
        self.items.first().copied()
    }

    pub fn max(&self) -> Option<Int> {
        self.items.last().copied()
    }

    pub fn iter(&self) -> impl Iterator<Item = Int> + '_ {
        self.items.iter().copied()
    }

    pub fn union(&self, other: &IntSet) -> IntSet {
        let mut items = Vec::with_capacity(self.len() + other.len());
        merge_union(&self.items, &other.items, &mut items);
        IntSet { items }
    }

    pub fn intersection(&self, other: &IntSet) -> IntSet {
        let mut items = Vec::new();
        merge_intersection(&self.items, &other.items, &mut items);
        IntSet { items }
    }

    pub fn difference(&self, other: &IntSet) -> IntSet {
        let mut items = Vec::new();
        merge_difference(&self.items, &other.items, &mut items);
        IntSet { items }
    }

    pub fn contains_all(&self, other: &IntSet) -> bool {
        if other.len() > self.len() {
            return false;
        }
        let mut iter = self.items.iter();
        for &value in &other.items {
            match iter.find(|&&candidate| candidate >= value) {
                Some(&found) if found == value => {}
                _ => return false,
            }
        }
        true
    }

    pub fn add_all(&mut self, other: &IntSet) -> bool {
        let before = self.len();
        *self = self.union(other);
        self.len() != before
    }

    pub fn remove_all(&mut self, other: &IntSet) -> bool {
        let mut changed = false;
        let mut result = Vec::with_capacity(self.len());
        for &value in &self.items {
            if other.contains(value) {
                changed = true;
            } else {
                result.push(value);
            }
        }
        if changed {
            self.items = result;
        }
        changed
    }
}

impl FromIterator<Int> for IntSet {
    fn from_iter<I: IntoIterator<Item = Int>>(iter: I) -> Self {
        let mut set = IntSet::new();
        for value in iter {
            set.insert(value);
        }
        set
    }
}

fn merge_union(a: &[Int], b: &[Int], out: &mut Vec<Int>) {
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        match a[i].cmp(&b[j]) {
            Ordering::Less => {
                out.push(a[i]);
                i += 1;
            }
            Ordering::Greater => {
                out.push(b[j]);
                j += 1;
            }
            Ordering::Equal => {
                out.push(a[i]);
                i += 1;
                j += 1;
            }
        }
    }
    out.extend_from_slice(&a[i..]);
    out.extend_from_slice(&b[j..]);
}

fn merge_intersection(a: &[Int], b: &[Int], out: &mut Vec<Int>) {
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        match a[i].cmp(&b[j]) {
            Ordering::Less => i += 1,
            Ordering::Greater => j += 1,
            Ordering::Equal => {
                out.push(a[i]);
                i += 1;
                j += 1;
            }
        }
    }
}

fn merge_difference(a: &[Int], b: &[Int], out: &mut Vec<Int>) {
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        match a[i].cmp(&b[j]) {
            Ordering::Less => {
                out.push(a[i]);
                i += 1;
            }
            Ordering::Greater => j += 1,
            Ordering::Equal => {
                i += 1;
                j += 1;
            }
        }
    }
    out.extend_from_slice(&a[i..]);
}
