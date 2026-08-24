//! Integer set with an automatic sparse/dense representation (backlog 5).
//!
//! * `Sparse` — sorted `Vec<i64>`; best for small or very sparse index sets
//!   (typical for relation bounds).
//! * `Dense`  — `Vec<u64>` bitset; best for large, dense index spaces such as
//!   full product bounds (`upper_bound × states`).
//!
//! The representation switches automatically: bulk construction promotes to
//! dense when the values are small enough and reasonably dense, and set
//! operations produce dense results whenever both sides are densifiable.
//! Values above [`DENSE_MAX`] always fall back to the sparse form so that
//! huge tuple indices can never allocate a giant bitset.

use std::cmp::Ordering;

pub type Int = i64;

/// Largest value representable in the dense representation.
const DENSE_MAX: Int = 1 << 22;
/// Minimum element count before a sparse set promotes to dense.
const DENSE_MIN_LEN: usize = 256;

#[derive(Clone, Debug)]
enum Rep {
    S(Vec<Int>),
    D(Dense),
}

#[derive(Clone, Debug, Default)]
struct Dense {
    bits: Vec<u64>,
    len: usize,
}

impl Dense {
    fn new() -> Dense {
        Dense {
            bits: Vec::new(),
            len: 0,
        }
    }

    fn words_for(value: Int) -> usize {
        (value as usize) / 64 + 1
    }

    fn ensure(&mut self, value: Int) {
        let need = Self::words_for(value);
        if self.bits.len() < need {
            self.bits.resize(need, 0);
        }
    }

    fn insert(&mut self, value: Int) -> bool {
        self.ensure(value);
        let w = (value as usize) / 64;
        let mask = 1u64 << (value % 64);
        if self.bits[w] & mask == 0 {
            self.bits[w] |= mask;
            self.len += 1;
            true
        } else {
            false
        }
    }

    fn remove(&mut self, value: Int) -> bool {
        let w = (value as usize) / 64;
        if w >= self.bits.len() {
            return false;
        }
        let mask = 1u64 << (value % 64);
        if self.bits[w] & mask != 0 {
            self.bits[w] &= !mask;
            self.len -= 1;
            true
        } else {
            false
        }
    }

    fn contains(&self, value: Int) -> bool {
        let w = (value as usize) / 64;
        w < self.bits.len() && (self.bits[w] >> (value % 64)) & 1 == 1
    }

    fn min(&self) -> Option<Int> {
        for (wi, word) in self.bits.iter().enumerate() {
            if *word != 0 {
                return Some((wi * 64 + word.trailing_zeros() as usize) as Int);
            }
        }
        None
    }

    fn max(&self) -> Option<Int> {
        for (wi, word) in self.bits.iter().enumerate().rev() {
            if *word != 0 {
                return Some((wi * 64 + (63 - word.leading_zeros() as usize)) as Int);
            }
        }
        None
    }

    fn iter(&self) -> impl Iterator<Item = Int> + '_ {
        self.bits.iter().enumerate().flat_map(|(wi, &word)| {
            let base = (wi * 64) as Int;
            (0..64).filter_map(move |b| {
                if (word >> b) & 1 == 1 {
                    Some(base + b as Int)
                } else {
                    None
                }
            })
        })
    }
}

#[derive(Clone, Debug)]
pub struct IntSet {
    rep: Rep,
}

impl Default for IntSet {
    fn default() -> Self {
        IntSet {
            rep: Rep::S(Vec::new()),
        }
    }
}

fn densifiable(rep: &Rep) -> Option<()> {
    match rep {
        Rep::D(_) => Some(()),
        Rep::S(items) => {
            let max = *items.last()?;
            (max <= DENSE_MAX).then_some(())
        }
    }
}

fn as_dense(rep: &Rep) -> Dense {
    match rep {
        Rep::D(d) => d.clone(),
        Rep::S(items) => {
            let mut d = Dense::new();
            for &v in items {
                d.insert(v);
            }
            d
        }
    }
}

fn as_vec(rep: &Rep) -> Vec<Int> {
    match rep {
        Rep::S(v) => v.clone(),
        Rep::D(d) => d.iter().collect(),
    }
}

impl IntSet {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn len(&self) -> usize {
        match &self.rep {
            Rep::S(v) => v.len(),
            Rep::D(d) => d.len,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn contains(&self, value: Int) -> bool {
        match &self.rep {
            Rep::S(v) => v.binary_search(&value).is_ok(),
            Rep::D(d) => d.contains(value),
        }
    }

    pub fn insert(&mut self, value: Int) -> bool {
        match &mut self.rep {
            Rep::S(items) => {
                if value > DENSE_MAX
                    || (items.len() + 1 < DENSE_MIN_LEN)
                    || value > DENSE_MAX.min(items.last().map(|m| m * 64).unwrap_or(DENSE_MAX))
                {
                    match items.binary_search(&value) {
                        Ok(_) => false,
                        Err(pos) => {
                            items.insert(pos, value);
                            true
                        }
                    }
                } else {
                    let mut d = as_dense(&Rep::S(std::mem::take(items)));
                    let inserted = d.insert(value);
                    self.rep = Rep::D(d);
                    inserted
                }
            }
            Rep::D(d) => d.insert(value),
        }
    }

    pub fn remove(&mut self, value: Int) -> bool {
        match &mut self.rep {
            Rep::S(items) => match items.binary_search(&value) {
                Ok(pos) => {
                    items.remove(pos);
                    true
                }
                Err(_) => false,
            },
            Rep::D(d) => d.remove(value),
        }
    }

    pub fn min(&self) -> Option<Int> {
        match &self.rep {
            Rep::S(v) => v.first().copied(),
            Rep::D(d) => d.min(),
        }
    }

    pub fn max(&self) -> Option<Int> {
        match &self.rep {
            Rep::S(v) => v.last().copied(),
            Rep::D(d) => d.max(),
        }
    }

    pub fn iter(&self) -> std::boxed::Box<dyn Iterator<Item = Int> + '_> {
        match &self.rep {
            Rep::S(v) => Box::new(v.iter().copied()),
            Rep::D(d) => Box::new(d.iter()),
        }
    }

    pub fn union(&self, other: &IntSet) -> IntSet {
        if let (Some(()), Some(())) = (densifiable(&self.rep), densifiable(&other.rep)) {
            let (a, b) = (as_dense(&self.rep), as_dense(&other.rep));
            let mut out = Dense::default();
            let words = a.bits.len().max(b.bits.len());
            out.bits.resize(words, 0);
            let mut len = 0usize;
            for w in 0..words {
                let aw = a.bits.get(w).copied().unwrap_or(0);
                let bw = b.bits.get(w).copied().unwrap_or(0);
                out.bits[w] = aw | bw;
                len += out.bits[w].count_ones() as usize;
            }
            out.len = len;
            return IntSet { rep: Rep::D(out) };
        }
        let mut items = Vec::with_capacity(self.len() + other.len());
        merge_union(&as_vec(&self.rep), &as_vec(&other.rep), &mut items);
        IntSet { rep: Rep::S(items) }
    }

    pub fn intersection(&self, other: &IntSet) -> IntSet {
        if let (Some(()), Some(())) = (densifiable(&self.rep), densifiable(&other.rep)) {
            let (a, b) = (as_dense(&self.rep), as_dense(&other.rep));
            let mut out = Dense::default();
            let words = a.bits.len().min(b.bits.len());
            out.bits.resize(words, 0);
            let mut len = 0usize;
            for w in 0..words {
                out.bits[w] = a.bits[w] & b.bits[w];
                len += out.bits[w].count_ones() as usize;
            }
            out.len = len;
            return IntSet { rep: Rep::D(out) };
        }
        let mut items = Vec::new();
        merge_intersection(&as_vec(&self.rep), &as_vec(&other.rep), &mut items);
        IntSet { rep: Rep::S(items) }
    }

    pub fn difference(&self, other: &IntSet) -> IntSet {
        if let (Some(()), Some(())) = (densifiable(&self.rep), densifiable(&other.rep)) {
            let (a, b) = (as_dense(&self.rep), as_dense(&other.rep));
            let mut out = a.clone();
            let mut len = 0usize;
            for w in 0..out.bits.len() {
                let bw = b.bits.get(w).copied().unwrap_or(0);
                out.bits[w] &= !bw;
                len += out.bits[w].count_ones() as usize;
            }
            out.len = len;
            return IntSet { rep: Rep::D(out) };
        }
        let mut items = Vec::new();
        merge_difference(&as_vec(&self.rep), &as_vec(&other.rep), &mut items);
        IntSet { rep: Rep::S(items) }
    }

    pub fn contains_all(&self, other: &IntSet) -> bool {
        if other.len() > self.len() {
            return false;
        }
        if let (Rep::D(a), Rep::D(b)) = (&self.rep, &other.rep) {
            for (w, &bw) in b.bits.iter().enumerate() {
                let aw = a.bits.get(w).copied().unwrap_or(0);
                if aw & bw != bw {
                    return false;
                }
            }
            return true;
        }
        other.iter().all(|v| self.contains(v))
    }

    pub fn add_all(&mut self, other: &IntSet) -> bool {
        let before = self.len();
        *self = self.union(other);
        self.len() != before
    }

    pub fn remove_all(&mut self, other: &IntSet) -> bool {
        let before = self.len();
        *self = self.difference(other);
        self.len() != before
    }
}

impl PartialEq for IntSet {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.iter().eq(other.iter())
    }
}

impl Eq for IntSet {}

impl FromIterator<Int> for IntSet {
    fn from_iter<I: IntoIterator<Item = Int>>(iter: I) -> Self {
        let items: Vec<Int> = iter.into_iter().collect();
        let mut sorted = items;
        sorted.sort_unstable();
        sorted.dedup();
        let max_ok = sorted
            .last()
            .copied()
            .map(|m| m <= DENSE_MAX)
            .unwrap_or(false);
        if max_ok && sorted.len() >= DENSE_MIN_LEN {
            let mut d = Dense::new();
            for &v in &sorted {
                d.insert(v);
            }
            return IntSet { rep: Rep::D(d) };
        }
        IntSet {
            rep: Rep::S(sorted),
        }
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
