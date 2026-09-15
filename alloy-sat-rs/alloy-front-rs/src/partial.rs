//! Binary partial instances (APIN v1): no human-readable format involved.
//!
//! A [`PartialInstance`] is an in-memory `(name, arity, tuple-index set)`
//! snapshot plus integer bindings. It serializes to a compact binary form
//! (`APIN` magic + varints, same house style as ARE1/ARE2) and applies to an
//! [`IncrementalSession`] in three modes sharing one frozen slot space:
//!
//! - [`PartialInstance::apply_units`]: permanent unit clauses (`pin_units`),
//! - [`PartialInstance::apply_gated`]: retractable units behind one fresh
//!   selector (`add_gated`; assume it to activate),
//! - [`PartialInstance::avoid_clause`]: one blocking clause excluding every
//!   completion of the partial value (strong nogood generalization).
//!
//! Precondition (by design): instance and target Cnf share type, bounds and
//! signature names. This is still verified defensively (name resolution,
//! arity, universe size, `set_covers` upper containment); violations are
//! resolution errors, never silent UNSAT.
//!
//! Integers are saved but never compiled to clauses: int bounds are always
//! exact singletons, so there are no free int cells to pin. On apply they
//! are consistency-checked against the target's `exact_int_bound`.

use alloy_kodkod_rs::instance::Instance;
use alloy_kodkod_rs::intset::IntSet;
use alloy_kodkod_rs::relation::RelationId;
use alloy_kodkod_rs::sat::SatSolver;
use alloy_kodkod_rs::tupleset::TupleSet;

use crate::incremental::{find_relation, set_covers, IncrementalSession};
use crate::FrontError;

pub const APIN_MAGIC: &[u8; 4] = b"APIN";
pub const APIN_VERSION: u32 = 1;

/// One relation's value: name, arity, and sorted flat tuple indices.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PartialRel {
    pub name: String,
    pub arity: u32,
    pub indices: Vec<i64>,
}

/// One integer binding: value and its (singleton) tuple index.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PartialInt {
    pub value: i64,
    pub tuple: i64,
}

/// Binary partial instance. `skipped_skolem` records witness relations left
/// out by [`PartialInstance::extract`]; it is not serialized.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct PartialInstance {
    pub universe_size: usize,
    pub rels: Vec<PartialRel>,
    pub ints: Vec<PartialInt>,
    pub skipped_skolem: Vec<String>,
}

// ---------------------------------------------------------------------------
// Minimal varint/str16 codec (ARE1/ARE2 house style, dependency-free).
// ---------------------------------------------------------------------------

struct Writer(Vec<u8>);

impl Writer {
    fn new() -> Self {
        Writer(Vec::new())
    }
    fn bytes(&mut self, b: &[u8]) {
        self.0.extend_from_slice(b);
    }
    fn uvar(&mut self, mut v: u64) {
        loop {
            let byte = (v & 0x7f) as u8;
            v >>= 7;
            if v == 0 {
                self.0.push(byte);
                break;
            }
            self.0.push(byte | 0x80);
        }
    }
    fn u32v(&mut self, v: u32) {
        self.uvar(v as u64);
    }
    fn svar(&mut self, v: i64) {
        self.uvar(((v << 1) ^ (v >> 63)) as u64);
    }
    fn str16(&mut self, s: &str) {
        let b = s.as_bytes();
        self.0.extend_from_slice(&(b.len() as u16).to_le_bytes());
        self.0.extend_from_slice(b);
    }
}

struct Reader<'a> {
    buf: &'a [u8],
    pos: usize,
}

impl<'a> Reader<'a> {
    fn new(buf: &'a [u8]) -> Self {
        Reader { buf, pos: 0 }
    }
    fn take(&mut self, n: usize) -> Result<&'a [u8], FrontError> {
        if self.buf.len() < self.pos + n {
            return Err(FrontError::Resolve("APIN truncated".into()));
        }
        let s = &self.buf[self.pos..self.pos + n];
        self.pos += n;
        Ok(s)
    }
    fn uvar(&mut self) -> Result<u64, FrontError> {
        let mut out = 0u64;
        let mut shift = 0;
        loop {
            let b = self.take(1)?[0];
            out |= u64::from(b & 0x7f) << shift;
            if b & 0x80 == 0 {
                return Ok(out);
            }
            shift += 7;
            if shift > 63 {
                return Err(FrontError::Resolve("APIN varint overflow".into()));
            }
        }
    }
    fn u32v(&mut self) -> Result<u32, FrontError> {
        let v = self.uvar()?;
        u32::try_from(v).map_err(|_| FrontError::Resolve("APIN u32 overflow".into()))
    }
    fn svar(&mut self) -> Result<i64, FrontError> {
        let z = self.uvar()?;
        Ok(((z >> 1) as i64) ^ -((z & 1) as i64))
    }
    fn str16(&mut self) -> Result<String, FrontError> {
        let len = u16::from_le_bytes(self.take(2)?.try_into().unwrap()) as usize;
        let raw = self.take(len)?;
        String::from_utf8(raw.to_vec())
            .map_err(|_| FrontError::Resolve("APIN invalid utf-8".into()))
    }
    fn eof(&self) -> bool {
        self.pos == self.buf.len()
    }
}

impl PartialInstance {
    /// Snapshot an instance. `only=None` takes every non-skolem relation;
    /// `Some(names)` takes exactly those (unknown or skolem names are
    /// errors). Integers are always taken whole.
    pub fn extract(inst: &Instance, only: Option<&[&str]>) -> Result<Self, FrontError> {
        let pool = inst.pool();
        let mut rels = Vec::new();
        let mut skipped_skolem = Vec::new();
        let take = |name: &str| -> bool {
            match only {
                None => true,
                Some(list) => list.contains(&name),
            }
        };
        if let Some(list) = only {
            for want in list {
                match inst.find_relation_by_name(want) {
                    None => {
                        return Err(FrontError::Resolve(format!(
                            "no relation `{want}` in instance"
                        )));
                    }
                    Some(r) if pool.is_skolem(r) => {
                        return Err(FrontError::Resolve(format!(
                            "cannot extract skolem witness `{want}`"
                        )));
                    }
                    _ => {}
                }
            }
        }
        for (r, ts) in inst.relation_tuples() {
            let name = pool.name(r).to_string();
            if !take(&name) {
                continue;
            }
            if pool.is_skolem(r) {
                skipped_skolem.push(name);
                continue;
            }
            let mut indices: Vec<i64> = ts.index_view().iter().collect();
            indices.sort_unstable();
            rels.push(PartialRel {
                name,
                arity: ts.arity(),
                indices,
            });
        }
        let mut ints: Vec<PartialInt> = inst
            .int_tuples()
            .map(|(v, ts)| PartialInt {
                value: v,
                tuple: ts.index_view().iter().next().unwrap_or(-1),
            })
            .collect();
        ints.sort_by_key(|p| p.value);
        Ok(PartialInstance {
            universe_size: inst.universe().size(),
            rels,
            ints,
            skipped_skolem,
        })
    }

    /// Keep only `names` (plus all ints). Unknown names are errors.
    pub fn project(&self, names: &[&str]) -> Result<Self, FrontError> {
        let mut rels = Vec::new();
        for want in names {
            match self.rels.iter().find(|r| r.name == *want) {
                Some(r) => rels.push(r.clone()),
                None => {
                    return Err(FrontError::Resolve(format!(
                        "partial instance has no relation `{want}`"
                    )));
                }
            }
        }
        Ok(PartialInstance {
            universe_size: self.universe_size,
            rels,
            ints: self.ints.clone(),
            skipped_skolem: Vec::new(),
        })
    }

    /// Serialize (pure). Layout: magic, version, universe, rels
    /// (name/arity/sorted indices), ints (value/tuple).
    pub fn encode(&self) -> Vec<u8> {
        let mut w = Writer::new();
        w.bytes(APIN_MAGIC);
        w.u32v(APIN_VERSION);
        w.u32v(self.universe_size as u32);
        w.u32v(self.rels.len() as u32);
        for r in &self.rels {
            w.str16(&r.name);
            w.u32v(r.arity);
            w.u32v(r.indices.len() as u32);
            for &i in &r.indices {
                w.u32v(i as u32);
            }
        }
        w.u32v(self.ints.len() as u32);
        for p in &self.ints {
            w.svar(p.value);
            w.u32v(p.tuple as u32);
        }
        w.0
    }

    /// Deserialize (pure). Trailing bytes, bad magic/version, truncation and
    /// varint overflow are all errors.
    pub fn decode(buf: &[u8]) -> Result<Self, FrontError> {
        let mut r = Reader::new(buf);
        if r.take(4)? != APIN_MAGIC {
            return Err(FrontError::Resolve("not an APIN file (bad magic)".into()));
        }
        // Version check before any further parsing.
        let version = r.u32v()?;
        if version != APIN_VERSION {
            return Err(FrontError::Resolve(format!(
                "APIN version {version} unsupported (want {APIN_VERSION})"
            )));
        }
        let universe_size = r.u32v()? as usize;
        let n_rels = r.u32v()?;
        let mut rels = Vec::with_capacity(n_rels.min(1_000_000) as usize);
        for _ in 0..n_rels {
            let name = r.str16()?;
            let arity = r.u32v()?;
            let n_idx = r.u32v()?;
            if n_idx > 10_000_000 {
                return Err(FrontError::Resolve("APIN index count absurd".into()));
            }
            let mut indices = Vec::with_capacity(n_idx.min(1_000_000) as usize);
            for _ in 0..n_idx {
                indices.push(r.u32v()? as i64);
            }
            rels.push(PartialRel {
                name,
                arity,
                indices,
            });
        }
        let n_ints = r.u32v()?;
        if n_ints > 10_000_000 {
            return Err(FrontError::Resolve("APIN int count absurd".into()));
        }
        let mut ints = Vec::with_capacity(n_ints.min(1_000_000) as usize);
        for _ in 0..n_ints {
            ints.push(PartialInt {
                value: r.svar()?,
                tuple: r.u32v()? as i64,
            });
        }
        if !r.eof() {
            return Err(FrontError::Resolve("APIN trailing bytes".into()));
        }
        Ok(PartialInstance {
            universe_size,
            rels,
            ints,
            skipped_skolem: Vec::new(),
        })
    }

    /// Resolve one partial relation against session bounds and rebuild its
    /// value on the session universe. Shared by all apply paths.
    fn rebuild_value<S: SatSolver>(
        &self,
        sess: &IncrementalSession<S>,
        rel: &PartialRel,
    ) -> Result<(RelationId, TupleSet), FrontError> {
        let bounds = sess.bounds();
        let rid = find_relation(bounds, &rel.name)
            .ok_or_else(|| FrontError::Resolve(format!("target has no relation `{}`", rel.name)))?;
        if bounds.pool().is_skolem(rid) {
            return Err(FrontError::Resolve(format!(
                "cannot pin skolem witness `{}`",
                rel.name
            )));
        }
        if bounds.pool().arity(rid) != rel.arity {
            return Err(FrontError::Resolve(format!(
                "arity mismatch for `{}` (partial {}, target {})",
                rel.name,
                rel.arity,
                bounds.pool().arity(rid)
            )));
        }
        if bounds.universe().size() != self.universe_size {
            return Err(FrontError::Resolve(format!(
                "universe mismatch for `{}` (partial {}, target {})",
                rel.name,
                self.universe_size,
                bounds.universe().size()
            )));
        }
        let mut set = IntSet::new();
        for &i in &rel.indices {
            set.insert(i);
        }
        let ts = TupleSet::from_indices(bounds.universe(), rel.arity, set)
            .map_err(|_| FrontError::Resolve(format!("index out of range for `{}`", rel.name)))?;
        Ok((rid, ts))
    }

    /// Check saved integer bindings against the target's exact int bounds.
    fn check_ints<S: SatSolver>(&self, sess: &IncrementalSession<S>) -> Result<(), FrontError> {
        for p in &self.ints {
            match sess.bounds().exact_int_bound(p.value) {
                None => {
                    return Err(FrontError::Resolve(format!(
                        "target has no int bound for {}",
                        p.value
                    )));
                }
                Some(ts) => {
                    if ts.len() != 1 || !ts.contains_index(p.tuple) {
                        return Err(FrontError::Resolve(format!(
                            "int {} differs (partial tuple {}, target differs)",
                            p.value, p.tuple
                        )));
                    }
                }
            }
        }
        Ok(())
    }

    /// Permanently pin every relation via unit clauses. Returns the number
    /// of unit clauses added. Integer bindings are consistency-checked
    /// (never compiled to clauses).
    pub fn apply_units<S: SatSolver>(
        &self,
        sess: &mut IncrementalSession<S>,
    ) -> Result<usize, FrontError> {
        self.check_ints(sess)?;
        let mut n = 0;
        // Resolve-then-pin in two passes so a late failure cannot leave a
        // half-pinned session behind.
        let mut pairs = Vec::with_capacity(self.rels.len());
        for rel in &self.rels {
            pairs.push(self.rebuild_value(sess, rel)?);
        }
        for (rid, ts) in &pairs {
            n += sess.pin_units(*rid, ts)?;
        }
        Ok(n)
    }

    /// Retractable pin: all unit clauses behind one fresh selector.
    /// Returns the selector; assume it on the next `solve` to activate.
    pub fn apply_gated<S: SatSolver>(
        &self,
        sess: &mut IncrementalSession<S>,
    ) -> Result<i64, FrontError> {
        self.check_ints(sess)?;
        let mut units = Vec::new();
        for rel in &self.rels {
            let (rid, ts) = self.rebuild_value(sess, rel)?;
            // Same checks as `pin_units` without mutating first.
            if sess.bounds().pool().arity(rid) != ts.arity() {
                return Err(FrontError::Resolve(format!(
                    "arity mismatch for `{}`",
                    rel.name
                )));
            }
            for o in sess.origins() {
                if o.relation != rid {
                    continue;
                }
                let lit = o.slot as i64;
                units.push(vec![if ts.contains_index(o.tuple_index) {
                    lit
                } else {
                    -lit
                }]);
            }
        }
        sess.add_gated(&units)
    }

    /// Blocking clause excluding every completion of the partial value over
    /// `project` (default: all partial relations). Pure: the caller adds it
    /// via `add_clauses` (permanent) or `add_gated` (retractable).
    ///
    /// An empty clause means the scope covers no primary cells (everything
    /// already fixed): there is nothing to exclude.
    pub fn avoid_clause<S: SatSolver>(
        &self,
        sess: &IncrementalSession<S>,
        project: Option<&[&str]>,
    ) -> Result<Vec<i64>, FrontError> {
        let names: Vec<&str> = match project {
            Some(list) => {
                for want in list {
                    if !self.rels.iter().any(|r| r.name == *want) {
                        return Err(FrontError::Resolve(format!(
                            "partial instance has no relation `{want}`"
                        )));
                    }
                }
                list.to_vec()
            }
            None => self.rels.iter().map(|r| r.name.as_str()).collect(),
        };
        let mut clause = Vec::new();
        for name in names {
            let rel = self.rels.iter().find(|r| r.name == name).expect("checked");
            let bounds = sess.bounds();
            let rid = find_relation(bounds, name)
                .ok_or_else(|| FrontError::Resolve(format!("target has no relation `{name}`")))?;
            if bounds.universe().size() != self.universe_size {
                return Err(FrontError::Resolve(format!(
                    "universe mismatch for `{name}`"
                )));
            }
            for o in sess.origins() {
                if o.relation != rid {
                    continue;
                }
                let lit = o.slot as i64;
                clause.push(if rel.indices.contains(&o.tuple_index) {
                    -lit
                } else {
                    lit
                });
            }
        }
        Ok(clause)
    }
}

/// Build verifier assumes pinning `holes` to a decoded partial value.
///
/// Same checks as the live-candidate path in `run_cegis` (name resolution,
/// arity, universe size, upper containment); integers are intentionally
/// ignored to preserve that path's behavior exactly.
pub fn verifier_pin_from_partial<S: SatSolver>(
    sess: &IncrementalSession<S>,
    partial: &PartialInstance,
    holes: &[&str],
) -> Result<Vec<i64>, FrontError> {
    let mut assumes = Vec::new();
    for h in holes {
        let prel = partial
            .rels
            .iter()
            .find(|r| r.name == *h)
            .ok_or_else(|| FrontError::Resolve(format!("partial lacks hole `{h}`")))?;
        let bounds = sess.bounds();
        let rv = find_relation(bounds, h)
            .ok_or_else(|| FrontError::Resolve(format!("verifier has no relation `{h}`")))?;
        if bounds.pool().arity(rv) != prel.arity {
            return Err(FrontError::Resolve(format!(
                "arity mismatch for hole `{h}` between partial and verifier"
            )));
        }
        if bounds.universe().size() != partial.universe_size {
            return Err(FrontError::Resolve(format!(
                "universe mismatch for hole `{h}` (scopes differ?)"
            )));
        }
        let mut set = IntSet::new();
        for &i in &prel.indices {
            set.insert(i);
        }
        let ts = TupleSet::from_indices(bounds.universe(), prel.arity, set)
            .map_err(|_| FrontError::Resolve(format!("index out of range for hole `{h}`")))?;
        if let Some(upper) = bounds.upper_bound(rv) {
            if !set_covers(upper, &ts) {
                return Err(FrontError::Resolve(format!(
                    "partial hole `{h}` escapes the verifier upper bound"
                )));
            }
        }
        assumes.extend(sess.assumes_for_relation(rv, &ts));
    }
    Ok(assumes)
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloy_kodkod_rs::sat::RecordingSolver;

    fn model_cnf() -> crate::cnf::Cnf {
        // `A` free over 2 atoms (4 models), `B` fixed by `exactly`.
        // Explicit `4 Int` keeps int bounds materialized (int atoms are
        // otherwise allocated lazily, only when Int is used as a set).
        let src = "sig A {}\none sig B {}\nrun { A = A } for 2, 4 Int";
        let m = crate::parse_module(src).expect("parse");
        crate::cnf::run(&m, 0).expect("build")
    }

    fn open_rec(cnf: &crate::cnf::Cnf) -> IncrementalSession<RecordingSolver> {
        IncrementalSession::open_with(RecordingSolver::new(), cnf).expect("open")
    }

    fn first_model(cnf: &crate::cnf::Cnf) -> alloy_kodkod_rs::instance::Instance {
        let mut s = open_rec(cnf);
        s.solve(&[]).expect("solve").expect("SAT")
    }

    #[test]
    fn roundtrip_apply_matches_original() {
        let cnf = model_cnf();
        let inst = first_model(&cnf);
        let p = PartialInstance::extract(&inst, None).expect("extract");
        assert!(p.rels.iter().any(|r| r.name == "A"));
        assert!(p.skipped_skolem.is_empty());
        let bytes = p.encode();
        assert!(bytes.starts_with(APIN_MAGIC));
        let q = PartialInstance::decode(&bytes).expect("decode");
        assert_eq!(p, q);

        let mut s = open_rec(&cnf);
        let n = q.apply_units(&mut s).expect("apply");
        assert!(n > 0);
        let back = s.solve(&[]).expect("solve").expect("SAT");
        for r in &q.rels {
            let rid = back.find_relation_by_name(&r.name).expect("rel");
            let got: Vec<i64> = back.tuples(rid).unwrap().index_view().iter().collect();
            assert_eq!(got, r.indices, "relation {}", r.name);
        }
    }

    #[test]
    fn subset_leaves_rest_free() {
        let cnf = model_cnf();
        let inst = first_model(&cnf);
        let full = PartialInstance::extract(&inst, None).expect("extract");
        // A has 4 values over 2 atoms; pin only B (fixed) and enumerate A.
        let sub = full.project(&["B"]).expect("project");
        assert_eq!(sub.rels.len(), 1);
        let mut s = open_rec(&cnf);
        sub.apply_units(&mut s).expect("apply");
        let mut seen = std::collections::HashSet::new();
        while let Some(m) = s.solve(&[]).expect("solve") {
            let r = m.find_relation_by_name("A").expect("A");
            seen.insert(format!("{}", m.tuples(r).unwrap()));
            assert!(s.block_last_model(None).expect("block"));
        }
        assert_eq!(seen.len(), 4, "A stays free under a B-only pin");
    }

    #[test]
    fn violations_are_errors() {
        let cnf = model_cnf();
        let inst = first_model(&cnf);
        let p = PartialInstance::extract(&inst, None).expect("extract");

        // Unknown relation.
        let mut bad = p.clone();
        bad.rels.push(PartialRel {
            name: "Nope".into(),
            arity: 1,
            indices: vec![],
        });
        assert!(bad.apply_units(&mut open_rec(&cnf)).is_err());

        // Arity mismatch.
        let mut bad = p.clone();
        bad.rels.iter_mut().find(|r| r.name == "A").unwrap().arity = 2;
        assert!(bad.apply_units(&mut open_rec(&cnf)).is_err());

        // Universe mismatch.
        let mut bad = p.clone();
        bad.universe_size += 1;
        assert!(bad.apply_units(&mut open_rec(&cnf)).is_err());

        // Upper escape: far-out index is outside A's upper bound.
        let mut bad = p.clone();
        bad.rels.iter_mut().find(|r| r.name == "A").unwrap().indices = vec![10_000];
        assert!(bad.apply_units(&mut open_rec(&cnf)).is_err());

        // Lower drop: `one B` lower bound is non-empty; emptying B violates it.
        let mut bad = p.clone();
        bad.rels.iter_mut().find(|r| r.name == "B").unwrap().indices = vec![];
        assert!(bad.apply_units(&mut open_rec(&cnf)).is_err());

        // Int mismatch.
        if !p.ints.is_empty() {
            let mut bad = p.clone();
            bad.ints[0].tuple += 100;
            assert!(bad.apply_units(&mut open_rec(&cnf)).is_err());
        }
    }

    #[test]
    fn gated_apply_activates_and_releases() {
        let cnf = model_cnf();
        let inst = first_model(&cnf);
        let p = PartialInstance::extract(&inst, Some(&["A"])).expect("extract");
        let mut s = open_rec(&cnf);
        let sel = p.apply_gated(&mut s).expect("gate");
        assert!(sel > cnf.num_vars as i64);
        // Activated: A equals the extracted value.
        let pinned = s.solve(&[sel]).expect("solve").expect("SAT");
        let r = pinned.find_relation_by_name("A").expect("A");
        let got: Vec<i64> = pinned.tuples(r).unwrap().index_view().iter().collect();
        let want = &p.rels.iter().find(|r| r.name == "A").unwrap().indices;
        assert_eq!(&got, want);
        // Dormant: free again (all 4 A values reachable).
        let mut seen = std::collections::HashSet::new();
        while let Some(m) = s.solve(&[]).expect("solve") {
            seen.insert(format!("{}", m.tuples(r).unwrap()));
            assert!(s.block_last_model(None).expect("block"));
        }
        assert_eq!(seen.len(), 4);
    }

    #[test]
    fn avoid_excludes_candidate() {
        let cnf = model_cnf();
        let inst = first_model(&cnf);
        let p = PartialInstance::extract(&inst, Some(&["A"])).expect("extract");
        let mut s = open_rec(&cnf);
        let clause = p.avoid_clause(&s, None).expect("avoid");
        assert!(!clause.is_empty());
        s.add_clauses(std::slice::from_ref(&clause)).expect("add");
        // The pinned value is gone; the other 3 A values remain.
        let mut seen = std::collections::HashSet::new();
        while let Some(m) = s.solve(&[]).expect("solve") {
            let r = m.find_relation_by_name("A").expect("A");
            seen.insert(format!("{}", m.tuples(r).unwrap()));
            assert!(s.block_last_model(None).expect("block"));
        }
        assert_eq!(seen.len(), 3);
        // Unknown projection names are errors, not silent skips.
        assert!(p.avoid_clause(&s, Some(&["Nope"])).is_err());
    }

    #[test]
    fn skolem_excluded_from_extract() {
        let src = "sig A {} pred p { some x: A | some x } run p for 2";
        let m = crate::parse_module(src).expect("parse");
        let cnf = crate::cnf::run(&m, 0).expect("build");
        assert!(!cnf.bounds.skolems().is_empty());
        let inst = first_model(&cnf);
        let p = PartialInstance::extract(&inst, None).expect("extract");
        assert!(!p.skipped_skolem.is_empty());
        assert!(p.rels.iter().all(|r| !r.name.starts_with("$sk")));
        // Wire round-trip drops the (non-serialized) skip list by design.
        let q = PartialInstance::decode(&p.encode()).expect("decode");
        assert!(q.skipped_skolem.is_empty());
        assert_eq!(q.rels, p.rels);
    }

    #[test]
    fn corrupt_inputs_rejected() {
        let cnf = model_cnf();
        let inst = first_model(&cnf);
        let bytes = PartialInstance::extract(&inst, None)
            .expect("extract")
            .encode();
        assert!(PartialInstance::decode(&bytes[..bytes.len() - 1]).is_err());
        let mut bad = bytes.clone();
        bad[0] = b'X';
        assert!(PartialInstance::decode(&bad).is_err());
        let mut bad = bytes.clone();
        bad[4] = 99; // version
        assert!(PartialInstance::decode(&bad).is_err());
        let mut bad = bytes.clone();
        bad.push(0); // trailing
        assert!(PartialInstance::decode(&bad).is_err());
        assert!(PartialInstance::decode(&[]).is_err());
    }

    #[test]
    fn int_bindings_checked() {
        let cnf = model_cnf();
        let probe = open_rec(&cnf);
        let (v, idx) = match probe.bounds().int_bounds().next() {
            Some((v, ts)) => (v, ts.index_view().iter().next().unwrap()),
            None => panic!("expected int bounds in target"),
        };
        let unisz = probe.bounds().universe().size();
        let good = PartialInstance {
            universe_size: unisz,
            rels: vec![],
            ints: vec![PartialInt {
                value: v,
                tuple: idx,
            }],
            skipped_skolem: vec![],
        };
        // Ints survive the wire round-trip.
        let back = PartialInstance::decode(&good.encode()).expect("decode");
        assert_eq!(back, good);
        // Matching ints: no-op success (0 units, no rels).
        let mut s = open_rec(&cnf);
        assert_eq!(back.apply_units(&mut s).expect("apply"), 0);
        // Mismatched tuple: hard error, solver untouched.
        let mut bad = back.clone();
        bad.ints[0].tuple = idx + 10_000;
        assert!(bad.apply_units(&mut open_rec(&cnf)).is_err());
        // Unknown int value: hard error.
        let mut bad = back.clone();
        bad.ints[0].value = i64::MIN;
        assert!(bad.apply_units(&mut open_rec(&cnf)).is_err());
    }

    #[test]
    fn verifier_helper_matches_live_path() {
        // Same candidate through live TupleSets vs decoded partial: identical assumes.
        let src = "sig A {}\nassert someA { some A }\nrun { A = A } for 2\ncheck someA for 2";
        let m = crate::parse_module(src).expect("parse");
        let synth = crate::cnf::run(&m, 0).expect("synth");
        let verify = crate::cnf::check(&m, 1).expect("verify");
        let cand = first_model(&synth);
        let ver = open_rec(&verify);
        let ts = cand
            .find_relation_by_name("A")
            .and_then(|r| cand.tuples(r))
            .unwrap()
            .clone();
        let rid = crate::incremental::find_relation(ver.bounds(), "A").expect("A");
        let mut live: Vec<i64> = ver.assumes_for_relation(rid, &ts);
        let partial = PartialInstance::extract(&cand, Some(&["A"])).expect("extract");
        let mut via = verifier_pin_from_partial(&ver, &partial, &["A"]).expect("helper");
        live.sort_unstable();
        via.sort_unstable();
        assert_eq!(live, via);
    }
}
