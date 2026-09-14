//! Incremental solving sessions for iterative methods (CEGAR/CEGIS).
//!
//! A [`IncrementalSession`] owns one SAT solver and keeps its learned clauses
//! across iterations. The *primary* slot space is frozen at
//! [`IncrementalSession::open`] time: in-session refinement is expressed with
//! clauses over primary slots (blocking clauses, pins, units, multiplicity
//! constraints) plus fresh selector variables allocated by
//! [`IncrementalSession::new_selector`] for retractable (`gated`) refinements.
//! Selectors live strictly above the frozen space, so learned clauses stay
//! valid. Anything needing fresh *formula* variables (new Tseitin conjunctions
//! over primaries) must go through a derived `Cnf` + a new session.
//!
//! v1 scope decisions (see design notes):
//! - Concrete over `IpasirSolver` via [`IncrementalSession::open`]; generic
//!   over `S: SatSolver` via [`IncrementalSession::open_with`] (e.g. small
//!   models with `RecordingSolver` in tests).
//! - `failed_core_names` exposes UNSAT cores; core-driven *generalization* is
//!   v2 (the accessor exists so v1 can already measure core sizes).

use std::collections::HashSet;

use alloy_kodkod_rs::bounds::Bounds;
use alloy_kodkod_rs::fol::TranslateError;
use alloy_kodkod_rs::instance::Instance;
use alloy_kodkod_rs::ipasir_bridge::IpasirSolver;
use alloy_kodkod_rs::relation::RelationId;
use alloy_kodkod_rs::sat::SatSolver;
use alloy_kodkod_rs::tupleset::TupleSet;

use crate::cnf::Cnf;
use crate::FrontError;

/// Multiplicity constraint kind over a relation's primary cells.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MultKind {
    /// No cell true.
    No,
    /// At least one cell true.
    Some,
    /// At least one cell false.
    NotAll,
    /// At most one cell true.
    Lone,
    /// Exactly one cell true.
    One,
}

/// Per-session counters for CEGAR/CEGIS measurement (v1 observes, v2 tunes).
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct SessionStats {
    /// Total `solve` calls on this session.
    pub solves: usize,
    /// SAT answers.
    pub sat: usize,
    /// UNSAT answers.
    pub unsat: usize,
    /// Clauses added after `open` (refinement clauses, not the base Cnf).
    pub clauses_added: usize,
    /// Total assumption literals passed to `solve`.
    pub assumes_total: usize,
}

/// Find a bounded relation by (sig/field) name.
///
/// Pools are rebuilt per `Cnf`, so callers must resolve by name, never by
/// carrying a `RelationId` across sessions.
pub(crate) fn find_relation(bounds: &Bounds, name: &str) -> Option<RelationId> {
    bounds
        .relations()
        .find(|&r| bounds.pool().name(r).as_ref() == name)
}

/// Index-based containment for cross-session values.
///
/// `TupleSet::covers` requires universe *identity* (`Universe::same` is
/// pointer equality), which never holds across separately built `Cnf`s even
/// for identical scopes. Pin/transfer checks must use this instead: same
/// arity, same universe *size*, and index-set containment.
pub(crate) fn set_covers(sup: &TupleSet, sub: &TupleSet) -> bool {
    sup.arity() == sub.arity()
        && sup.universe().size() == sub.universe().size()
        && sup.index_view().contains_all(sub.index_view())
}

/// An incremental solver session bound to one frozen [`Cnf`] slot space.
///
/// Created by [`IncrementalSession::open`] (CaDiCaL backend) or
/// [`IncrementalSession::open_with`] (caller-provided solver, e.g.
/// `RecordingSolver` for tiny models in tests).
pub struct IncrementalSession<S = IpasirSolver> {
    solver: S,
    bounds: Bounds,
    origins: Vec<alloy_kodkod_rs::fol::VarOrigin>,
    num_primary: usize,
    last_sat: Option<bool>,
    last_instance: Option<Instance>,
    stats: SessionStats,
}

impl<S: SatSolver> IncrementalSession<S> {
    /// Open a session on a caller-provided solver, loading the base clauses once.
    pub fn open_with(mut solver: S, cnf: &Cnf) -> Result<Self, FrontError> {
        if cnf.num_vars > solver.num_variables() {
            solver.add_variables(cnf.num_vars - solver.num_variables());
        }
        for clause in &cnf.clauses {
            if !solver.add_clause(clause) {
                return Err(FrontError::Solve(TranslateError::Solver(
                    "incremental session: failed to add base clause".into(),
                )));
            }
        }
        Ok(IncrementalSession {
            solver,
            bounds: cnf.bounds.clone(),
            origins: cnf.origins.clone(),
            num_primary: cnf.num_vars,
            last_sat: None,
            last_instance: None,
            stats: SessionStats::default(),
        })
    }

    /// Solve once under `assumes` (consumed by this call; clauses persist).
    ///
    /// - SAT   => `Ok(Some(instance))`
    /// - UNSAT => `Ok(None)` (use [`Self::failed_core_names`] for the core)
    pub fn solve(&mut self, assumes: &[i64]) -> Result<Option<Instance>, FrontError> {
        for &a in assumes {
            self.solver.assume(a);
        }
        self.stats.solves += 1;
        self.stats.assumes_total += assumes.len();
        if SatSolver::solve(&mut self.solver) {
            let inst = crate::cnf::materialize(&self.bounds, &self.origins, |slot| {
                SatSolver::value_of(&self.solver, slot as i64)
            })
            .map_err(FrontError::Solve)?;
            self.last_sat = Some(true);
            self.last_instance = Some(inst.clone());
            self.stats.sat += 1;
            Ok(Some(inst))
        } else {
            self.last_sat = Some(false);
            self.last_instance = None;
            self.stats.unsat += 1;
            Ok(None)
        }
    }

    /// Permanently add refinement clauses (blocking clauses, counterexamples).
    /// Learned clauses from prior solves are retained by the backend.
    pub fn add_clauses(&mut self, clauses: &[Vec<i64>]) -> Result<(), FrontError> {
        for clause in clauses {
            if !self.solver.add_clause(clause) {
                return Err(FrontError::Solve(TranslateError::Solver(
                    "incremental session: failed to add refinement clause".into(),
                )));
            }
        }
        self.stats.clauses_added += clauses.len();
        Ok(())
    }

    /// Allocate a fresh selector variable above the frozen slot space.
    ///
    /// The returned literal is strictly greater than every variable used so
    /// far, so it can never alias a primary or Tseitin variable. No clause
    /// constrains it; pair with [`Self::add_gated`].
    ///
    /// Discipline (Java-port lesson): the fresh number must be `N+1` where `N`
    /// is the current vocabulary size. Using `N` itself would alias the last
    /// primary/Tseitin variable and silently corrupt refinements.
    pub fn new_selector(&mut self) -> i64 {
        let lit = self.solver.num_variables() as i64 + 1;
        self.solver.add_variables(1);
        lit
    }

    /// Permanently add `clauses`, each weakened with `¬sel`, and return `sel`.
    ///
    /// Solving under the assumption `sel` activates the whole set; solving
    /// without it leaves the session unconstrained by them. This is the
    /// retractable-refinement primitive (the sound form of Java `Cnf`'s gated
    /// `cnf_avoid`/`cnf_some`/`cnf_notAll` else-branches): one shared selector
    /// gates an arbitrary clause set, including multi-clause constraints such
    /// as [`MultKind::Lone`].
    pub fn add_gated(&mut self, clauses: &[Vec<i64>]) -> Result<i64, FrontError> {
        let sel = self.new_selector();
        let gated: Vec<Vec<i64>> = clauses
            .iter()
            .map(|c| {
                let mut g = c.clone();
                g.push(-sel);
                g
            })
            .collect();
        self.add_clauses(&gated)?;
        Ok(sel)
    }

    /// Positive primary literals of `rel`, in origin order.
    fn primary_lits(&self, rel: RelationId) -> Vec<i64> {
        self.origins
            .iter()
            .filter(|o| o.relation == rel)
            .map(|o| o.slot as i64)
            .collect()
    }

    /// Build multiplicity clauses over `rel`'s primary cells (pure function).
    ///
    /// - `No`     : every cell false (`cnf_no`).
    /// - `Some`   : at least one cell true (`cnf_some`).
    /// - `NotAll` : at least one cell false (`cnf_notAll`).
    /// - `Lone`   : at most one cell true, pairwise (`cnf_lone`).
    /// - `One`    : exactly one cell true (`cnf_one` = lone + some).
    ///
    /// Lower-bound awareness (Java `Cnf` has none and over-constrains when the
    /// lower bound is non-empty): a non-empty lower bound already satisfies
    /// `Some` (no clause), already violates `No` (immediate-UNSAT empty
    /// clause), forces every free cell false under `Lone`/`One`, and violates
    /// them outright at two or more lower tuples. Fully-fixed relations (no
    /// primary cells) are decided against the lower bound: `[]` when the
    /// constraint already holds, `[[]]` when violated.
    ///
    /// Compose with [`Self::add_clauses`] (permanent) or [`Self::add_gated`]
    /// (retractable, one shared selector even for multi-clause `Lone`).
    pub fn mult_clauses(&self, rel: RelationId, kind: MultKind) -> Vec<Vec<i64>> {
        let lits = self.primary_lits(rel);
        let lower_len = self.bounds.lower_bound(rel).map(|t| t.len()).unwrap_or(0);
        if lits.is_empty() {
            let holds = match kind {
                MultKind::No => lower_len == 0,
                MultKind::Some => lower_len >= 1,
                // Fixed means every upper cell is forced true.
                MultKind::NotAll => false,
                MultKind::Lone => lower_len < 2,
                MultKind::One => lower_len == 1,
            };
            return if holds { vec![] } else { vec![vec![]] };
        }
        match kind {
            MultKind::No => {
                if lower_len > 0 {
                    vec![vec![]]
                } else {
                    lits.into_iter().map(|l| vec![-l]).collect()
                }
            }
            MultKind::Some => {
                if lower_len > 0 {
                    vec![]
                } else {
                    vec![lits]
                }
            }
            // Lower cells are constant-true, so "some free cell is false" is
            // already the exact meaning: no lower adjustment needed.
            MultKind::NotAll => vec![lits.into_iter().map(|l| -l).collect()],
            MultKind::Lone => Self::lone_clauses(&lits, lower_len),
            MultKind::One => {
                let mut out = Self::lone_clauses(&lits, lower_len);
                if lower_len == 0 {
                    out.push(lits);
                }
                out
            }
        }
    }

    /// Name-resolved variant of [`Self::mult_clauses`]; rejects unknown and
    /// skolem-witness relations.
    pub fn mult_clauses_by_name(
        &self,
        name: &str,
        kind: MultKind,
    ) -> Result<Vec<Vec<i64>>, FrontError> {
        let rel = find_relation(&self.bounds, name)
            .ok_or_else(|| FrontError::Resolve(format!("no relation `{name}` in session")))?;
        if self.bounds.pool().is_skolem(rel) {
            return Err(FrontError::Resolve(format!(
                "cannot constrain skolem witness `{name}`"
            )));
        }
        Ok(self.mult_clauses(rel, kind))
    }

    /// Pairwise at-most-one clauses, plus forced-false units when the lower
    /// bound already contributes its single allowed tuple.
    fn lone_clauses(lits: &[i64], lower_len: usize) -> Vec<Vec<i64>> {
        if lower_len >= 2 {
            return vec![vec![]];
        }
        let mut out: Vec<Vec<i64>> = lits
            .iter()
            .enumerate()
            .flat_map(|(i, &a)| lits[i + 1..].iter().map(move |&b| vec![-a, -b]))
            .collect();
        if lower_len == 1 {
            out.extend(lits.iter().map(|&l| vec![-l]));
        }
        out
    }

    /// Assumption literals pinning `rel` exactly to `val` (no solver mutation).
    ///
    /// Low-level hot path: no validation. Use [`Self::assumes_for_name`] for
    /// the checked variant.
    pub fn assumes_for_relation(&self, rel: RelationId, val: &TupleSet) -> Vec<i64> {
        let mut out = Vec::new();
        for o in &self.origins {
            if o.relation != rel {
                continue;
            }
            let lit = o.slot as i64;
            out.push(if val.contains_index(o.tuple_index) {
                lit
            } else {
                -lit
            });
        }
        out
    }

    /// Checked variant of [`Self::assumes_for_relation`] by relation name.
    ///
    /// Rejects unknown/skolem relations, arity mismatches, universe
    /// mismatches, and values outside the relation's upper bound.
    pub fn assumes_for_name(&self, name: &str, val: &TupleSet) -> Result<Vec<i64>, FrontError> {
        let rel = find_relation(&self.bounds, name)
            .ok_or_else(|| FrontError::Resolve(format!("no relation `{name}` in session")))?;
        if self.bounds.pool().is_skolem(rel) {
            return Err(FrontError::Resolve(format!(
                "cannot pin skolem witness `{name}`"
            )));
        }
        self.check_value(rel, name, val)?;
        Ok(self.assumes_for_relation(rel, val))
    }

    /// Permanently pin `rel` exactly to `val` via unit clauses.
    ///
    /// Lighter than a derived `Cnf` (`bound_exactly` + re-translate): no new
    /// variables, no re-encode. Additionally requires `lower ⊆ val`
    /// (exact-pin semantics); violations are resolution errors, not UNSAT.
    /// Returns the number of unit clauses added.
    pub fn pin_units(&mut self, rel: RelationId, val: &TupleSet) -> Result<usize, FrontError> {
        let name = self.bounds.pool().name(rel).to_string();
        if self.bounds.pool().is_skolem(rel) {
            return Err(FrontError::Resolve(format!(
                "cannot pin skolem witness `{name}`"
            )));
        }
        self.check_value(rel, &name, val)?;
        if let Some(lower) = self.bounds.lower_bound(rel) {
            if !set_covers(val, lower) {
                return Err(FrontError::Resolve(format!(
                    "pin of `{name}` drops lower-bound tuples"
                )));
            }
        }
        let units: Vec<Vec<i64>> = self
            .assumes_for_relation(rel, val)
            .into_iter()
            .map(|lit| vec![lit])
            .collect();
        let n = units.len();
        self.add_clauses(&units)?;
        Ok(n)
    }

    /// Block the last model (optionally projected to `relations`).
    ///
    /// Returns `Ok(false)` and adds nothing when there is no last model or
    /// the projection covers no primary variables (fully-fixed problem:
    /// callers should treat this as enumeration-exhausted).
    pub fn block_last_model(
        &mut self,
        relations: Option<&[RelationId]>,
    ) -> Result<bool, FrontError> {
        let inst = match &self.last_instance {
            Some(i) => i.clone(),
            None => return Ok(false),
        };
        let mut clause = Vec::new();
        for o in &self.origins {
            if let Some(rs) = relations {
                if !rs.contains(&o.relation) {
                    continue;
                }
            }
            let present = inst
                .tuples(o.relation)
                .map(|t| t.contains_index(o.tuple_index))
                .unwrap_or(false);
            let lit = o.slot as i64;
            clause.push(if present { -lit } else { lit });
        }
        if clause.is_empty() {
            return Ok(false);
        }
        self.add_clauses(std::slice::from_ref(&clause))?;
        Ok(true)
    }

    /// Names of relations in the last UNSAT failed core (deduplicated, sorted).
    ///
    /// Empty when the last solve was SAT or the backend reports no core.
    /// v1 exposes this for measurement; core-driven generalization is v2.
    pub fn failed_core_names(&self) -> Vec<String> {
        let mut names: HashSet<String> = HashSet::new();
        for lit in self.solver.failed_core() {
            let slot = lit.unsigned_abs() as u32;
            if let Some(o) = self.origins.iter().find(|o| o.slot == slot) {
                names.insert(self.bounds.pool().name(o.relation).to_string());
            }
        }
        let mut out: Vec<String> = names.into_iter().collect();
        out.sort();
        out
    }

    fn check_value(&self, rel: RelationId, name: &str, val: &TupleSet) -> Result<(), FrontError> {
        if self.bounds.pool().arity(rel) != val.arity() {
            return Err(FrontError::Resolve(format!(
                "arity mismatch pinning `{name}`"
            )));
        }
        if self.bounds.universe().size() != val.universe().size() {
            return Err(FrontError::Resolve(format!(
                "universe mismatch pinning `{name}` (different scope?)"
            )));
        }
        if let Some(upper) = self.bounds.upper_bound(rel) {
            if !set_covers(upper, val) {
                return Err(FrontError::Resolve(format!(
                    "pin of `{name}` escapes its upper bound"
                )));
            }
        }
        Ok(())
    }

    /// Session bounds (frozen slot space).
    pub fn bounds(&self) -> &Bounds {
        &self.bounds
    }

    /// Frozen slot origins.
    pub fn origins(&self) -> &[alloy_kodkod_rs::fol::VarOrigin] {
        &self.origins
    }

    /// Number of primary SAT variables loaded at `open`.
    pub fn num_primary(&self) -> usize {
        self.num_primary
    }

    /// Last solve outcome, if any.
    pub fn last_sat(&self) -> Option<bool> {
        self.last_sat
    }

    /// Measurement counters.
    pub fn stats(&self) -> SessionStats {
        self.stats
    }
}

impl IncrementalSession<IpasirSolver> {
    /// Open a session on the default IPASIR (CaDiCaL) backend.
    pub fn open(cnf: &Cnf) -> Result<Self, FrontError> {
        let solver =
            IpasirSolver::new().map_err(|e| FrontError::Solve(TranslateError::Solver(e)))?;
        Self::open_with(solver, cnf)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloy_kodkod_rs::sat::RecordingSolver;

    fn tiny_cnf() -> Cnf {
        // `A` free over a 1-atom universe: exactly 2 models ({} / {A$0}).
        //
        // NOTE: the body must *mention* `A`. An empty `run {}` compiles to a
        // constant-true formula, so no relation leaf (and no primary
        // variable) is ever created; likewise `for exactly 1` would fix `A`
        // to its lower bound. `A = A` is a tautology that forces the leaf.
        let src = "sig A {} run { A = A } for 1";
        let m = crate::parse_module(src).expect("parse");
        crate::cnf::run(&m, 0).expect("build")
    }

    fn open_rec(cnf: &Cnf) -> IncrementalSession<RecordingSolver> {
        IncrementalSession::open_with(RecordingSolver::new(), cnf).expect("open")
    }

    #[test]
    fn session_matches_fresh_solve() {
        let cnf = tiny_cnf();
        let fresh = crate::cnf::solve(&cnf).expect("fresh").is_some();
        let mut s = open_rec(&cnf);
        let inc = s.solve(&[]).expect("session").is_some();
        assert_eq!(fresh, inc);
        assert_eq!(s.stats().solves, 1);
        assert_eq!(s.stats().sat, 1);
    }

    #[test]
    fn assumes_pin_and_release() {
        let cnf = tiny_cnf();
        let mut s = open_rec(&cnf);
        let first = s.solve(&[]).expect("solve").expect("SAT");
        let rel = find_relation(s.bounds(), "A").expect("A");
        let val = first.tuples(rel).expect("A value").clone();
        // Exact pin of the first model: still SAT, same value.
        let assumes = s.assumes_for_relation(rel, &val);
        assert!(!assumes.is_empty());
        let pinned = s.solve(&assumes).expect("pinned").expect("SAT");
        assert_eq!(
            format!("{}", pinned.tuples(rel).unwrap()),
            format!("{}", val)
        );
        // Assumes are consumed: plain solve works again.
        assert!(s.solve(&[]).expect("released").is_some());
        assert_eq!(s.stats().solves, 3);
        assert_eq!(s.stats().assumes_total, assumes.len());
    }

    #[test]
    fn block_enumerates_all_models_then_unsat() {
        let cnf = tiny_cnf();
        let mut s = open_rec(&cnf);
        let mut seen = HashSet::new();
        while let Some(inst) = s.solve(&[]).expect("solve") {
            let rel = find_relation(s.bounds(), "A").expect("A");
            seen.insert(format!("{}", inst.tuples(rel).unwrap()));
            assert!(s.block_last_model(None).expect("block"));
        }
        assert_eq!(seen.len(), 2, "A over 1 atom has 2 models");
        assert_eq!(s.stats().unsat, 1);
    }

    #[test]
    fn pin_units_conflict_is_unsat() {
        let cnf = tiny_cnf();
        let mut s = open_rec(&cnf);
        let rel = find_relation(s.bounds(), "A").expect("A");
        // Pin A to empty, then pin A to {A$0}: permanent conflict.
        let empty = TupleSet::new(s.bounds().universe(), 1).expect("empty");
        s.pin_units(rel, &empty).expect("pin empty");
        let mut full = TupleSet::new(s.bounds().universe(), 1).expect("full");
        full.insert_index(0);
        s.pin_units(rel, &full).expect("pin full");
        assert!(s.solve(&[]).expect("solve").is_none());
    }

    #[test]
    fn conflicting_assumes_report_core_names() {
        // `failed_core` covers *assumptions*, not permanent clauses: pin A
        // empty as units, then assume the opposite in one solve call.
        let cnf = tiny_cnf();
        let mut s = open_rec(&cnf);
        let rel = find_relation(s.bounds(), "A").expect("A");
        let empty = TupleSet::new(s.bounds().universe(), 1).expect("empty");
        s.pin_units(rel, &empty).expect("pin empty");
        let mut full = TupleSet::new(s.bounds().universe(), 1).expect("full");
        full.insert_index(0);
        let assumes = s.assumes_for_relation(rel, &full);
        assert!(s.solve(&assumes).expect("solve").is_none());
        assert!(s.failed_core_names().contains(&"A".to_string()));
    }

    fn tiny2_cnf() -> Cnf {
        // Same tautology trick over 2 atoms: 2 primary vars, 4 models.
        let src = "sig A {} run { A = A } for 2";
        let m = crate::parse_module(src).expect("parse");
        crate::cnf::run(&m, 0).expect("build")
    }

    fn fixed_cnf() -> Cnf {
        // `exactly 1` fixes A to its lower bound: no primary variables.
        let src = "sig A {} run { A = A } for exactly 1";
        let m = crate::parse_module(src).expect("parse");
        crate::cnf::run(&m, 0).expect("build")
    }

    fn skolem_cnf() -> Cnf {
        let src = "sig A {} pred p { some x: A | some x } run p for 2";
        let m = crate::parse_module(src).expect("parse");
        crate::cnf::run(&m, 0).expect("build")
    }

    fn count_models(cnf: &Cnf, extra: &[Vec<i64>]) -> usize {
        let mut s = open_rec(cnf);
        s.add_clauses(extra).expect("refine");
        let mut n = 0;
        while s.solve(&[]).expect("solve").is_some() {
            n += 1;
            assert!(s.block_last_model(None).expect("block"));
        }
        n
    }

    #[test]
    fn gated_avoid_activate_and_release() {
        let cnf = tiny_cnf();
        let mut s = open_rec(&cnf);
        let rel = find_relation(s.bounds(), "A").expect("A");
        // Avoid A={A$0}: with one primary var this is the unit [-slot].
        let avoid = s.mult_clauses(rel, MultKind::NotAll);
        assert_eq!(avoid.len(), 1);
        let base_vars = cnf.num_vars as i64;
        let sel = s.add_gated(&avoid).expect("gate");
        // Fresh selector discipline: strictly above the frozen space.
        assert!(sel > base_vars);
        assert_eq!(s.new_selector(), sel + 1);
        assert_eq!(s.stats().clauses_added, 1);
        // Activated: A forced empty.
        let inst = s.solve(&[sel]).expect("solve").expect("SAT");
        assert!(inst.tuples(rel).unwrap().is_empty());
        // Dormant: plain solve unconstrained again.
        assert!(s.solve(&[]).expect("released").is_some());
    }

    #[test]
    fn mult_no_some_notall() {
        let cnf = tiny2_cnf();
        let rel = find_relation(&cnf.bounds, "A").expect("A");
        let s = open_rec(&cnf);
        assert_eq!(s.mult_clauses(rel, MultKind::No).len(), 2);
        assert_eq!(s.mult_clauses(rel, MultKind::Some).len(), 1);
        assert_eq!(s.mult_clauses(rel, MultKind::NotAll).len(), 1);
        // `no A`: exactly 1 model ({}). `some A`: 3 models.
        assert_eq!(
            count_models(&cnf, &open_rec(&cnf).mult_clauses(rel, MultKind::No)),
            1
        );
        assert_eq!(
            count_models(&cnf, &open_rec(&cnf).mult_clauses(rel, MultKind::Some)),
            3
        );
        // `notAll A`: everything but {A$0,A$1}: 3 models.
        assert_eq!(
            count_models(&cnf, &open_rec(&cnf).mult_clauses(rel, MultKind::NotAll)),
            3
        );
    }

    #[test]
    fn mult_lone_one() {
        let cnf = tiny2_cnf();
        let rel = find_relation(&cnf.bounds, "A").expect("A");
        let s = open_rec(&cnf);
        // Pairwise single binary clause over 2 cells.
        assert_eq!(s.mult_clauses(rel, MultKind::Lone), vec![vec![-1, -2]]);
        // `lone`: {}, {0}, {1} = 3 models. `one`: {0}, {1} = 2 models.
        assert_eq!(
            count_models(&cnf, &open_rec(&cnf).mult_clauses(rel, MultKind::Lone)),
            3
        );
        assert_eq!(
            count_models(&cnf, &open_rec(&cnf).mult_clauses(rel, MultKind::One)),
            2
        );
    }

    #[test]
    fn mult_gated_lone_shares_one_selector() {
        // Multi-clause constraints gate under a single shared selector:
        // 3 cells -> 3 pairwise clauses, all weakened with the same ¬sel.
        let src = "sig A {} run { A = A } for 3";
        let m = crate::parse_module(src).expect("parse");
        let cnf = crate::cnf::run(&m, 0).expect("build");
        let mut s = open_rec(&cnf);
        let rel = find_relation(s.bounds(), "A").expect("A");
        let lone = s.mult_clauses(rel, MultKind::Lone);
        assert_eq!(lone.len(), 3);
        let before = s.stats().clauses_added;
        let sel = s.add_gated(&lone).expect("gate");
        assert_eq!(s.stats().clauses_added, before + 3);
        // Activated: at most one A atom.
        let inst = s.solve(&[sel]).expect("solve").expect("SAT");
        assert!(inst.tuples(rel).unwrap().len() <= 1);
        // Dormant: the full 8-model space is back.
        let mut n = 0;
        while s.solve(&[]).expect("solve").is_some() {
            n += 1;
            assert!(s.block_last_model(None).expect("block"));
        }
        assert_eq!(n, 8);
    }

    #[test]
    fn mult_fixed_relations_decided_by_lower() {
        let cnf = fixed_cnf();
        assert!(cnf.origins.is_empty());
        let s = open_rec(&cnf);
        let rel = find_relation(s.bounds(), "A").expect("A");
        // A fixed to {A$0}: No/NotAll violated, Some/Lone/One hold.
        assert_eq!(s.mult_clauses(rel, MultKind::No), vec![vec![]]);
        assert_eq!(s.mult_clauses(rel, MultKind::Some), Vec::<Vec<i64>>::new());
        assert_eq!(s.mult_clauses(rel, MultKind::NotAll), vec![vec![]]);
        assert_eq!(s.mult_clauses(rel, MultKind::Lone), Vec::<Vec<i64>>::new());
        assert_eq!(s.mult_clauses(rel, MultKind::One), Vec::<Vec<i64>>::new());
        // The immediate-UNSAT empty clause really is UNSAT.
        assert_eq!(count_models(&cnf, &[vec![]]), 0);
    }

    #[test]
    fn mult_by_name_rejects_unknown_and_skolem() {
        let cnf = tiny2_cnf();
        let s = open_rec(&cnf);
        assert!(s.mult_clauses_by_name("A", MultKind::Some).is_ok());
        assert!(s.mult_clauses_by_name("Nope", MultKind::Some).is_err());
        let sk = skolem_cnf();
        let ss = open_rec(&sk);
        let witness = ss
            .bounds()
            .skolems()
            .first()
            .map(|r| ss.bounds().pool().name(*r).to_string())
            .expect("skolem witness");
        assert!(ss.mult_clauses_by_name(&witness, MultKind::Some).is_err());
    }

    #[test]
    fn pin_rejects_out_of_upper() {
        let cnf = tiny_cnf();
        let mut s = open_rec(&cnf);
        // Scope is exactly 1: index 1 is outside A's upper bound.
        let mut bad = TupleSet::new(s.bounds().universe(), 1).expect("set");
        bad.insert_index(1);
        let rel = find_relation(s.bounds(), "A").expect("A");
        assert!(s.pin_units(rel, &bad).is_err());
        assert!(s.assumes_for_name("A", &bad).is_err());
        assert!(s.assumes_for_name("Nope", &bad).is_err());
    }
}
