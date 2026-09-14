//! CEGIS driver (v1): synthesizer/verifier loop over persistent sessions.
//!
//! - `synth` session proposes candidates (hole relations take values).
//! - `verifier` session checks `¬spec` under an exact candidate pin expressed
//!   as *temporary assumes* (the verifier session is never mutated).
//! - On counterexample, the candidate's hole projection is excluded from
//!   `synth` as one permanent blocking clause (v1 default: hole-projection
//!   nogood; stronger counterexample generalization is v2).
//!
//! Both sessions keep their learned clauses across iterations; only the
//! refinement clauses grow. `synth` and `verifier` must share the universe
//! shape (same module/scope); mismatches are resolution errors, not UNSAT.

use alloy_kodkod_rs::instance::Instance;
use alloy_kodkod_rs::relation::RelationId;

use crate::cnf::Cnf;
use crate::incremental::{find_relation, IncrementalSession, SessionStats};
use crate::partial::{verifier_pin_from_partial, PartialInstance};
use crate::FrontError;

/// CEGIS loop configuration (v1).
#[derive(Debug, Clone)]
pub struct CegisConfig {
    /// Maximum synthesizer solves (0 => immediate timeout).
    pub max_iters: usize,
    /// Hole relations forming a candidate (projected blocking scope).
    /// Skolem witnesses are rejected.
    pub holes: Vec<String>,
    /// When the hole projection covers no primary variables, block the full
    /// model instead of stalling. `false` => timeout in that case.
    pub full_block_fallback: bool,
}

impl Default for CegisConfig {
    fn default() -> Self {
        CegisConfig {
            max_iters: 100,
            holes: Vec::new(),
            full_block_fallback: true,
        }
    }
}

/// CEGIS loop outcome. `iters` counts synthesizer solves performed.
#[derive(Debug)]
pub enum CegisOutcome {
    /// Verifier UNSAT under the candidate pin: candidate satisfies spec.
    Valid { candidate: Instance, iters: usize },
    /// Synthesizer UNSAT: no (more) candidates.
    NoCandidate { iters: usize },
    /// Iteration or progress budget exhausted.
    Timeout { iters: usize },
}

/// Outcome plus per-session measurement counters.
#[derive(Debug)]
pub struct CegisReport {
    pub outcome: CegisOutcome,
    pub synth_stats: SessionStats,
    pub verifier_stats: SessionStats,
}

fn report(
    outcome: CegisOutcome,
    synth: &IncrementalSession,
    verifier: &IncrementalSession,
) -> CegisReport {
    CegisReport {
        outcome,
        synth_stats: synth.stats(),
        verifier_stats: verifier.stats(),
    }
}

/// Run the CEGIS loop to a [`CegisOutcome`].
pub fn run_cegis(synth: &Cnf, verify: &Cnf, cfg: &CegisConfig) -> Result<CegisReport, FrontError> {
    if cfg.holes.is_empty() {
        return Err(FrontError::Resolve(
            "cegis needs at least one hole relation".into(),
        ));
    }
    // Resolve holes in the synthesizer (names, never cross-session ids).
    let mut hole_ids: Vec<(String, RelationId)> = Vec::new();
    for h in &cfg.holes {
        let r = find_relation(&synth.bounds, h)
            .ok_or_else(|| FrontError::Resolve(format!("synth has no relation `{h}`")))?;
        if synth.bounds.pool().is_skolem(r) {
            return Err(FrontError::Resolve(format!(
                "hole `{h}` is a skolem witness (cannot pin)"
            )));
        }
        hole_ids.push((h.clone(), r));
    }

    let mut synth_s = IncrementalSession::open(synth)?;
    let mut ver_s = IncrementalSession::open(verify)?;
    let mut iters = 0usize;

    loop {
        if iters >= cfg.max_iters {
            return Ok(report(CegisOutcome::Timeout { iters }, &synth_s, &ver_s));
        }
        let candidate = match synth_s.solve(&[])? {
            None => {
                return Ok(report(
                    CegisOutcome::NoCandidate { iters },
                    &synth_s,
                    &ver_s,
                ));
            }
            Some(inst) => inst,
        };
        iters += 1;

        // Exact candidate pin on the verifier (temporary assumes).
        // The candidate is snapshotted to a `PartialInstance` first so the
        // file-backed path (`verifier_pin_from_partial`) shares one checked
        // implementation with the live path (same name/arity/universe/upper
        // checks as the former inline hole loop).
        let hole_names: Vec<&str> = hole_ids.iter().map(|(h, _)| h.as_str()).collect();
        let partial = PartialInstance::extract(&candidate, Some(&hole_names))?;
        let assumes = verifier_pin_from_partial(&ver_s, &partial, &hole_names)?;

        match ver_s.solve(&assumes)? {
            // UNSAT under the pin: candidate satisfies the spec.
            None => {
                return Ok(report(
                    CegisOutcome::Valid { candidate, iters },
                    &synth_s,
                    &ver_s,
                ));
            }
            // Counterexample: exclude this hole projection from synth.
            Some(_) => {
                let mut block = block_of(&synth_s, &hole_ids, &candidate);
                if block.is_empty() && cfg.full_block_fallback {
                    block = block_of_all(&synth_s, &candidate);
                }
                if block.is_empty() {
                    return Ok(report(CegisOutcome::Timeout { iters }, &synth_s, &ver_s));
                }
                synth_s.add_clauses(std::slice::from_ref(&block))?;
            }
        }
    }
}

/// Blocking clause negating `candidate` restricted to `holes`.
fn block_of(
    sess: &IncrementalSession,
    holes: &[(String, RelationId)],
    candidate: &Instance,
) -> Vec<i64> {
    let mut block = Vec::new();
    for o in sess.origins() {
        if !holes.iter().any(|(_, r)| *r == o.relation) {
            continue;
        }
        let present = candidate
            .tuples(o.relation)
            .map(|t| t.contains_index(o.tuple_index))
            .unwrap_or(false);
        let lit = o.slot as i64;
        block.push(if present { -lit } else { lit });
    }
    block
}

/// Full-model blocking clause (fallback when the projection is vacuous).
fn block_of_all(sess: &IncrementalSession, candidate: &Instance) -> Vec<i64> {
    let mut block = Vec::new();
    for o in sess.origins() {
        let present = candidate
            .tuples(o.relation)
            .map(|t| t.contains_index(o.tuple_index))
            .unwrap_or(false);
        let lit = o.slot as i64;
        block.push(if present { -lit } else { lit });
    }
    block
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{parse_module, validate};

    fn build(src: &str, idx: usize, kind: &str) -> Cnf {
        let m = parse_module(src).expect("parse");
        match kind {
            "run" => crate::cnf::run(&m, idx).expect("run build"),
            _ => crate::cnf::check(&m, idx).expect("check build"),
        }
    }

    #[test]
    fn converges_and_candidate_validates() {
        // synth: any A (the tautology body forces A's leaf to exist; an
        // empty `run {}` would compile to constant-true with no primary
        // variables). verifier: negated `some A`, pinned to the candidate.
        // An empty-A first candidate refines; a nonempty first candidate
        // validates immediately. Either way the outcome is Valid.
        let src = r#"
            sig A {}
            assert someA { some A }
            run { A = A } for 2
            check someA for 2
        "#;
        let synth = build(src, 0, "run");
        let verify = build(src, 1, "check");
        let cfg = CegisConfig {
            max_iters: 8,
            holes: vec!["A".to_string()],
            full_block_fallback: true,
        };
        let rep = run_cegis(&synth, &verify, &cfg).expect("cegis");
        match rep.outcome {
            CegisOutcome::Valid { candidate, iters } => {
                assert!((1..=8).contains(&iters));
                assert!(validate(&synth, &candidate).is_some());
                // synth solved `iters` times, verifier `iters` times.
                assert_eq!(rep.synth_stats.solves, iters);
                assert_eq!(rep.verifier_stats.solves, iters);
            }
            other => panic!("expected Valid, got {other:?}"),
        }
    }

    #[test]
    fn no_candidate_when_synth_unsat() {
        let src = r#"
            sig A {}
            fact { no A }
            run { some A } for 2
            check { some A } for 2
        "#;
        let synth = build(src, 0, "run");
        let verify = build(src, 1, "check");
        let cfg = CegisConfig {
            max_iters: 8,
            holes: vec!["A".to_string()],
            ..Default::default()
        };
        let rep = run_cegis(&synth, &verify, &cfg).expect("cegis");
        assert!(matches!(
            rep.outcome,
            CegisOutcome::NoCandidate { iters: 0 }
        ));
    }

    #[test]
    fn zero_budget_times_out() {
        let src = r#"
            sig A {}
            run {} for 2
            check { some A } for 2
        "#;
        let synth = build(src, 0, "run");
        let verify = build(src, 1, "check");
        let cfg = CegisConfig {
            max_iters: 0,
            holes: vec!["A".to_string()],
            ..Default::default()
        };
        let rep = run_cegis(&synth, &verify, &cfg).expect("cegis");
        assert!(matches!(rep.outcome, CegisOutcome::Timeout { iters: 0 }));
    }

    #[test]
    fn rejects_bad_config() {
        let src = "sig A {} run {} for 2";
        let m = parse_module(src).expect("parse");
        let synth = crate::cnf::run(&m, 0).expect("build");
        let bad_empty = CegisConfig {
            holes: vec![],
            ..Default::default()
        };
        assert!(run_cegis(&synth, &synth, &bad_empty).is_err());
        let bad_hole = CegisConfig {
            holes: vec!["Nope".to_string()],
            ..Default::default()
        };
        assert!(run_cegis(&synth, &synth, &bad_hole).is_err());
    }
}
