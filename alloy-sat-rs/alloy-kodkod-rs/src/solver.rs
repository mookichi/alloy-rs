//! Solver facade: `Solver{options, bounds, formula} -> Solution`.
//!
//! This is the Rust analogue of kodkod's `Solver`/`IncrementalSolver` entry
//! point: give it an AST formula plus bounds and it runs the full pipeline
//! (FOL -> bool circuit -> CNF -> SAT -> materialized `Instance`).

use crate::ast::{AstArena, FormulaId};
use crate::bounds::Bounds;
use crate::cnf::translate_into_solver;
use crate::fol::{FolTranslator, TranslateError};
use crate::instance::Instance;
use crate::sat::SatSolver;

#[derive(Clone, Debug)]
pub struct SolverOptions {
    /// Bit width for integer encodings (1..=30).
    pub bitwidth: u32,
    /// Report translation statistics on the solution.
    pub report_stats: bool,
    /// Replace positive existentials with Skolem witness relations
    /// (equisatisfiability caveat: see `skolem` module docs).
    pub skolemize: bool,
}

impl Default for SolverOptions {
    fn default() -> Self {
        SolverOptions {
            bitwidth: 4,
            report_stats: false,
            skolemize: false,
        }
    }
}

#[derive(Debug)]
pub struct Solution {
    pub satisfiable: bool,
    pub instance: Option<Instance>,
    /// Populated by [`Solver::solve_temporal`]: the projected lasso trace.
    pub temporal: Option<crate::temporal::TemporalInstance>,
    /// Slots of every variable-relation leaf (slot, expanded relation,
    /// flat tuple index). Populated by the temporal pipeline; used for
    /// stage-1 blocking clauses in dynamic decomposition.
    pub witness_slots: Vec<(u32, crate::relation::RelationId, i64)>,
    pub num_primary_variables: usize,
    pub backend: &'static str,
}

pub struct Solver {
    options: SolverOptions,
}

impl Default for Solver {
    fn default() -> Self {
        Self::new()
    }
}

impl Solver {
    pub fn new() -> Solver {
        Solver {
            options: SolverOptions::default(),
        }
    }

    pub fn with_options(options: SolverOptions) -> Solver {
        Solver { options }
    }

    pub fn options(&self) -> &SolverOptions {
        &self.options
    }

    pub fn options_mut(&mut self) -> &mut SolverOptions {
        &mut self.options
    }

    /// Solve `formula` under `bounds` with a caller-provided SAT solver.
    ///
    /// On SAT the model is materialized into an [`Instance`].
    pub fn solve_with<S: SatSolver>(
        &self,
        solver: &mut S,
        arena: &AstArena,
        formula: FormulaId,
        bounds: &Bounds,
    ) -> Result<Solution, TranslateError> {
        let mut translator = FolTranslator::new(crate::BoolCtx::new(), bounds);
        translator.set_bitwidth(self.options.bitwidth);
        let root = translator.formula_ref(arena, formula, &[])?;
        let max_primary = translator.ctx.num_slots();
        let ctx = translator.ctx.clone();
        ctx.with_factory(|factory| translate_into_solver(solver, factory, root, max_primary))?;
        let satisfiable = SatSolver::solve(solver);
        let instance = if satisfiable {
            Some(translator.materialize(|slot| SatSolver::value_of(solver, slot as i64)))
        } else {
            None
        };
        let witness_slots: Vec<(u32, crate::relation::RelationId, i64)> = translator
            .var_origins()
            .iter()
            .map(|o| (o.slot, o.relation, o.tuple_index))
            .collect();
        Ok(Solution {
            satisfiable,
            instance,
            temporal: None,
            witness_slots,
            num_primary_variables: max_primary,
            backend: "ipasir",
        })
    }
}

#[cfg(feature = "ipasir")]
mod ipasir_impl {
    use super::*;
    use crate::ast::ExprId;
    use crate::ipasir_bridge::IpasirSolver;
    use crate::skolem::{skolemize_static, upper_bound_expr};
    use crate::temporal::{
        add_witness_relation, collect_witness_specs, expand_bounds, extract_temporal_instance,
        translate_temporal_formula, WitnessSpec,
    };
    use crate::tupleset::TupleSet;
    use std::collections::HashMap;

    impl Solver {
        /// Convenience entry point using the default IPASIR (CaDiCaL) backend.
        ///
        /// When [`SolverOptions::skolemize`] is set, positive existentials are
        /// replaced by witness relations first (on a cloned bounds set).
        pub fn solve(
            &self,
            arena: &mut AstArena,
            formula: FormulaId,
            bounds: &Bounds,
        ) -> Result<Solution, TranslateError> {
            let mut solver = IpasirSolver::new().map_err(TranslateError::Solver)?;
            if self.options.skolemize {
                let mut b2 = bounds.clone();
                let f2 = match skolemize_static(arena, &mut b2, formula)? {
                    Some(sk) => sk.formula,
                    None => formula,
                };
                let mut solution = self.solve_with(&mut solver, arena, f2, &b2)?;
                solution.backend = solver.backend_name();
                return Ok(solution);
            }
            let mut solution = self.solve_with(&mut solver, arena, formula, bounds)?;
            solution.backend = solver.backend_name();
            if self.options.report_stats {
                eprintln!(
                    "[solver] primary vars={} sat={}",
                    solution.num_primary_variables, solution.satisfiable
                );
            }
            Ok(solution)
        }

        /// Temporal entry point (Iter 7): expands the bounds over `steps`
        /// trace states, rewrites the LTL formula to FOL (future-time
        /// fragment: PRIME / always / eventually / until / releases), solves
        /// and projects the model into a lasso [`TemporalInstance`].
        ///
        /// Variable relations must be marked with `arena.set_variable(r, true)`.
        pub fn solve_temporal(
            &self,
            arena: &mut AstArena,
            formula: FormulaId,
            bounds: &Bounds,
            steps: usize,
        ) -> Result<Solution, TranslateError> {
            self.solve_temporal_with(
                arena,
                formula,
                bounds,
                steps,
                self.options.skolemize,
                &[],
                &[],
            )
        }

        /// Like [`Self::solve_temporal`] with explicit skolemization control,
        /// optional stage-2 anchors (dynamic decomposition) and extra clauses
        /// (blocking clauses for stage-1 exploration).
        #[allow(clippy::too_many_arguments)]
        pub fn solve_temporal_with(
            &self,
            arena: &mut AstArena,
            formula: FormulaId,
            bounds: &Bounds,
            steps: usize,
            skolemize: bool,
            anchors: &[(crate::relation::RelationId, TupleSet)],
            extra_clauses: &[Vec<i64>],
        ) -> Result<Solution, TranslateError> {
            // HASLab witnesses: collect OUTERMOST totality-context existentials
            let mut specs: Vec<WitnessSpec> = Vec::new();
            if skolemize {
                collect_witness_specs(
                    arena, bounds, formula, true, true, false, &mut specs, &mut 0,
                );
            }
            let mut expansion = expand_bounds(arena, bounds, steps, 1)?;
            for &(orig, ref ts) in anchors {
                let ere = *expansion
                    .mapping
                    .get(&orig)
                    .ok_or(TranslateError::UnboundRelation(orig.0))?;
                expansion.anchor_relation(ere, ts)?;
            }
            let mut witnesses: HashMap<crate::ast::VarId, crate::relation::RelationId> =
                HashMap::new();
            let mut witness_domains: Vec<(crate::relation::RelationId, ExprId)> = Vec::new();
            for sp in &specs {
                let upper = upper_bound_expr(arena, sp.domain, bounds)
                    .expect("collected specs have computable upper bounds");
                let rel =
                    add_witness_relation(&mut expansion, arena, &sp.name, sp.value_arity, &upper)?;
                witnesses.insert(sp.var, rel);
                witness_domains.push((rel, sp.domain));
            }
            let rewritten = translate_temporal_formula(
                arena,
                formula,
                &expansion,
                &witnesses,
                &witness_domains,
            )?;
            let mut solver = IpasirSolver::new().map_err(TranslateError::Solver)?;
            for cl in extra_clauses {
                solver.add_clause(cl);
            }
            let mut solution = self.solve_with(&mut solver, arena, rewritten, &expansion.bounds)?;
            solution.temporal = if solution.satisfiable {
                let inst = solution.instance.as_ref().expect("SAT implies instance");
                Some(extract_temporal_instance(inst, &expansion)?)
            } else {
                None
            };
            Ok(solution)
        }

        /// Static component decomposition (Iter 8): top-level conjuncts are
        /// grouped into connected components over shared relations, solved
        /// independently, and their instances merged. Serial.
        pub fn solve_decomposed(
            &self,
            arena: &mut AstArena,
            formula: FormulaId,
            bounds: &Bounds,
        ) -> Result<Solution, TranslateError> {
            crate::pardinus::solve_static_components(self, arena, formula, bounds)
        }

        /// Parallel variant of [`Self::solve_decomposed`] (backlog 3):
        /// component groups are solved on a bounded worker pool. Requires
        /// `AstArena: Clone` (each worker gets its own copy).
        pub fn solve_decomposed_parallel(
            &self,
            arena: &mut AstArena,
            formula: FormulaId,
            bounds: &Bounds,
            max_threads: usize,
        ) -> Result<Solution, TranslateError> {
            crate::pardinus::solve_static_components_parallel(
                self,
                arena,
                formula,
                bounds,
                max_threads,
            )
        }

        /// Dynamic two-stage decomposition (Iter 8): slice the formula by the
        /// partial relations of a [`crate::pardinus::PardinusBounds`], solve
        /// the partial problem, anchor it, and complete.
        pub fn solve_dynamic(
            &self,
            arena: &mut AstArena,
            formula: FormulaId,
            pb: &crate::pardinus::PardinusBounds,
            steps: usize,
        ) -> Result<Solution, TranslateError> {
            crate::pardinus::solve_dynamic(self, arena, formula, pb, steps)
        }
    }
}
