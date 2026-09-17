//! MaxSAT-style optimization (Iter 13): OLL/Fu-Malik core-guided loop.
//!
//! Three objective kinds are supported:
//!
//! * [`Objective::Int`] — maximize/minimize a single integer (`IntId`)
//!   expression. The lowered [`IntCircuit`](crate::int::IntCircuit) bits
//!   (little-endian two's complement) become weighted soft unit clauses:
//!   bit `i` carries weight `2^i`, and maximizing the signed value is
//!   reduced to maximizing `v + 2^(w-1)` (i.e. the sign bit is rewarded
//!   negated).
//! * [`Objective::Weighted`] — maximize/minimize `sum(w_r * #r)` over
//!   relations. Every variable cell of a weighted relation (see
//!   [`FolTranslator::var_origins`](crate::fol::FolTranslator::var_origins))
//!   becomes a soft unit clause with its relation's weight. This finally
//!   wires [`PardinusBounds::weights`](crate::pardinus::PardinusBounds::weights)
//!   (previously recorded-but-unused) into the SAT layer.
//! * [`Objective::And`] — reward conjunctions of two bound cells without
//!   any counting circuit (one AND gate + unit soft per pair). This is
//!   the fast path for `#(R & S)`-shaped objectives over large models.
//!
//! Mechanism: each soft clause is selector-guarded (`soft ∨ ¬sel`) and the
//! selectors are passed as SAT *assumptions*. On UNSAT the backend's
//! [`failed_core`](crate::sat::SatSolver::failed_core) names the culprit
//! softs; they are relaxed with fresh variables, weight-split at the
//! core's minimum weight (OLL), and an exactly-one constraint over the
//! relaxation variables is added as hard clauses. The single solver
//! session is kept across iterations, so conflict state is inherited.
//! The first SAT model is optimal; its exact cost is re-evaluated from
//! the materialized [`Instance`] (relation cardinalities /
//! [`Evaluator::int_value`](crate::eval::Evaluator::int_value)), never
//! from soft-clause arithmetic.
//!
//! Requirements: a [`SatSolver`] with assumption support (CaDiCaL via
//! [`IpasirSolver`](crate::ipasir_bridge::IpasirSolver),
//! [`RecordingSolver`](crate::sat::RecordingSolver)); splr-style
//! backends without assumptions are rejected with an error.

use std::collections::{HashMap, HashSet};

use crate::ast::{AstArena, FormulaId, IntId};
use crate::bool::{BoolFactory, BoolRef};
use crate::bounds::Bounds;
use crate::cnf::{translate_conjunct_def, RootCnf};
use crate::eval::Evaluator;
use crate::fol::{FolTranslator, TranslateError};
use crate::instance::Instance;
use crate::relation::RelationId;
use crate::sat::SatSolver;

/// Optimization sense.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OptSense {
    Maximize,
    Minimize,
}

/// A single bound cell: (relation, flat tuple index).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CellRef {
    pub relation: RelationId,
    pub tuple_index: i64,
}

/// Objective function to optimize.
#[derive(Clone, Debug)]
pub enum Objective {
    /// Maximize/minimize a single integer expression.
    Int { id: IntId, sense: OptSense },
    /// Maximize/minimize `sum(w_r * #r)`. Relations absent from the map
    /// carry weight 0 (ignored).
    Weighted {
        weights: HashMap<RelationId, i64>,
        sense: OptSense,
    },
    /// Reward conjunctions of two cells: each `(a, b, w)` earns `w` iff
    /// both cells hold. This expresses `#(R & S)`-style objectives
    /// without the counting circuit (one AND gate + unit soft per pair);
    /// bound-forced cells fold away.
    And {
        pairs: Vec<(CellRef, CellRef, i64)>,
        sense: OptSense,
    },
    /// Use only translation-collected softs (AlloyMax `maxsome` /
    /// `minsome` / `soft fact` nodes in the formula). Errors when the
    /// translation collects nothing.
    Collected,
}

impl Objective {
    pub fn max_int(id: IntId) -> Objective {
        Objective::Int {
            id,
            sense: OptSense::Maximize,
        }
    }

    pub fn min_int(id: IntId) -> Objective {
        Objective::Int {
            id,
            sense: OptSense::Minimize,
        }
    }

    pub fn max_weighted(weights: HashMap<RelationId, i64>) -> Objective {
        Objective::Weighted {
            weights,
            sense: OptSense::Maximize,
        }
    }

    pub fn min_weighted(weights: HashMap<RelationId, i64>) -> Objective {
        Objective::Weighted {
            weights,
            sense: OptSense::Minimize,
        }
    }

    pub fn max_and(pairs: Vec<(CellRef, CellRef, i64)>) -> Objective {
        Objective::And {
            pairs,
            sense: OptSense::Maximize,
        }
    }

    pub fn min_and(pairs: Vec<(CellRef, CellRef, i64)>) -> Objective {
        Objective::And {
            pairs,
            sense: OptSense::Minimize,
        }
    }

    /// Optimize translation-collected softs only (AlloyMax surface).
    pub fn collected() -> Objective {
        Objective::Collected
    }

    /// Builds a maximization objective from Pardinus target weights.
    pub fn max_from_pardinus(pb: &crate::pardinus::PardinusBounds) -> Objective {
        Objective::max_weighted(pb.weights().clone())
    }

    /// Builds a minimization objective from Pardinus target weights.
    pub fn min_from_pardinus(pb: &crate::pardinus::PardinusBounds) -> Objective {
        Objective::min_weighted(pb.weights().clone())
    }

    fn sense(&self) -> OptSense {
        match self {
            Objective::Int { sense, .. } => *sense,
            Objective::Weighted { sense, .. } => *sense,
            Objective::And { sense, .. } => *sense,
            // Collected entries carry their own sense (minsome is
            // negated at collection); the loop maximizes their sum.
            Objective::Collected => OptSense::Maximize,
        }
    }
}

/// Result of [`solve_opt_with`].
#[derive(Debug)]
pub struct OptSolution {
    /// Whether the hard formula is satisfiable. `false` implies
    /// `instance`/`cost` are `None`.
    pub satisfiable: bool,
    /// Optimal model. Populated on SAT.
    pub instance: Option<Instance>,
    /// Exact objective value of `instance`. Populated on SAT.
    pub cost: Option<i64>,
    /// Number of `solve()` calls issued (initial feasibility + loop).
    pub sat_calls: usize,
    pub num_primary_variables: usize,
    /// Projected lasso trace for temporal optimization (populated by the
    /// temporal optimizer path; `None` for static optimization).
    /// `instance` then holds the flat time-expanded model.
    pub temporal: Option<crate::temporal::TemporalInstance>,
}

/// Core-guided optimization generic over any assumption-capable
/// [`SatSolver`]. See the [module docs](self) for the mechanism.
pub fn solve_opt_with<S: SatSolver>(
    solver: &mut S,
    bitwidth: u32,
    arena: &AstArena,
    formula: FormulaId,
    bounds: &Bounds,
    objective: Objective,
) -> Result<OptSolution, TranslateError> {
    if !solver.supports_assumptions() {
        return Err(TranslateError::Solver(
            "optimization requires a SAT solver with assumption support \
             (e.g. IpasirSolver/CaDiCaL)"
                .into(),
        ));
    }
    let mut translator = FolTranslator::new(crate::BoolCtx::new(), bounds);
    translator.set_bitwidth(bitwidth);
    let root = translator.formula_ref(arena, formula, &[])?;

    // Relations appearing in cell objectives need leaf circuits (and
    // hence primary slots) even when the formula never mentions them.
    {
        use std::collections::BTreeSet;
        let mut rels: BTreeSet<RelationId> = BTreeSet::new();
        match &objective {
            Objective::Weighted { weights, .. } => {
                rels.extend(weights.iter().filter(|(_, &w)| w != 0).map(|(&r, _)| r));
            }
            Objective::And { pairs, .. } => {
                for (a, b, w) in pairs {
                    if *w != 0 {
                        rels.insert(a.relation);
                        rels.insert(b.relation);
                    }
                }
            }
            // Collected softs resolve their own leaves during translation.
            Objective::Int { .. } | Objective::Collected => {}
        }
        for r in rels {
            translator.ensure_relation(r)?;
        }
    }

    // Lower the objective circuit (shares the translator's BoolCtx so
    // gates — and primary slots — coincide with the formula's).
    let int_bits: Option<Vec<BoolRef>> = match &objective {
        Objective::Int { id, .. } => {
            let circ = translator.int_expr(arena, *id, &[])?;
            Some(circ.bits.clone())
        }
        Objective::Weighted { .. } | Objective::And { .. } | Objective::Collected => None,
    };
    let max_primary = translator.ctx.num_slots();
    let ctx = translator.ctx.clone();
    // Register every primary slot up front. Later emissions do this
    // per-call, but paths with no CNF emission yet (trivially-true
    // formula, raw-slot softs) would otherwise leave the solver
    // under-registered and strict backends (RecordingSolver) silently
    // drop clauses referencing unregistered variables.
    if solver.num_variables() < max_primary {
        solver.add_variables(max_primary - solver.num_variables());
    }
    // Fresh-variable stream for AND gates below and OLL selectors later.
    // Re-synced after every emission phase (emitters register their own
    // variables internally).
    let mut next_var = solver.num_variables() as i64;

    // Hard part: full-definition translation + asserted root.
    if root.is_const() && !root.const_value() {
        return Ok(unsat_solution(max_primary));
    }
    if !root.is_const() {
        let lit = ctx.with_factory(|factory| {
            translate_conjunct_def(solver, factory, root, max_primary)
        })?;
        match lit {
            RootCnf::Lit(l) => {
                solver.add_clause(&[l]);
            }
            _ => unreachable!("non-constant root yields a literal"),
        }
    }

    // Soft unit clauses over CNF literals: (lit, weight > 0).
    // For Minimize the literal polarity is flipped, turning the loop
    // into a maximization of the negated sum; the reported cost is
    // always re-evaluated from the model.
    let minimize = objective.sense() == OptSense::Minimize;
    let mut softs: Vec<(i64, i64)> = Vec::new();
    match &objective {
        Objective::Weighted { weights, .. } => {
            for o in translator.var_origins() {
                let w = weights.get(&o.relation).copied().unwrap_or(0);
                if w == 0 {
                    continue;
                }
                let slot = o.slot as i64;
                let (lit, weight) = if w > 0 { (slot, w) } else { (-slot, -w) };
                softs.push((if minimize { -lit } else { lit }, weight));
            }
        }
        Objective::Int { .. } => {
            let bits = int_bits.expect("int objective lowers bits");
            let w = bits.len();
            if w > 0 {
                for (i, &b) in bits.iter().enumerate() {
                    if b.is_const() {
                        continue; // fixed offset: irrelevant to the argmax
                    }
                    let weight: i64 = 1i64 << (w - 1); // top bit weight
                    let weight = if i + 1 < w { 1i64 << i } else { weight };
                    // Maximizing the signed value = maximizing v + 2^(w-1),
                    // i.e. the sign bit is rewarded negated.
                    let lit = emit_lit(solver, &ctx, b, max_primary)?;
                    next_var = next_var.max(solver.num_variables() as i64);
                    let lit = if i + 1 == w { -lit } else { lit };
                    softs.push((if minimize { -lit } else { lit }, weight));
                }
            }
        }
        Objective::And { pairs, .. } => {
            let mut slots: HashMap<(RelationId, i64), u32> = HashMap::new();
            for o in translator.var_origins() {
                slots.insert((o.relation, o.tuple_index), o.slot);
            }
            for (a, b, w) in pairs {
                if *w == 0 {
                    continue;
                }
                let la = cell_lit(bounds, &slots, a)?;
                let lb = cell_lit(bounds, &slots, b)?;
                // Maximize-direction literal; Minimize flips at push time.
                let lit = match (la, lb) {
                    (CellVal::False, _) | (_, CellVal::False) => continue,
                    (CellVal::True, CellVal::True) => continue, // fixed offset
                    (CellVal::True, CellVal::Slot(s))
                    | (CellVal::Slot(s), CellVal::True) => s,
                    (CellVal::Slot(x), CellVal::Slot(y)) => {
                        // Fresh gate g ⟺ x ∧ y (full definition).
                        next_var += 1;
                        solver.add_variables(1);
                        let g = next_var;
                        solver.add_clause(&[-g, x]);
                        solver.add_clause(&[-g, y]);
                        solver.add_clause(&[-x, -y, g]);
                        g
                    }
                };
                let (lit, weight) = if *w > 0 { (lit, *w) } else { (-lit, -*w) };
                softs.push((if minimize { -lit } else { lit }, weight));
            }
            next_var = next_var.max(solver.num_variables() as i64);
        }
        // No objective-level softs for the Collected mode.
        Objective::Collected => {}
    }
    // Translation-collected softs (AlloyMax `maxsome` / `minsome` /
    // `soft fact` nodes): emit full definitions, then pool with the
    // objective softs. Entries are already maximize-direction
    // (`minsome` is negated at collection); cost accounting below
    // complements `minimize` entries back to natural values.
    let mut collected_units: Vec<(i64, i64, bool)> = Vec::new();
    // Clone: `translator` is borrowed below via `ctx` closures.
    let collected_roots: Vec<crate::fol::SoftEntry> = translator.softs.clone();
    for entry in &collected_roots {
        let lit = emit_lit(solver, &ctx, entry.root, max_primary)?;
        next_var = next_var.max(solver.num_variables() as i64);
        softs.push((lit, entry.weight));
        collected_units.push((lit, entry.weight, entry.minimize));
    }
    if matches!(objective, Objective::Collected) && collected_units.is_empty() {
        return Err(TranslateError::Solver(
            "objective Collected but the formula collected no soft \
             constraints (no maxsome/minsome/soft fact)"
                .into(),
        ));
    }
    merge_softs(&mut softs);

    // Feasibility probe under no assumptions: UNSAT here means the hard
    // formula itself is unsatisfiable (reported, not an error).
    let mut sat_calls = 1;
    if !solver.solve() {
        return Ok(unsat_solution(max_primary));
    }

    if softs.is_empty() {
        // Constant objective: the feasible model is trivially optimal.
        let instance =
            Some(translator.materialize(|slot| SatSolver::value_of(solver, slot as i64)));
        let mut cost = eval_cost(arena, &objective, instance.as_ref().unwrap())?;
        cost = add_collected_cost(cost, solver, &collected_units)?;
        return Ok(OptSolution {
            satisfiable: true,
            instance,
            cost: Some(cost),
            sat_calls,
            num_primary_variables: max_primary,
            temporal: None,
        });
    }

    // OLL loop state: each item is (clause incl. relax lits, weight,
    // selector, active). Fresh SAT variables continue past everything
    // allocated above (re-sync: emitters register their own variables).
    // NOTE: allocating at or below max_primary would alias selectors
    // onto primary variables (tautological soft clauses + stray
    // assumptions = silently wrong optima).
    next_var = next_var.max(solver.num_variables() as i64);
    let mut items: Vec<Work> = Vec::new();
    for &(lit, weight) in &softs {
        next_var += 1;
        solver.add_variables(1);
        let sel = next_var;
        solver.add_clause(&[lit, -sel]);
        items.push(Work {
            clause: vec![lit],
            weight,
            sel,
            active: true,
        });
    }
    let total_weight: i64 = softs
        .iter()
        .try_fold(0i64, |acc, &(_, w)| acc.checked_add(w))
        .ok_or_else(|| TranslateError::Solver("objective weights overflow i64".into()))?;
    // Every round raises the proven bound by >= 1, so this cap is only
    // a backstop against solver misbehavior, never a real limit.
    let max_rounds = total_weight
        .checked_add(items.len() as i64 + 8)
        .ok_or_else(|| TranslateError::Solver("objective weights overflow i64".into()))?;

    let mut rounds: i64 = 0;
    loop {
        let mut sel_to_idx: HashMap<i64, usize> = HashMap::new();
        for (i, it) in items.iter().enumerate() {
            if it.active {
                SatSolver::assume(solver, it.sel);
                sel_to_idx.insert(it.sel, i);
            }
        }
        sat_calls += 1;
        if solver.solve() {
            let instance =
                Some(translator.materialize(|slot| SatSolver::value_of(solver, slot as i64)));
            let mut cost = eval_cost(arena, &objective, instance.as_ref().unwrap())?;
            cost = add_collected_cost(cost, solver, &collected_units)?;
            return Ok(OptSolution {
                satisfiable: true,
                instance,
                cost: Some(cost),
                sat_calls,
                num_primary_variables: max_primary,
                temporal: None,
            });
        }
        // Core inheritance: the failed selectors name the culprits.
        let mut core: Vec<usize> = Vec::new();
        let mut seen = HashSet::new();
        for sel in solver.failed_core() {
            if let Some(&i) = sel_to_idx.get(&sel) {
                if seen.insert(i) {
                    core.push(i);
                }
            }
        }
        if core.is_empty() {
            // Backend reported nothing usable: minimize over all active
            // selectors (RCE-style single-removal pass). An empty result
            // means the hard part is UNSAT after all.
            core = deletion_filter(solver, &items, &mut sat_calls);
            if core.is_empty() {
                return Ok(unsat_solution(max_primary));
            }
        }
        let w_min = core.iter().map(|&i| items[i].weight).min().unwrap();
        debug_assert!(w_min > 0);

        let mut relax_vars: Vec<i64> = Vec::new();
        let mut residuals: Vec<(Vec<i64>, i64)> = Vec::new();
        for &i in &core {
            next_var += 1;
            solver.add_variables(1);
            relax_vars.push(next_var);
            if items[i].weight > w_min {
                residuals.push((items[i].clause.clone(), items[i].weight - w_min));
            }
            items[i].clause.push(next_var);
            items[i].weight = w_min;
        }
        for (clause, weight) in residuals {
            next_var += 1;
            solver.add_variables(1);
            let sel = next_var;
            let mut full = clause.clone();
            full.push(-sel);
            solver.add_clause(&full);
            items.push(Work {
                clause,
                weight,
                sel,
                active: true,
            });
        }
        for &i in &core {
            next_var += 1;
            solver.add_variables(1);
            let sel = next_var;
            let mut full = items[i].clause.clone();
            full.push(-sel);
            solver.add_clause(&full);
            items[i].sel = sel;
        }
        // Exactly-one over the relaxation variables: precisely one
        // w_min slice of this core is paid.
        if relax_vars.len() == 1 {
            solver.add_clause(&[relax_vars[0]]);
        } else {
            for (a, &ra) in relax_vars.iter().enumerate() {
                for &rb in &relax_vars[a + 1..] {
                    solver.add_clause(&[-ra, -rb]);
                }
            }
            solver.add_clause(&relax_vars);
        }
        rounds += 1;
        if rounds > max_rounds {
            return Err(TranslateError::Solver(
                "optimization loop exceeded its round cap; solver core reports are inconsistent"
                    .into(),
            ));
        }
    }
}

/// A bound cell resolved to a truth value: forced by bounds, or a live
/// primary slot (positive literal = the cell holds).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CellVal {
    True,
    False,
    Slot(i64),
}

/// Resolves a cell to [`CellVal`]: forced-true when in the lower bound,
/// forced-false when outside the upper bound, else its primary slot.
fn cell_lit(
    bounds: &Bounds,
    slots: &HashMap<(RelationId, i64), u32>,
    c: &CellRef,
) -> Result<CellVal, TranslateError> {
    if let Some(lo) = bounds.lower_bound(c.relation) {
        if lo.contains_index(c.tuple_index) {
            return Ok(CellVal::True);
        }
    } else {
        return Err(TranslateError::UnboundRelation(c.relation.0));
    }
    // Mirror leaf_relation: missing upper defaults to the lower (exact).
    let in_upper = match bounds.upper_bound(c.relation) {
        Some(up) => up.contains_index(c.tuple_index),
        None => false, // not in lower (checked above) and no upper
    };
    if !in_upper {
        return Ok(CellVal::False);
    }
    match slots.get(&(c.relation, c.tuple_index)) {
        Some(&s) => Ok(CellVal::Slot(s as i64)),
        None => Err(TranslateError::Solver(
            "objective cell has no primary slot (relation not visited)".into(),
        )),
    }
}

/// Emits full (both-polarity) definitions for `r` and returns its signed
/// CNF literal. Callers must have excluded constants.
fn emit_lit<S: SatSolver>(
    solver: &mut S,
    ctx: &crate::BoolCtx,
    r: BoolRef,
    max_primary: usize,
) -> Result<i64, TranslateError> {
    debug_assert!(!r.is_const());
    let lit = ctx.with_factory(|factory: &BoolFactory| {
        translate_conjunct_def(solver, factory, r, max_primary)
    })?;
    match lit {
        RootCnf::Lit(l) => Ok(l),
        _ => unreachable!("non-constant root yields a literal"),
    }
}

/// Merges duplicate soft literals by summing weights (checked); drops
/// zero-weight entries. Keeps the loop's weight-splitting sound.
fn merge_softs(softs: &mut Vec<(i64, i64)>) {
    let mut merged: HashMap<i64, i64> = HashMap::new();
    for &(lit, w) in softs.iter() {
        // Weights are small in practice; saturate rather than fail on
        // pathological duplicates.
        let e = merged.entry(lit).or_insert(0);
        *e = e.saturating_add(w);
    }
    softs.clear();
    for (lit, w) in merged {
        if w > 0 {
            softs.push((lit, w));
        }
    }
    softs.sort_unstable();
}

/// One working soft clause: body (accumulated relaxation literals
/// included), remaining weight, current selector, and activity flag.
struct Work {
    clause: Vec<i64>,
    weight: i64,
    sel: i64,
    active: bool,
}

/// RCE-style fallback: single-removal minimization over all active
/// selectors when the backend reports an empty failed core.
fn deletion_filter<S: SatSolver>(
    solver: &mut S,
    items: &[Work],
    sat_calls: &mut usize,
) -> Vec<usize> {
    let mut core: Vec<usize> = items
        .iter()
        .enumerate()
        .filter(|(_, it)| it.active)
        .map(|(i, _)| i)
        .collect();
    let mut i = 0;
    while i < core.len() {
        let trial: Vec<i64> = core
            .iter()
            .enumerate()
            .filter(|(j, _)| *j != i)
            .map(|(_, &k)| items[k].sel)
            .collect();
        for &lit in &trial {
            SatSolver::assume(solver, lit);
        }
        *sat_calls += 1;
        if !solver.solve() {
            core.remove(i);
        } else {
            i += 1;
        }
    }
    core
}

fn unsat_solution(max_primary: usize) -> OptSolution {
    OptSolution {
        satisfiable: false,
        instance: None,
        cost: None,
        sat_calls: 1,
        num_primary_variables: max_primary,
        temporal: None,
    }
}

/// Exact objective value of a materialized instance.
fn eval_cost(
    arena: &AstArena,
    objective: &Objective,
    instance: &Instance,
) -> Result<i64, TranslateError> {
    match objective {
        Objective::Int { id, .. } => {
            let ev = Evaluator::new(instance);
            Ok(ev.int_value(arena, *id, &Vec::new())?)
        }
        Objective::Weighted { weights, .. } => {
            let mut total = 0i64;
            for (&r, &w) in weights {
                if w == 0 {
                    continue;
                }
                let card = instance.tuples(r).map(|ts| ts.len() as i64).unwrap_or(0);
                total = total
                    .checked_add(card.checked_mul(w).ok_or_else(|| {
                        TranslateError::Solver("objective cost overflow i64".into())
                    })?)
                    .ok_or_else(|| TranslateError::Solver("objective cost overflow i64".into()))?;
            }
            Ok(total)
        }
        Objective::And { pairs, .. } => {
            // Natural (maximize-direction) value; sense only steers search.
            let mut total = 0i64;
            for (a, b, w) in pairs {
                if cell_holds(instance, a) && cell_holds(instance, b) {
                    total = total.checked_add(*w).ok_or_else(|| {
                        TranslateError::Solver("objective cost overflow i64".into())
                    })?;
                }
            }
            Ok(total)
        }
        // Translation-collected softs are evaluated from the solver
        // model by the caller; nothing instance-level to add here.
        Objective::Collected => Ok(0),
    }
}

/// Adds translation-collected earnings (read from the final solver
/// model) to an instance-evaluated cost. `minimize` entries are
/// complemented back to natural (minimization-direction) values.
fn add_collected_cost<S: SatSolver>(
    base: i64,
    solver: &S,
    collected: &[(i64, i64, bool)],
) -> Result<i64, TranslateError> {
    let mut total = base;
    for &(lit, w, minimize) in collected {
        let holds = SatSolver::value_of(solver, lit);
        let earned = if minimize { !holds } else { holds };
        if earned {
            total = total.checked_add(w).ok_or_else(|| {
                TranslateError::Solver("objective cost overflow i64".into())
            })?;
        }
    }
    Ok(total)
}

/// Whether a cell holds in a materialized instance.
fn cell_holds(instance: &Instance, c: &CellRef) -> bool {
    instance
        .tuples(c.relation)
        .map(|ts| ts.contains_index(c.tuple_index))
        .unwrap_or(false)
}
