//! Pardinus decomposition (Iter 8) — serial subset.
//!
//! * [`PardinusBounds`] — immutable decoration of [`Bounds`] with stage-1
//!   (*partial*) relation marks, targets, weights and symbolic
//!   (expression-valued) bounds resolved against an [`Instance`].
//! * [`slice_formula`] — port of `DecompFormulaSlicer`: partitions top-level
//!   conjuncts into (partial-only, remainder).
//! * [`solve_dynamic`] — two-stage serial executor: stage 1 solves the
//!   partial slice; stage 2 fixes the partial relations to that model and
//!   solves the full formula.
//! * [`solve_static_components`] — groups top-level conjuncts into connected
//!   components over shared relations, solves each independently and merges
//!   the instances.
//!
//! Deviations from Java Pardinus (documented): no PARALLEL mode, simplified
//! amalgamated/integrated handling (explicit partial marks instead of the
//! synchronized state machine), and single-shot stage 1 (no multi-model
//! exploration/backtracking).

use std::collections::{BTreeSet, HashMap};

use crate::ast::{AstArena, ExprId, FormulaBinOp, FormulaId, IntId};
use crate::bounds::Bounds;
use crate::eval::Evaluator;
use crate::instance::Instance;
use crate::relation::RelationId;
use crate::tupleset::TupleSet;

#[derive(Debug, thiserror::Error)]
pub enum PardinusError {
    #[error("ast error: {0}")]
    Ast(#[from] crate::ast::AstError),
    #[error("relation {0} is not present in the base bounds")]
    UnboundRelation(u32),
    #[error("symbolic bound evaluation failed: {0}")]
    Eval(String),
    #[error("bounds error: {0}")]
    Bounds(#[from] crate::bounds::BoundsError),
    #[error("tuple set error: {0}")]
    Capacity(#[from] crate::tupleset::CapacityError),
    #[error("instance error: {0}")]
    Instance(#[from] crate::instance::InstanceError),
}

/// Immutable decoration of [`Bounds`] with Pardinus-specific information.
#[derive(Clone, Debug)]
pub struct PardinusBounds {
    base: Bounds,
    /// relations selected for the stage-1 (partial) problem
    partials: BTreeSet<RelationId>,
    /// preferred values for variable relations (hints for stage 2)
    targets: HashMap<RelationId, TupleSet>,
    /// optimization weights (recorded; unused by the SAT layer)
    weights: HashMap<RelationId, i64>,
    /// symbolic bounds: relation -> bounding expression
    symb_lower: HashMap<RelationId, ExprId>,
    symb_upper: HashMap<RelationId, ExprId>,
}

impl PardinusBounds {
    pub fn new(base: Bounds) -> PardinusBounds {
        PardinusBounds {
            base,
            partials: BTreeSet::new(),
            targets: HashMap::new(),
            weights: HashMap::new(),
            symb_lower: HashMap::new(),
            symb_upper: HashMap::new(),
        }
    }

    pub fn base(&self) -> &Bounds {
        &self.base
    }

    pub fn partials(&self) -> &BTreeSet<RelationId> {
        &self.partials
    }

    pub fn targets(&self) -> &HashMap<RelationId, TupleSet> {
        &self.targets
    }

    pub fn weights(&self) -> &HashMap<RelationId, i64> {
        &self.weights
    }

    /// Marks a VARIABLE relation as belonging to the stage-1 problem.
    pub fn with_partial(mut self, r: RelationId) -> Self {
        self.partials.insert(r);
        self
    }

    pub fn with_target(mut self, r: RelationId, ts: TupleSet) -> Self {
        self.targets.insert(r, ts);
        self
    }

    pub fn with_weight(mut self, r: RelationId, weight: i64) -> Self {
        self.weights.insert(r, weight);
        self
    }

    /// Attaches a symbolic upper bound expression for `r`.
    pub fn with_symb_upper(mut self, r: RelationId, expr: ExprId) -> Self {
        self.symb_upper.insert(r, expr);
        self
    }

    /// Attaches a symbolic lower bound expression for `r`.
    pub fn with_symb_lower(mut self, r: RelationId, expr: ExprId) -> Self {
        self.symb_lower.insert(r, expr);
        self
    }

    /// Evaluates every symbolic bound against `env` and returns concrete
    /// bounds where those entries replace the base ones.
    ///
    /// Expressions may reference any relation present in `env`; this is how
    /// stage 2 consumes stage-1 results (dynamic decomposition).
    pub fn resolve_symbolic(
        &self,
        arena: &AstArena,
        env: &Instance,
    ) -> Result<Bounds, PardinusError> {
        let mut out = self.base.clone();
        let ev = Evaluator::new(env);
        for (&r, &expr) in &self.symb_upper {
            let ts = ev
                .expr_set(arena, expr, &Vec::new())
                .map_err(|e| PardinusError::Eval(e.to_string()))?;
            out.bound_upper(r, &ts)?;
        }
        for (&r, &expr) in &self.symb_lower {
            let lower = ev
                .expr_set(arena, expr, &Vec::new())
                .map_err(|e| PardinusError::Eval(e.to_string()))?;
            let upper = out
                .upper_bound(r)
                .cloned()
                .ok_or(PardinusError::UnboundRelation(r.0))?;
            out.bound(r, &lower, &upper)?;
        }
        Ok(out)
    }
}

// ---------------------------------------------------------------------------
// relation collection + top-level conjunct slicing (DecompFormulaSlicer)
// ---------------------------------------------------------------------------

fn collect_expr_relations(arena: &AstArena, e: ExprId, out: &mut BTreeSet<RelationId>) {
    match arena.expr(e).clone() {
        crate::ast::ExprNode::Relation(r) => {
            out.insert(r);
        }
        crate::ast::ExprNode::Variable(_)
        | crate::ast::ExprNode::Constant(_)
        | crate::ast::ExprNode::FromInt(_) => {}
        crate::ast::ExprNode::Unary { child, .. }
        | crate::ast::ExprNode::Temporal { child, .. } => {
            collect_expr_relations(arena, child, out);
        }
        crate::ast::ExprNode::Binary { left, right, .. } => {
            collect_expr_relations(arena, left, out);
            collect_expr_relations(arena, right, out);
        }
        crate::ast::ExprNode::Nary { children, .. } => {
            for c in children {
                collect_expr_relations(arena, c, out);
            }
        }
        crate::ast::ExprNode::If { cond, then, els } => {
            collect_formula_relations(arena, cond, out);
            collect_expr_relations(arena, then, out);
            collect_expr_relations(arena, els, out);
        }
        crate::ast::ExprNode::Project { expr, .. } => {
            collect_expr_relations(arena, expr, out);
        }
        crate::ast::ExprNode::Comprehension { decls, body } => {
            for d in arena.decls(decls) {
                collect_expr_relations(arena, d.expr, out);
            }
            collect_formula_relations(arena, body, out);
        }
    }
}

fn collect_int_relations(arena: &AstArena, i: IntId, out: &mut BTreeSet<RelationId>) {
    match arena.int(i).clone() {
        crate::ast::IntNode::Constant(_) => {}
        crate::ast::IntNode::OfExpr { expr, .. } => collect_expr_relations(arena, expr, out),
        crate::ast::IntNode::Binary { left, right, .. } => {
            collect_int_relations(arena, left, out);
            collect_int_relations(arena, right, out);
        }
        crate::ast::IntNode::If { cond, then, els } => {
            collect_formula_relations(arena, cond, out);
            collect_int_relations(arena, then, out);
            collect_int_relations(arena, els, out);
        }
        crate::ast::IntNode::Sum { decls, body } => {
            for d in arena.decls(decls) {
                collect_expr_relations(arena, d.expr, out);
            }
            collect_int_relations(arena, body, out);
        }
    }
}

/// Collects every relation referenced anywhere inside `f`.
pub fn collect_formula_relations(arena: &AstArena, f: FormulaId, out: &mut BTreeSet<RelationId>) {
    match arena.formula(f).clone() {
        crate::ast::FormulaNode::Constant(_) => {}
        crate::ast::FormulaNode::Not(child) => collect_formula_relations(arena, child, out),
        crate::ast::FormulaNode::Nary { children, .. } => {
            for c in children {
                collect_formula_relations(arena, c, out);
            }
        }
        crate::ast::FormulaNode::Comparison { left, right, .. } => {
            collect_expr_relations(arena, left, out);
            collect_expr_relations(arena, right, out);
        }
        crate::ast::FormulaNode::IntComparison { left, right, .. } => {
            collect_int_relations(arena, left, out);
            collect_int_relations(arena, right, out);
        }
        crate::ast::FormulaNode::Multiplicity { expr, .. } => {
            collect_expr_relations(arena, expr, out);
        }
        crate::ast::FormulaNode::Quantified { decls, body, .. } => {
            for d in arena.decls(decls) {
                collect_expr_relations(arena, d.expr, out);
            }
            collect_formula_relations(arena, body, out);
        }
        crate::ast::FormulaNode::TemporalUnary { child, .. } => {
            collect_formula_relations(arena, child, out);
        }
        crate::ast::FormulaNode::TemporalBinary { left, right, .. } => {
            collect_formula_relations(arena, left, out);
            collect_formula_relations(arena, right, out);
        }
    }
}

fn flatten_ands(arena: &AstArena, f: FormulaId, out: &mut Vec<FormulaId>) {
    if let crate::ast::FormulaNode::Nary {
        op: FormulaBinOp::And,
        children,
    } = arena.formula(f).clone()
    {
        for c in children {
            flatten_ands(arena, c, out);
        }
    } else if let crate::ast::FormulaNode::Nary { .. } = arena.formula(f).clone() {
        unreachable!()
    } else {
        out.push(f);
    }
}

/// Partitions the TOP-LEVEL conjunctions of `f` into conjuncts whose
/// relations are all within `partials` (first element) and the rest.
pub fn slice_formula(
    arena: &mut AstArena,
    f: FormulaId,
    partials: &BTreeSet<RelationId>,
) -> Result<(FormulaId, FormulaId), crate::ast::AstError> {
    let mut conjuncts = Vec::new();
    flatten_ands(arena, f, &mut conjuncts);
    let mut f1 = Vec::new();
    let mut f2 = Vec::new();
    for c in conjuncts {
        let mut rels = BTreeSet::new();
        collect_formula_relations(arena, c, &mut rels);
        if rels.iter().all(|r| partials.contains(r)) {
            f1.push(c);
        } else {
            f2.push(c);
        }
    }
    // dedup identical ids (and re-conjunction of the same node twice)
    let lhs = if f1.is_empty() {
        arena.true_formula()
    } else {
        arena.and(&f1)
    };
    let rhs = if f2.is_empty() {
        arena.true_formula()
    } else {
        arena.and(&f2)
    };
    Ok((lhs, rhs))
}

// ---------------------------------------------------------------------------
// dynamic (two-stage) decomposed solving
// ---------------------------------------------------------------------------

fn restrict_to_partials(base: &Bounds, partials: &BTreeSet<RelationId>) -> Bounds {
    let mut out = base.clone();
    for r in base.relations().collect::<Vec<_>>() {
        if base.pool().is_variable(r) && !partials.contains(&r) {
            out.unbind(r);
        }
    }
    out
}

/// Two-stage dynamic decomposition:
///
/// 1. slice the formula into (partial-only, rest);
/// 2. solve the partial slice over bounds restricted to the partial
///    variables;
/// 3. fix the partial relations to that model and solve the full formula.
///
/// If the first stage fails, the whole problem is reported UNSAT (the full
/// formula contains the partial slice as a conjunct). Note that, like
/// Pardinus itself without exploration, a single unlucky stage-1 model can
/// make stage 2 fail even though other stage-1 models would succeed.
#[cfg(feature = "ipasir")]
pub fn solve_dynamic(
    solver: &crate::Solver,
    arena: &mut AstArena,
    formula: FormulaId,
    pb: &PardinusBounds,
    steps: usize,
) -> Result<crate::solver::Solution, crate::fol::TranslateError> {
    use crate::solver::Solution;

    let partials = pb.partials().clone();
    let (f1, _f2) = slice_formula(arena, formula, &partials)?;

    // ---- stage 1 with bounded exploration of distinct partial models ----
    let stage1_bounds = restrict_to_partials(pb.base(), &partials);
    let skolemize = solver.options().skolemize;
    const MAX_ATTEMPTS: usize = 64;

    // probe mapping (deterministic ids) to translate origin relations
    let probe = crate::temporal::expand_bounds(arena, pb.base(), steps, 1)?;
    let partial_expanded: HashMap<RelationId, RelationId> = partials
        .iter()
        .filter_map(|&r| probe.mapping.get(&r).map(|&e| (r, e)))
        .collect();

    let mut blocked: Vec<Vec<i64>> = Vec::new();
    let mut last: Option<Solution> = None;

    for _attempt in 0..MAX_ATTEMPTS {
        let sol1 = solver.solve_temporal_with(
            arena,
            f1,
            &stage1_bounds,
            steps,
            skolemize,
            &[],
            &blocked,
        )?;
        if !sol1.satisfiable || sol1.instance.is_none() {
            // no (more) stage-1 models: whole problem UNSAT if none worked
            return Ok(last.unwrap_or(Solution {
                satisfiable: false,
                instance: None,
                temporal: None,
                witness_slots: Vec::new(),
                num_primary_variables: sol1.num_primary_variables,
                backend: sol1.backend,
            }));
        }
        let inst1 = sol1.instance.expect("SAT implies instance");

        // anchors + blocking clause over the partial cells of this model
        let mut anchors: Vec<(RelationId, TupleSet)> = Vec::new();
        let mut block: Vec<i64> = Vec::new();
        for (&orig_rel, &ere) in &partial_expanded {
            if let Some(ts) = inst1.tuples(ere) {
                anchors.push((orig_rel, ts.clone()));
                for idx in ts.index_view().iter() {
                    let slot = sol1
                        .witness_slots
                        .iter()
                        .find(|(_, r, t)| *r == ere && *t == idx)
                        .map(|(s, _, _)| *s);
                    if let Some(s) = slot {
                        // forbid this exact truth value next attempt
                        block.push(-(s as i64)); // slots were TRUE here
                    }
                }
            }
        }
        if !block.is_empty() {
            blocked.push(block);
        }

        // ---- stage 2: full formula anchored to this stage-1 model ----
        let final_sol = solver.solve_temporal_with(
            arena,
            formula,
            pb.base(),
            steps,
            skolemize,
            &anchors,
            &[],
        )?;
        if final_sol.satisfiable {
            return Ok(final_sol);
        }
        last = Some(final_sol);
    }

    Ok(Solution {
        satisfiable: false,
        instance: None,
        temporal: None,
        witness_slots: Vec::new(),
        num_primary_variables: 0,
        backend: "decomposed-exhausted",
    })
}

// ---------------------------------------------------------------------------
// static connected-component decomposition
// ---------------------------------------------------------------------------

/// Splits top-level conjuncts into connected components over shared
/// relations and solves each independently. Any UNSAT component makes the
/// whole UNSAT; otherwise the component instances are merged (relations are
/// disjoint across components by construction).
#[cfg(feature = "ipasir")]
pub fn solve_static_components(
    solver: &crate::Solver,
    arena: &mut AstArena,
    formula: FormulaId,
    bounds: &Bounds,
) -> Result<crate::solver::Solution, crate::fol::TranslateError> {
    use crate::solver::Solution;

    let groups = component_groups(arena, formula);

    if groups.len() <= 1 {
        // nothing to decompose
        let mut si = crate::ipasir_bridge::IpasirSolver::new()
            .map_err(crate::fol::TranslateError::Solver)?;
        return solver.solve_with(&mut si, arena, formula, bounds);
    }

    let mut merged = Instance::new(bounds.universe(), bounds.pool());
    for group in &groups {
        let gformula = arena.and(&group.formulas);
        let mut si = crate::ipasir_bridge::IpasirSolver::new()
            .map_err(crate::fol::TranslateError::Solver)?;
        let sol = solver.solve_with(&mut si, arena, gformula, bounds)?;
        if !sol.satisfiable {
            return Ok(Solution {
                satisfiable: false,
                instance: None,
                temporal: None,
                witness_slots: Vec::new(),
                num_primary_variables: sol.num_primary_variables,
                backend: sol.backend,
            });
        }
        let inst = sol.instance.expect("SAT implies instance");
        for r in inst.relations().collect::<Vec<_>>() {
            if !group.relations.contains(&r) {
                continue; // unrelated filler from shared base bounds
            }
            let ts = inst.tuples(r).expect("relation present");
            merged
                .add(r, ts)
                .map_err(|e| crate::fol::TranslateError::Pardinus(PardinusError::Instance(e)))?;
        }
    }

    Ok(Solution {
        satisfiable: true,
        instance: Some(merged),
        temporal: None,
        witness_slots: Vec::new(),
        num_primary_variables: 0,
        backend: "decomposed",
    })
}

/// Parallel variant of [`solve_static_components`] (backlog 3): component
/// groups are solved on a bounded worker pool (work-pulling over an atomic
/// counter; no external scheduler dependency). Each worker gets its own
/// clone of the arena — relation interning stays consistent because the
/// pool is shared through `Arc`. Any UNSAT component makes the whole
/// problem UNSAT.
///
/// `max_threads` caps the worker count (`0` = one worker per group).
#[cfg(feature = "ipasir")]
pub fn solve_static_components_parallel(
    solver: &crate::Solver,
    arena: &mut AstArena,
    formula: FormulaId,
    bounds: &Bounds,
    max_threads: usize,
) -> Result<crate::solver::Solution, crate::fol::TranslateError> {
    use crate::solver::Solution;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Mutex;

    let groups = component_groups(arena, formula);
    if groups.len() <= 1 {
        let mut si = crate::ipasir_bridge::IpasirSolver::new()
            .map_err(crate::fol::TranslateError::Solver)?;
        return solver.solve_with(&mut si, arena, formula, bounds);
    }

    let nworkers = if max_threads == 0 {
        groups.len()
    } else {
        max_threads.min(groups.len())
    };
    let next = AtomicUsize::new(0);
    let results: Vec<Mutex<Option<Result<Solution, String>>>> =
        (0..groups.len()).map(|_| Mutex::new(None)).collect();

    std::thread::scope(|scope| {
        for _w in 0..nworkers {
            scope.spawn(|| loop {
                let i = next.fetch_add(1, Ordering::SeqCst);
                if i >= groups.len() {
                    break;
                }
                // own arena clone per task: translation is thread-local
                let mut a2 = arena.clone();
                let gformula = a2.and(&groups[i].formulas);
                let out = (|| -> Result<Solution, crate::fol::TranslateError> {
                    let mut si = crate::ipasir_bridge::IpasirSolver::new()
                        .map_err(crate::fol::TranslateError::Solver)?;
                    let r = solver.solve_with(&mut si, &a2, gformula, bounds);
                    if std::env::var_os("DBG_PAR").is_some() {
                        if let Ok(sol) = &r {
                            if let Some(inst) = &sol.instance {
                                let names: Vec<String> = inst
                                    .relations()
                                    .map(|rr| {
                                        format!(
                                            "{}:{}",
                                            bounds.pool().name(rr),
                                            inst.tuples(rr).map(|t| t.len()).unwrap_or(0)
                                        )
                                    })
                                    .collect();
                                eprintln!(
                                    "[par] group{i} sat={} rels={:?}",
                                    sol.satisfiable, names
                                );
                            }
                        }
                    }
                    r
                })();
                let mut slot = results[i].lock().unwrap();
                *slot = Some(out.map_err(|e| e.to_string()));
            });
        }
    });

    let mut merged = Instance::new(bounds.universe(), bounds.pool());
    let mut num_primary = 0usize;
    for (idx_out, r) in results.into_iter().enumerate() {
        let sol = r
            .into_inner()
            .unwrap()
            .expect("worker panicked")
            .map_err(|e| crate::fol::TranslateError::Pardinus(PardinusError::Eval(e)))?;
        num_primary += sol.num_primary_variables;
        if !sol.satisfiable {
            return Ok(Solution {
                satisfiable: false,
                instance: None,
                temporal: None,
                witness_slots: Vec::new(),
                num_primary_variables: sol.num_primary_variables,
                backend: "decomposed-parallel",
            });
        }
        let owned = &groups[idx_out].relations;
        let inst = sol.instance.expect("SAT implies instance");
        for rel in inst.relations().collect::<Vec<_>>() {
            if !owned.contains(&rel) {
                continue; // unrelated filler from shared base bounds
            }
            let ts = inst.tuples(rel).expect("relation present");
            merged
                .add(rel, ts)
                .map_err(|e| crate::fol::TranslateError::Pardinus(PardinusError::Instance(e)))?;
        }
    }

    Ok(Solution {
        satisfiable: true,
        instance: Some(merged),
        temporal: None,
        witness_slots: Vec::new(),
        num_primary_variables: num_primary,
        backend: "decomposed-parallel",
    })
}

/// One decomposition component: its formulas plus every relation the
/// component owns (used to merge instances unambiguously).
#[derive(Debug, Clone)]
pub struct ComponentGroup {
    pub formulas: Vec<FormulaId>,
    pub relations: BTreeSet<RelationId>,
}

/// Splits top-level conjuncts into connected components over shared
/// relations. Returns the groups (order-stable by first appearance).
pub fn component_groups(arena: &AstArena, formula: FormulaId) -> Vec<ComponentGroup> {
    let mut conjuncts = Vec::new();
    flatten_ands(arena, formula, &mut conjuncts);

    let rels_per: Vec<BTreeSet<RelationId>> = conjuncts
        .iter()
        .map(|&c| {
            let mut s = BTreeSet::new();
            collect_formula_relations(arena, c, &mut s);
            s
        })
        .collect();

    let mut parent: Vec<usize> = (0..conjuncts.len()).collect();
    fn find(p: &mut [usize], x: usize) -> usize {
        if p[x] != x {
            p[x] = find(p, p[x]);
        }
        p[x]
    }
    let mut owner: HashMap<RelationId, usize> = HashMap::new();
    for (i, rels) in rels_per.iter().enumerate() {
        for &r in rels {
            match owner.get(&r) {
                Some(&j) => {
                    let (a, b) = (find(&mut parent, i), find(&mut parent, j));
                    parent[a] = b;
                }
                None => {
                    owner.insert(r, i);
                }
            }
        }
    }
    let mut order: Vec<usize> = Vec::new();
    let mut groups_formulas: HashMap<usize, Vec<FormulaId>> = HashMap::new();
    let mut groups_rels: HashMap<usize, BTreeSet<RelationId>> = HashMap::new();
    for (i, c) in conjuncts.iter().enumerate() {
        let root = find(&mut parent, i);
        if !groups_formulas.contains_key(&root) {
            order.push(root);
        }
        groups_formulas.entry(root).or_default().push(*c);
        groups_rels
            .entry(root)
            .or_default()
            .extend(rels_per[i].iter().copied());
    }
    order
        .into_iter()
        .map(|root| ComponentGroup {
            formulas: groups_formulas.remove(&root).unwrap_or_default(),
            relations: groups_rels.remove(&root).unwrap_or_default(),
        })
        .collect()
}
