//! UNSAT core extraction (Iter 9): the Rust analogue of kodkod's
//! `-core=rce` machinery.
//!
//! Java kodkod bakes a *selector axiom* (unit clause) per top-level
//! conjunct into the CNF, minimizes the resolution proof with RCEStrategy,
//! and maps surviving selector units back to culprit constraints. Here we
//! take the assumption route instead: every top-level conjunct is
//! translated into definitions whose root literal is passed as a SAT
//! *assumption*; after an UNSAT solve the backend's failed assumptions
//! (`ipasir_failed` / CaDiCaL `failed()`) directly name the conjuncts that
//! participate in the conflict. The initial core is then shrunk by an
//! RCEStrategy-equivalent pass giving each member exactly one elimination
//! attempt (deletion filtering), so no remaining member can be dropped
//! while staying UNSAT.
//!
//! A resolution-proof based design (Proof/ResolutionTrace) is documented in
//! `docs/pardinus-core-survey.md`; it is not required for assumption-based
//! cores and remains future work.

use std::collections::HashSet;

use crate::ast::{AstArena, FormulaBinOp, FormulaId, FormulaNode};
use crate::bounds::Bounds;
use crate::cnf::translate_conjunct_def;
use crate::fol::{FolTranslator, TranslateError};
use crate::instance::Instance;
use crate::sat::SatSolver;

/// Flattens `f` into its top-level conjuncts (kodkod `Nodes.conjuncts`):
/// nested N-ary ANDs are expanded, everything else is atomic.
pub fn conjuncts_of(arena: &AstArena, f: FormulaId) -> Vec<FormulaId> {
    let mut out = Vec::new();
    collect(arena, f, &mut out);
    fn collect(arena: &AstArena, f: FormulaId, out: &mut Vec<FormulaId>) {
        if let FormulaNode::Nary {
            op: FormulaBinOp::And,
            children,
        } = arena.formula(f)
        {
            let children = children.clone();
            for &c in &children {
                collect(arena, c, out);
            }
        } else {
            out.push(f);
        }
    }
    out
}

/// Result of [`solve_core_with`] / [`Solver::solve_core`](crate::Solver).
#[derive(Debug)]
pub struct CoreSolution {
    pub satisfiable: bool,
    pub instance: Option<Instance>,
    /// Top-level conjuncts of the input formula, flattened.
    pub conjuncts: Vec<FormulaId>,
    /// On UNSAT: ascending indices into `conjuncts` forming the minimized
    /// core. Empty on SAT. Every member is individually necessary: dropping
    /// it makes the remainder satisfiable.
    pub core: Vec<usize>,
}

/// Core-extraction solve generic over any assumption-capable
/// [`SatSolver`]. See the [module docs](self) for the mechanism.
pub fn solve_core_with<S: SatSolver>(
    solver: &mut S,
    bitwidth: u32,
    arena: &AstArena,
    formula: FormulaId,
    bounds: &Bounds,
) -> Result<CoreSolution, TranslateError> {
    if !solver.supports_assumptions() {
        return Err(TranslateError::Solver(
            "core extraction requires a SAT solver with assumption support \
             (e.g. IpasirSolver/CaDiCaL)"
                .into(),
        ));
    }
    let conjuncts = conjuncts_of(arena, formula);
    let mut translator = FolTranslator::new(crate::BoolCtx::new(), bounds);
    translator.set_bitwidth(bitwidth);

    // Translate every conjunct into definitions; non-trivial roots become
    // selectors assumed during the solve. Selectors are *signed* literals
    // (`not(f)` shares its inner gate, so the sign matters). Identical
    // literals from duplicate conjuncts are deduplicated: kodkod does the
    // same when mapping cores back to identical roots.
    let mut selectors: Vec<(usize, i64)> = Vec::new();
    for (i, &c) in conjuncts.iter().enumerate() {
        let root = translator.formula_ref(arena, c, &[])?;
        if !root.is_const() {
            let ctx = translator.ctx.clone();
            let max_primary = ctx.num_slots();
            let lit = ctx.with_factory(|factory| {
                translate_conjunct_def(solver, factory, root, max_primary)
            })?;
            match lit {
                crate::cnf::RootCnf::Lit(l) => {
                    if !selectors.iter().any(|&(_, v)| v == l) {
                        selectors.push((i, l));
                    }
                }
                // Handled below via the const checks above; unreachable here.
                _ => unreachable!("constant root handled by is_const branch"),
            }
        } else if !root.const_value() {
            // Constant false: unconditionally UNSAT; this conjunct alone is
            // a trivially minimal core.
            return Ok(CoreSolution {
                satisfiable: false,
                instance: None,
                conjuncts,
                core: vec![i],
            });
        }
    }

    // Solve under all selector assumptions at once.
    for &(_, var) in &selectors {
        SatSolver::assume(solver, var);
    }
    let satisfiable = solver.solve();

    if satisfiable {
        let instance =
            Some(translator.materialize(|slot| SatSolver::value_of(solver, slot as i64)));
        return Ok(CoreSolution {
            satisfiable: true,
            instance,
            conjuncts,
            core: Vec::new(),
        });
    }

    // Initial core from the backend's failed assumptions; fall back to all
    // selectors when the backend reports nothing useful.
    let failed: HashSet<i64> = solver.failed_core().into_iter().collect();
    let mut candidates: Vec<usize> = (0..selectors.len())
        .filter(|&k| failed.contains(&selectors[k].1))
        .collect();
    if candidates.is_empty() {
        candidates = (0..selectors.len()).collect();
    }

    let sel_vars: Vec<i64> = selectors.iter().map(|&(_, v)| v).collect();
    let kept = deletion_filter(solver, &sel_vars, &candidates);
    let mut core: Vec<usize> = kept.iter().map(|&k| selectors[k].0).collect();
    core.sort_unstable();
    Ok(CoreSolution {
        satisfiable: false,
        instance: None,
        conjuncts,
        core,
    })
}

/// RCEStrategy-equivalent minimization: every candidate gets exactly one
/// elimination attempt — drop it permanently when the rest is still UNSAT,
/// keep it otherwise. The result is minimal w.r.t. single removals among
/// the attempted orders.
fn deletion_filter<S: SatSolver>(
    solver: &mut S,
    sel_vars: &[i64],
    candidates: &[usize],
) -> Vec<usize> {
    let mut core: Vec<usize> = candidates.to_vec();
    let mut i = 0;
    while i < core.len() {
        let trial: Vec<i64> = core
            .iter()
            .filter(|&&j| j != core[i])
            .map(|&j| sel_vars[j])
            .collect();
        for &lit in &trial {
            SatSolver::assume(solver, lit);
        }
        if !solver.solve() {
            core.remove(i);
        } else {
            i += 1;
        }
    }
    core
}

// ---------------------------------------------------------------------------
// CNF-level soft-constraint groups (used directly by e.g. Sudoku demos)
// ---------------------------------------------------------------------------

/// A group of clauses treated as one removable constraint with selector
/// semantics: the group holds iff its selector literal is true.
#[derive(Clone, Debug)]
pub struct SoftGroup {
    /// Human-readable label (e.g. "clue r0c0=1").
    pub name: String,
    pub clauses: Vec<Vec<i64>>,
}

impl SoftGroup {
    pub fn new(name: impl Into<String>, clauses: Vec<Vec<i64>>) -> SoftGroup {
        SoftGroup {
            name: name.into(),
            clauses,
        }
    }
}

/// Result of [`extract_cnf_core`].
#[derive(Debug)]
pub struct CnfCore {
    /// Initial failed set reported by the backend (group indices).
    pub initial: Vec<usize>,
    /// Minimized core after deletion filtering (group indices).
    pub groups: Vec<usize>,
    /// Number of solve calls spent (initial + one per elimination attempt).
    pub solves: usize,
}

/// Extracts a minimized UNSAT core over `soft` groups under the hard
/// clauses `hard`, using fresh selector variables and assumptions.
///
/// Returns `Ok(None)` when the problem is satisfiable.
pub fn extract_cnf_core<S: SatSolver>(
    solver: &mut S,
    hard: &[Vec<i64>],
    soft: &[SoftGroup],
) -> Result<Option<CnfCore>, String> {
    if !solver.supports_assumptions() {
        return Err("core extraction requires a SAT solver with assumption support".into());
    }
    let max_lit = hard
        .iter()
        .chain(soft.iter().flat_map(|g| g.clauses.iter()))
        .flatten()
        .map(|&l| l.unsigned_abs() as usize)
        .max()
        .unwrap_or(0);
    let selector = |i: usize| (max_lit + 1 + i) as i64;
    let needed = max_lit + soft.len();
    if needed > solver.num_variables() {
        solver.add_variables(needed - solver.num_variables());
    }
    for c in hard {
        if !solver.add_clause(c) {
            return Err("hard clause references undefined variable".into());
        }
    }
    for (i, group) in soft.iter().enumerate() {
        for c in &group.clauses {
            let mut guarded = vec![-selector(i)];
            guarded.extend_from_slice(c);
            if !solver.add_clause(&guarded) {
                return Err("soft clause references undefined variable".into());
            }
        }
    }

    for i in 0..soft.len() {
        SatSolver::assume(solver, selector(i));
    }
    let mut solves = 1;
    if solver.solve() {
        return Ok(None);
    }

    let failed: HashSet<i64> = solver.failed_core().into_iter().collect();
    let mut candidates: Vec<usize> = (0..soft.len())
        .filter(|&i| failed.contains(&selector(i)))
        .collect();
    if candidates.is_empty() {
        candidates = (0..soft.len()).collect();
    }

    // Deletion filter (one attempt per member), reusing guarded clauses.
    let mut core = candidates.clone();
    let mut i = 0;
    while i < core.len() {
        let trial: Vec<usize> = core.iter().copied().filter(|&j| j != core[i]).collect();
        for &j in &trial {
            SatSolver::assume(solver, selector(j));
        }
        solves += 1;
        if !solver.solve() {
            core.remove(i);
        } else {
            i += 1;
        }
    }
    core.sort_unstable();
    let mut initial = candidates;
    initial.sort_unstable();
    Ok(Some(CnfCore {
        initial,
        groups: core,
        solves,
    }))
}
