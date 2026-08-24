use crate::backend::{Backend, Outcome};
use splr::config::Config;
use splr::solver::{SatSolverIF, SolveIF, Solver};
use splr::types::{CNFDescription, Instantiate};
use splr::Certificate;

/// Splr-backed implementation.
///
/// IPASIR declares variables implicitly and never deletes clauses, so this
/// backend keeps its own copy of the clause database and rebuilds the solver
/// whenever new clauses or variables appeared since the last solve. This
/// works around two splr limitations: late variables are not registered in
/// its internal processor heap, and clauses added after a solve are not
/// handled reliably.
pub struct SplrBackend {
    /// `None` once an inconsistency has been discovered.
    inner: Option<Solver>,
    clauses: Vec<Vec<i32>>,
    declared_vars: usize,
    model: Option<Vec<bool>>,
    trivially_unsat: bool,
    dirty: bool,
}

impl SplrBackend {
    pub fn new() -> Self {
        let mut backend = SplrBackend {
            inner: None,
            clauses: Vec::new(),
            declared_vars: 0,
            model: None,
            trivially_unsat: false,
            dirty: false,
        };
        backend.rebuild();
        backend.dirty = false;
        backend
    }

    fn rebuild(&mut self) {
        if self.trivially_unsat {
            self.inner = None;
            return;
        }
        let mut declared_vars = 0usize;
        for clause in &self.clauses {
            let max_var = clause
                .iter()
                .map(|l| l.unsigned_abs() as usize)
                .max()
                .unwrap_or(0);
            declared_vars = declared_vars.max(max_var);
        }
        self.declared_vars = declared_vars;
        let cnf = CNFDescription {
            num_of_variables: self.declared_vars,
            ..CNFDescription::default()
        };
        let mut solver = <Solver as Instantiate>::instantiate(&Config::default(), &cnf);
        for clause in &self.clauses {
            match solver.add_clause(clause.clone()) {
                Ok(_) => {}
                Err(_) => {
                    // Any error while replaying means the formula is
                    // inconsistent at level 0.
                    self.trivially_unsat = true;
                    self.inner = None;
                    return;
                }
            }
        }
        self.inner = Some(solver);
    }
}

impl Backend for SplrBackend {
    fn name(&self) -> &'static str {
        "splr"
    }

    fn add_clause(&mut self, lits: &[i32]) {
        if self.trivially_unsat {
            return;
        }
        if lits.is_empty() {
            // The empty clause is unsatisfiable by definition.
            self.trivially_unsat = true;
            self.inner = None;
            return;
        }
        self.clauses.push(lits.to_vec());
        self.dirty = true;
    }

    fn solve(&mut self, assumptions: &[i32]) -> Result<Outcome, String> {
        if !assumptions.is_empty() {
            return Err("splr backend does not support assumptions; \
                        use the cadical backend or set ALLOY_SAT_BACKEND=cadical"
                .to_string());
        }
        if self.trivially_unsat {
            self.model = None;
            return Ok(Outcome::Unsat);
        }
        if self.dirty {
            self.rebuild();
            self.dirty = false;
        }
        let Some(solver) = self.inner.as_mut() else {
            self.model = None;
            return Ok(Outcome::Unsat);
        };
        match solver.solve() {
            Ok(Certificate::SAT(model)) => {
                // splr returns signed literals; entry i holds the value of
                // variable i+1.
                self.model = Some(model.iter().map(|&l| l > 0).collect());
                Ok(Outcome::Sat)
            }
            Ok(Certificate::UNSAT) => {
                self.model = None;
                Ok(Outcome::Unsat)
            }
            Err(e) => Err(format!("splr solve failed: {e:?}")),
        }
    }

    fn value(&self, lit: i32) -> Option<bool> {
        let var = lit.unsigned_abs() as usize;
        let v = *self.model.as_ref()?.get(var - 1)?;
        Some(if lit > 0 { v } else { !v })
    }

    fn max_var(&self) -> i32 {
        self.declared_vars as i32
    }

    fn supports_assumptions(&self) -> bool {
        false
    }
}

impl Default for SplrBackend {
    fn default() -> Self {
        Self::new()
    }
}
