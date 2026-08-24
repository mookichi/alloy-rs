pub trait SatSolver {
    fn add_variables(&mut self, n: usize);
    fn num_variables(&self) -> usize;
    fn add_clause(&mut self, lits: &[i64]) -> bool;
    fn solve(&mut self) -> bool;
    fn value_of(&self, var: i64) -> bool;

    /// Accumulate an assumption for the next [`SatSolver::solve`].
    /// The list is consumed (reset) by each solve.
    fn assume(&mut self, _lit: i64) {}

    /// Whether `lit` was a *failed* assumption in the last UNSAT solve, i.e.
    /// whether it belongs to the unsatisfiable core reported by the backend.
    /// Always `false` unless the last result was UNSAT under assumptions.
    fn failed(&self, _lit: i64) -> bool {
        false
    }

    /// The failed assumptions of the last UNSAT solve.
    fn failed_core(&self) -> Vec<i64> {
        Vec::new()
    }

    /// Whether this solver supports assumptions at all.
    fn supports_assumptions(&self) -> bool {
        false
    }
}

pub const BRUTE_FORCE_MAX_VARS: usize = 22;

#[derive(Debug)]
pub enum RecordingError {
    TooManyVariables,
}

#[derive(Default)]
pub struct RecordingSolver {
    vars: usize,
    pub clauses: Vec<Vec<i64>>,
    model: Vec<bool>,
    sat: bool,
    /// Assumptions accumulated for the next solve.
    pending: Vec<i64>,
    /// Failed assumptions of the last UNSAT solve (exact minimal core).
    last_failed: Vec<i64>,
}

impl RecordingSolver {
    pub fn new() -> RecordingSolver {
        RecordingSolver::default()
    }

    fn brute_force_under(&self, assumptions: &[i64]) -> Option<Vec<bool>> {
        if self.vars > BRUTE_FORCE_MAX_VARS {
            return None;
        }
        // Assumption literals refer to real formula variables.
        for mask in 0u128..(1u128 << self.vars) {
            let bit = |i: usize| (mask >> i) & 1 == 1;
            let holds = |l: i64| l > 0 && bit(l as usize - 1) || l < 0 && !bit((-l) as usize - 1);
            let ok_clauses = self.clauses.iter().all(|c| c.iter().any(|&l| holds(l)));
            let ok_assumptions = assumptions.iter().all(|&a| holds(a));
            if ok_clauses && ok_assumptions {
                return Some((0..self.vars).map(bit).collect());
            }
        }
        None
    }

    /// Exact minimal unsatisfiable subset of `assumptions` via deletion
    /// filtering (one removal attempt per member). Returns the surviving
    /// members; empty means the formula plus no assumptions is already UNSAT.
    fn minimal_failed_core(&self, assumptions: &[i64]) -> Vec<i64> {
        let mut core: Vec<i64> = assumptions.to_vec();
        let mut i = 0;
        while i < core.len() {
            let trial: Vec<i64> = core
                .iter()
                .enumerate()
                .filter(|&(j, _)| j != i)
                .map(|(_, &l)| l)
                .collect();
            if self.brute_force_under(&trial).is_none() {
                core.remove(i);
            } else {
                i += 1;
            }
        }
        core
    }
}

impl SatSolver for RecordingSolver {
    fn add_variables(&mut self, n: usize) {
        self.vars += n;
    }

    fn num_variables(&self) -> usize {
        self.vars
    }

    fn add_clause(&mut self, lits: &[i64]) -> bool {
        for &l in lits {
            if l == 0 || l.unsigned_abs() as usize > self.vars {
                return false;
            }
        }
        self.clauses.push(lits.to_vec());
        true
    }

    fn assume(&mut self, lit: i64) {
        if lit != 0 {
            self.pending.push(lit);
        }
    }

    fn solve(&mut self) -> bool {
        match self.brute_force_under(&self.pending) {
            Some(model) => {
                self.model = model;
                self.sat = true;
                self.last_failed.clear();
                self.pending.clear();
                true
            }
            None => {
                self.sat = false;
                self.last_failed = self.minimal_failed_core(&self.pending);
                self.pending.clear();
                false
            }
        }
    }

    fn failed(&self, lit: i64) -> bool {
        !self.sat && self.last_failed.contains(&lit)
    }

    fn failed_core(&self) -> Vec<i64> {
        if self.sat {
            Vec::new()
        } else {
            self.last_failed.clone()
        }
    }

    fn supports_assumptions(&self) -> bool {
        true
    }

    fn value_of(&self, var: i64) -> bool {
        self.model[(var.abs() - 1) as usize] ^ (var < 0)
    }
}
