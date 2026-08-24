pub trait SatSolver {
    fn add_variables(&mut self, n: usize);
    fn num_variables(&self) -> usize;
    fn add_clause(&mut self, lits: &[i64]) -> bool;
    fn solve(&mut self) -> bool;
    fn value_of(&self, var: i64) -> bool;
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
}

impl RecordingSolver {
    pub fn new() -> RecordingSolver {
        RecordingSolver::default()
    }

    fn brute_force(&self) -> Option<Vec<bool>> {
        if self.vars > BRUTE_FORCE_MAX_VARS {
            return None;
        }
        for mask in 0u128..(1u128 << self.vars) {
            let model: Vec<bool> = (0..self.vars).map(|i| (mask >> i) & 1 == 1).collect();
            let ok = self.clauses.iter().all(|c| {
                c.iter()
                    .any(|&l| l > 0 && model[l as usize - 1] || l < 0 && !model[(-l) as usize - 1])
            });
            if ok {
                return Some(model);
            }
        }
        None
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

    fn solve(&mut self) -> bool {
        match self.brute_force() {
            Some(model) => {
                self.model = model;
                self.sat = true;
                true
            }
            None => {
                self.sat = false;
                false
            }
        }
    }

    fn value_of(&self, var: i64) -> bool {
        self.model[(var.abs() - 1) as usize] ^ (var < 0)
    }
}
