use crate::sat::SatSolver;
use alloy_ipasir::{Session, IPASIR_SAT};

pub struct IpasirSolver {
    session: Session,
    vars: usize,
}

impl IpasirSolver {
    pub fn new() -> Result<IpasirSolver, String> {
        Ok(IpasirSolver {
            session: Session::new()?,
            vars: 0,
        })
    }

    pub fn backend_name(&self) -> &'static str {
        self.session.backend_name()
    }
}

impl SatSolver for IpasirSolver {
    fn add_variables(&mut self, n: usize) {
        self.vars += n;
    }

    fn num_variables(&self) -> usize {
        self.vars
    }

    fn add_clause(&mut self, lits: &[i64]) -> bool {
        let clause: Vec<i32> = lits.iter().map(|&l| l as i32).collect();
        self.session.add_clause(&clause);
        true
    }

    fn solve(&mut self) -> bool {
        self.session.solve() == IPASIR_SAT
    }

    fn value_of(&self, var: i64) -> bool {
        self.session.value(var as i32) == var as i32
    }
}
