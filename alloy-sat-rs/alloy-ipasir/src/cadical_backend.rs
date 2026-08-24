use crate::backend::{Backend, CancelToken, Outcome};
use cadical::{Callbacks, Solver};

/// Bridge that lets CaDiCaL's periodic termination checks observe the shared
/// cancellation token.
struct CancelBridge(CancelToken);

impl Callbacks for CancelBridge {
    fn terminate(&mut self) -> bool {
        self.0.is_cancelled()
    }
}

pub struct CadicalBackend {
    inner: Solver<CancelBridge>,
    cancel: CancelToken,
}

impl CadicalBackend {
    pub fn new(cancel: CancelToken) -> Self {
        let mut solver = Solver::new();
        solver.set_callbacks(Some(CancelBridge(cancel.clone())));
        CadicalBackend {
            inner: solver,
            cancel,
        }
    }
}

impl Backend for CadicalBackend {
    fn name(&self) -> &'static str {
        "cadical"
    }

    fn add_clause(&mut self, lits: &[i32]) {
        self.inner.add_clause(lits.iter().copied());
    }

    fn solve(&mut self, assumptions: &[i32]) -> Result<Outcome, String> {
        // Refresh the bridge each solve so a token installed after
        // construction is honoured too.
        self.inner
            .set_callbacks(Some(CancelBridge(self.cancel.clone())));
        let r = if assumptions.is_empty() {
            self.inner.solve()
        } else {
            self.inner.solve_with(assumptions.iter().copied())
        };
        match r {
            Some(true) => Ok(Outcome::Sat),
            Some(false) => Ok(Outcome::Unsat),
            None => Ok(Outcome::Unknown),
        }
    }

    fn value(&self, lit: i32) -> Option<bool> {
        self.inner.value(lit)
    }

    fn failed(&self, lit: i32) -> bool {
        self.inner.failed(lit)
    }

    fn max_var(&self) -> i32 {
        self.inner.max_variable()
    }
}
