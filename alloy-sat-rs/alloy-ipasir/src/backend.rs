use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

/// Shared cancellation token. Set by the host from any thread; solvers that
/// support interruption poll it during search.
#[derive(Clone, Default)]
pub struct CancelToken(Arc<AtomicBool>);

impl CancelToken {
    pub fn cancel(&self) {
        self.0.store(true, Ordering::Relaxed);
    }

    /// Reset before starting a new solve so stale cancellations are dropped.
    pub fn reset(&self) {
        self.0.store(false, Ordering::Relaxed);
    }

    pub fn is_cancelled(&self) -> bool {
        self.0.load(Ordering::Relaxed)
    }
}

pub enum Outcome {
    Sat,
    Unsat,
    Unknown,
}

pub trait Backend {
    fn name(&self) -> &'static str;

    fn add_clause(&mut self, lits: &[i32]);

    /// Solve under the given assumptions.
    fn solve(&mut self, assumptions: &[i32]) -> Result<Outcome, String>;

    /// Value of `lit` after a SAT result. `None` means the formula does not
    /// constrain the variable (either polarity satisfies it).
    fn value(&self, lit: i32) -> Option<bool>;

    /// Highest variable index touched by the formula.
    fn max_var(&self) -> i32 {
        0
    }

    /// Whether `solve` supports assumptions.
    fn supports_assumptions(&self) -> bool {
        true
    }

    /// Whether the assumption literal was *failed* in the last UNSAT solve
    /// (i.e. it participates in the final conflict). Only meaningful after an
    /// UNSAT result obtained under assumptions; backends without assumption
    /// support always report `false`.
    fn failed(&self, _lit: i32) -> bool {
        false
    }
}

/// Create the backend named by `ALLOY_SAT_BACKEND`, or the first available
/// one. Called on the worker thread, so the backend never crosses threads.
pub fn create_backend(cancel: CancelToken) -> Result<Box<dyn Backend>, String> {
    let mut candidates: Vec<&str> = Vec::new();
    if let Ok(name) = std::env::var("ALLOY_SAT_BACKEND") {
        candidates.push(Box::leak(name.into_boxed_str()) as &str);
    }
    #[cfg(feature = "cadical")]
    candidates.push("cadical");
    #[cfg(feature = "splr")]
    candidates.push("splr");

    for name in candidates {
        match name {
            #[cfg(feature = "cadical")]
            "cadical" => {
                return Ok(Box::new(crate::cadical_backend::CadicalBackend::new(
                    cancel,
                )))
            }
            #[cfg(feature = "splr")]
            "splr" => return Ok(Box::new(crate::splr_backend::SplrBackend::new())),
            _ => {}
        }
    }
    Err("no SAT backend compiled in (enable feature cadical and/or splr)".to_string())
}
