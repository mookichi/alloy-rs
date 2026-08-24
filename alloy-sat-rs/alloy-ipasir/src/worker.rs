use std::ffi::c_int;
use std::sync::mpsc;
use std::sync::{Arc, Condvar, Mutex};
use std::thread::JoinHandle;

use crate::backend::{create_backend, Backend, CancelToken, Outcome};

/// Solve status: still running / no result yet.
pub const STATUS_RUNNING: c_int = -1;

enum Command {
    Add(Vec<c_int>),
    /// Solve under the given assumptions.
    Solve(Vec<c_int>),
    Free,
}

/// Shared solve-result slot. The posting side sets `STATUS_RUNNING` before
/// submitting a solve; the worker overwrites it with 10/20/0 and notifies.
#[derive(Default)]
struct Slot(Mutex<c_int>, Condvar);

impl Slot {
    fn set(&self, v: c_int) {
        let mut guard = self.0.lock().unwrap();
        *guard = v;
        self.1.notify_all();
    }

    fn get(&self) -> c_int {
        *self.0.lock().unwrap()
    }

    fn wait(&self) -> c_int {
        let mut guard = self.0.lock().unwrap();
        while *guard == STATUS_RUNNING {
            guard = self.1.wait(guard).unwrap();
        }
        *guard
    }
}

/// A dedicated solver thread. All backend state lives on that thread; hosts
/// interact exclusively through commands and shared status slots.
pub struct Worker {
    tx: Option<mpsc::Sender<Command>>,
    cancel: CancelToken,
    status: Arc<Slot>,
    /// Assignment snapshot (index = var-1) filled after each SAT result.
    model: Arc<Mutex<Vec<bool>>>,
    join: Mutex<Option<JoinHandle<()>>>,
    name: &'static str,
    supports_assumptions: bool,
}

impl Worker {
    /// Spawn the worker thread and construct the backend inside it.
    ///
    /// Returns an error if no backend is available.
    pub fn spawn() -> Result<Worker, String> {
        let (tx, rx) = mpsc::channel::<Command>();
        let cancel = CancelToken::default();
        let status = Arc::new(Slot(Mutex::new(-1), Condvar::new()));
        let model = Arc::new(Mutex::new(Vec::new()));

        let (ready_tx, ready_rx) = mpsc::channel::<Result<(&'static str, bool), String>>();

        // Slot values are plain i32 codes; see constants in lib.rs.
        const SAT: c_int = 10;
        const UNSAT: c_int = 20;

        let join = std::thread::Builder::new()
            .name("alloy-sat-worker".into())
            .spawn({
                let status = Arc::clone(&status);
                let model = Arc::clone(&model);
                let cancel = cancel.clone();
                move || {
                    let body = || -> Result<(), String> {
                        let mut backend = create_backend(cancel.clone())?;
                        let _ = ready_tx.send(Ok((backend.name(), backend.supports_assumptions())));
                        while let Ok(cmd) = rx.recv() {
                            match cmd {
                                Command::Add(lits) => backend.add_clause(&lits),
                                Command::Solve(assumptions) => {
                                    let result =
                                        backend.solve(&assumptions).unwrap_or(Outcome::Unknown);
                                    match result {
                                        Outcome::Sat => {
                                            *model.lock().unwrap() =
                                                snapshot_model(backend.as_ref());
                                            status.set(SAT);
                                        }
                                        Outcome::Unsat => {
                                            model.lock().unwrap().clear();
                                            status.set(UNSAT);
                                        }
                                        Outcome::Unknown => {
                                            model.lock().unwrap().clear();
                                            status.set(0);
                                        }
                                    }
                                }
                                Command::Free => break,
                            }
                        }
                        Ok(())
                    };
                    // Never leave waiters hanging if the worker panics.
                    if std::panic::catch_unwind(std::panic::AssertUnwindSafe(body)).is_err() {
                        status.set(0);
                    }
                }
            })
            .map_err(|e| format!("failed to spawn solver worker: {e}"))?;

        let (name, supports_assumptions) = ready_rx
            .recv()
            .map_err(|_| "worker died during init".to_string())??;

        Ok(Worker {
            tx: Some(tx),
            cancel,
            status,
            model,
            join: Mutex::new(Some(join)),
            name,
            supports_assumptions,
        })
    }

    pub fn name(&self) -> &'static str {
        self.name
    }

    pub fn supports_assumptions(&self) -> bool {
        self.supports_assumptions
    }

    /// Queue a clause for the worker.
    pub fn add_clause(&self, lits: Vec<c_int>) {
        self.send(Command::Add(lits));
    }

    /// Start an asynchronous solve under `assumptions`.
    pub fn start_solve(&self, assumptions: Vec<c_int>) {
        self.cancel.reset();
        self.status.set(STATUS_RUNNING);
        self.send(Command::Solve(assumptions));
    }

    /// Current solve status: [`STATUS_RUNNING`], 10, 20 or 0.
    pub fn status(&self) -> c_int {
        self.status.get()
    }

    /// Block until the running solve finishes; returns its status.
    pub fn wait(&self) -> c_int {
        self.status.wait()
    }

    /// Request interruption of a running solve from any thread.
    pub fn cancel(&self) {
        self.cancel.cancel();
    }

    /// Value of `lit` after a SAT result: `lit` / `-lit` / 0.
    pub fn value_of(&self, lit: c_int) -> c_int {
        if lit == 0 || lit == i32::MIN || self.status() != 10 {
            return 0;
        }
        let var = lit.unsigned_abs() as usize;
        match self.model.lock().unwrap().get(var - 1) {
            Some(true) => lit.abs(),
            _ => -lit.abs(),
        }
    }

    fn send(&self, cmd: Command) {
        if let Some(tx) = &self.tx {
            // Failure means the worker is gone; results stay at their last value.
            let _ = tx.send(cmd);
        }
    }
}

impl Drop for Worker {
    fn drop(&mut self) {
        if let Some(tx) = self.tx.take() {
            let _ = tx.send(Command::Free);
        }
        if let Some(join) = self.join.lock().unwrap().take() {
            let _ = join.join();
        }
    }
}

fn snapshot_model(backend: &dyn Backend) -> Vec<bool> {
    let max_var = backend.max_var();
    (1..=max_var)
        .map(|v| backend.value(v).unwrap_or(false))
        .collect()
}
