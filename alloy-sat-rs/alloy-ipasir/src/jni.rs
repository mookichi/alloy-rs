//! JNI bindings exposing the async worker as
//! `org.alloytools.solvers.natv.ipasir.IpasirWorker`.
//!
//! Only `addClause` touches the JNIEnv (to copy the literal array); every
//! other export works on the raw `Worker` pointer alone.

use jni::errors::Error;
use jni::objects::{JClass, JIntArray, JObject};
use jni::sys::{jboolean, jint, jlong};
use jni::EnvUnowned;

use crate::worker::Worker;

fn worker(peer: jlong) -> Option<&'static mut Worker> {
    // Safety: the JVM holds the sole Box<Worker>, handed out by `make`
    // and reclaimed exactly once by `free`.
    unsafe { (peer as *mut Worker).as_mut() }
}

/// static long make()
#[no_mangle]
pub extern "system" fn Java_org_alloytools_solvers_natv_ipasir_IpasirWorker_make<'local>(
    _env: EnvUnowned<'local>,
    _class: JClass<'local>,
) -> jlong {
    match Worker::spawn() {
        Ok(w) => Box::into_raw(Box::new(w)) as jlong,
        Err(_) => 0,
    }
}

/// void free(long peer)
#[no_mangle]
pub extern "system" fn Java_org_alloytools_solvers_natv_ipasir_IpasirWorker_free<'local>(
    _env: EnvUnowned<'local>,
    _this: JObject<'local>,
    peer: jlong,
) {
    if peer != 0 {
        drop(unsafe { Box::from_raw(peer as *mut Worker) });
    }
}

/// void addVariables(long peer, int n) — IPASIR variables are implicit.
#[no_mangle]
pub extern "system" fn Java_org_alloytools_solvers_natv_ipasir_IpasirWorker_addVariables<'local>(
    _env: EnvUnowned<'local>,
    _this: JObject<'local>,
    _peer: jlong,
    _n: jint,
) {
}

/// boolean addClause(long peer, int[] lits)
#[no_mangle]
pub extern "system" fn Java_org_alloytools_solvers_natv_ipasir_IpasirWorker_addClause<'local>(
    mut env: EnvUnowned<'local>,
    _this: JObject<'local>,
    peer: jlong,
    lits: JIntArray<'local>,
) -> jboolean {
    let Some(worker) = worker(peer) else {
        return false;
    };
    let result = env.with_env(|env| -> Result<bool, Error> {
        let len = lits.len(env)?;
        let mut buf = vec![0i32; len];
        lits.get_region(env, 0, &mut buf)?;
        buf.retain(|&l| l != i32::MIN);
        worker.add_clause(buf);
        Ok(true)
    });
    let ok: bool = result.resolve::<jni::errors::ThrowRuntimeExAndDefault>();
    ok as jboolean
}

/// boolean solve(long peer) — blocking solve over the worker.
#[no_mangle]
pub extern "system" fn Java_org_alloytools_solvers_natv_ipasir_IpasirWorker_solve<'local>(
    _env: EnvUnowned<'local>,
    _this: JObject<'local>,
    peer: jlong,
) -> jboolean {
    let Some(worker) = worker(peer) else {
        return false;
    };
    worker.start_solve(Vec::new());
    (worker.wait() == crate::IPASIR_SAT) as jboolean
}

/// boolean valueOf(long peer, int lit)
#[no_mangle]
pub extern "system" fn Java_org_alloytools_solvers_natv_ipasir_IpasirWorker_valueOf<'local>(
    _env: EnvUnowned<'local>,
    _this: JObject<'local>,
    peer: jlong,
    lit: jint,
) -> jboolean {
    let Some(worker) = worker(peer) else {
        return false;
    };
    if lit == 0 {
        return false;
    }
    (worker.value_of(lit) == lit) as jboolean
}

/// void solveAsync0(long peer) — submit a non-blocking solve.
#[no_mangle]
pub extern "system" fn Java_org_alloytools_solvers_natv_ipasir_IpasirWorker_solveAsync0<'local>(
    _env: EnvUnowned<'local>,
    _this: JObject<'local>,
    peer: jlong,
) {
    if let Some(worker) = worker(peer) {
        worker.start_solve(Vec::new());
    }
}

/// int status0(long peer) — -1 running / 10 SAT / 20 UNSAT / 0 unknown.
#[no_mangle]
pub extern "system" fn Java_org_alloytools_solvers_natv_ipasir_IpasirWorker_status0<'local>(
    _env: EnvUnowned<'local>,
    _this: JObject<'local>,
    peer: jlong,
) -> jint {
    match worker(peer) {
        Some(worker) => worker.status(),
        None => crate::IPASIR_INTERRUPTED,
    }
}

/// int waitSolution0(long peer) — block until the solve finishes.
#[no_mangle]
pub extern "system" fn Java_org_alloytools_solvers_natv_ipasir_IpasirWorker_waitSolution0<
    'local,
>(
    _env: EnvUnowned<'local>,
    _this: JObject<'local>,
    peer: jlong,
) -> jint {
    match worker(peer) {
        Some(worker) => worker.wait(),
        None => crate::IPASIR_INTERRUPTED,
    }
}

/// void cancel0(long peer) — request interruption from any thread.
#[no_mangle]
pub extern "system" fn Java_org_alloytools_solvers_natv_ipasir_IpasirWorker_cancel0<'local>(
    _env: EnvUnowned<'local>,
    _this: JObject<'local>,
    peer: jlong,
) {
    if let Some(worker) = worker(peer) {
        worker.cancel();
    }
}
