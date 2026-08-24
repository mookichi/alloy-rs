//! JNI binding: `edu.mit.csail.sdg.translator.RustEngineProxy.solveNative`
//! (`static native byte[] solveNative(byte[] problem)`).
//!
//! One attached-env closure copies the problem bytes, solves without holding
//! JNI handles, and builds the answer array; failures surface as a thrown
//! RuntimeException with a null return (jni crate `ThrowRuntimeExAndDefault`).

use jni::errors::Error;
use jni::objects::{JByteArray, JClass};
use jni::EnvUnowned;

/// static native byte[] solveNative(byte[] problem)
#[no_mangle]
pub extern "system" fn Java_edu_mit_csail_sdg_translator_RustEngineProxy_solveNative<'local>(
    mut env: EnvUnowned<'local>,
    _class: JClass<'local>,
    problem: JByteArray<'local>,
) -> JByteArray<'local> {
    let made = env.with_env(|env| -> Result<JByteArray<'local>, Error> {
        let input = env.convert_byte_array(&problem)?;
        // Heavy solving happens inside; no JNI handles are held meanwhile.
        let answer = crate::solve_wire(&input);
        env.byte_array_from_slice(&answer)
    });
    made.resolve::<jni::errors::ThrowRuntimeExAndDefault>()
}
