//! Turning a lowering-pass refusal into a diagnostic — quietly.
//!
//! Passes 4 and 5 refuse a construct they must not emit by panicking, and both
//! wrap themselves in `catch_unwind` so the refusal reaches the caller as an
//! `Err` instead of unwinding out of the compiler. That much already matched
//! the other six tiers.
//!
//! What did NOT match is what the USER sees. Rust's default panic hook writes
//!
//! ```text
//! thread 'main' panicked at src/codegen/stack.rs:1350:13:
//! <the diagnostic>
//! note: run with `RUST_BACKTRACE=1` environment variable to display a backtrace
//! ```
//!
//! to stderr *before* `catch_unwind` ever gets the payload. So a refusal the
//! TS / Go / Python / Zig / Ruby / Java tiers report as one clean line came out
//! of the Rust tier as a compiler crash report with a source location inside
//! the compiler and an invitation to collect a backtrace — reading, to anyone
//! holding a contract that will not compile, like a bug in Rúnar rather than a
//! diagnosis of their contract. The `Err` was then printed a second time.
//!
//! `catch_refusal` silences the hook for exactly the duration of the guarded
//! call, so the payload surfaces once, as a diagnostic. Genuine unexpected
//! panics still surface — they arrive as the same `Err` and are still printed
//! by the caller; only the hook's banner is suppressed, and only inside a
//! boundary that already treats every panic as a diagnostic.
//!
//! The hook is process-global. The compiler drives these passes from one
//! thread, so the swap is not observable elsewhere; do not call this from a
//! parallel pipeline without revisiting that.

use std::panic::{self, AssertUnwindSafe};

/// Run `f`, converting a panic into `Err(format!("{prefix}: {payload}"))`
/// without letting the default panic hook print its banner first.
pub fn catch_refusal<T>(prefix: &str, f: impl FnOnce() -> T) -> Result<T, String> {
    let previous = panic::take_hook();
    panic::set_hook(Box::new(|_| {}));
    let outcome = panic::catch_unwind(AssertUnwindSafe(f));
    panic::set_hook(previous);

    outcome.map_err(|e| {
        if let Some(s) = e.downcast_ref::<String>() {
            format!("{}: {}", prefix, s)
        } else if let Some(s) = e.downcast_ref::<&str>() {
            format!("{}: {}", prefix, s)
        } else {
            format!("{}: internal error", prefix)
        }
    })
}
