//! R3 regression — `prepare_call_terminal`'s continuation-satoshis resolution
//! must honor the user's explicit `outputSatoshis` ABI param.
//!
//! Strategy:
//!   We unit-test `resolve_continuation_satoshis` directly. This helper is
//!   the SAME code the production `prepare_call_terminal` calls inline — the
//!   patch routes the call site through this helper so test + production
//!   share one canonical implementation, eliminating any "test passes but
//!   production diverges" risk.
//!
//! The bug pre-patch: continuation output satoshis were hard-set to
//! `current_utxo.satoshis`, ignoring the user's declared `outputSatoshis`
//! ABI param (the value the compiler bakes into the on-chain `hashOutputs`
//! covenant). The on-chain HASH check then failed and ARC rejected the
//! broadcast with HTTP 461.
//!
//! After the patch, resolution priority is:
//!   1. CallOptions.satoshis (caller override)
//!   2. user's `outputSatoshis` ABI arg
//!   3. legacy fallback: current_utxo.satoshis

use runar_lang::sdk::anf_interpreter::OrderedOutputEntry;
use runar_lang::sdk::contract::resolve_continuation_satoshis;
use runar_lang::sdk::types::SdkValue;

/// These R3 rung tests exercise the `outputSatoshis`-param path with no ANF
/// addOutput recorded, so the ordered-outputs slice is always empty.
const NO_ORDERED_OUTPUTS: &[OrderedOutputEntry] = &[];

#[test]
fn r3_user_output_satoshis_arg_overrides_input_utxo() {
    // Method declares: setBalance(newBalance: bigint, outputSatoshis: bigint)
    // User passes (newBalance=2000, outputSatoshis=3000).
    // Input UTXO holds 5000 sats.
    // Continuation must carry 3000 (user arg), NOT 5000 (input).
    let names = ["newBalance", "outputSatoshis"];
    let args = vec![SdkValue::Int(2_000), SdkValue::Int(3_000)];
    let current_utxo_satoshis = 5_000;

    let resolved =
        resolve_continuation_satoshis(&names, &args, None, NO_ORDERED_OUTPUTS, current_utxo_satoshis);

    assert_eq!(
        resolved, 3_000,
        "R3 regression: continuation must use user's outputSatoshis arg (3000), \
         not the input UTXO's satoshis (5000). Found: {}",
        resolved
    );
}

#[test]
fn r3_call_options_satoshis_beats_user_arg() {
    // Caller passes options.satoshis=7000. User passes outputSatoshis=3000.
    // The CallOptions override wins.
    let names = ["newBalance", "outputSatoshis"];
    let args = vec![SdkValue::Int(2_000), SdkValue::Int(3_000)];

    let resolved =
        resolve_continuation_satoshis(&names, &args, Some(7_000), NO_ORDERED_OUTPUTS, 5_000);

    assert_eq!(resolved, 7_000, "CallOptions.satoshis must override user arg");
}

#[test]
fn r3_legacy_no_output_satoshis_param_falls_back_to_input_utxo() {
    // Method does NOT declare outputSatoshis. Legacy behavior: continuation
    // uses input UTXO satoshis. Locks the no-regression contract.
    let names = ["newBalance"];
    let args = vec![SdkValue::Int(2_000)];

    let resolved = resolve_continuation_satoshis(&names, &args, None, NO_ORDERED_OUTPUTS, 5_000);

    assert_eq!(
        resolved, 5_000,
        "without outputSatoshis param: must fall back to input UTXO satoshis"
    );
}

#[test]
fn r3_param_declared_but_arg_not_int_falls_back() {
    // Edge case: outputSatoshis param is declared but the caller passed
    // something other than Int (e.g. Auto, or accidentally Bytes). The
    // resolver should fall back rather than panic — that locks in the
    // type-narrow rung from the patch (matches SdkValue::Int only).
    let names = ["newBalance", "outputSatoshis"];
    let args = vec![SdkValue::Int(2_000), SdkValue::Auto];

    let resolved = resolve_continuation_satoshis(&names, &args, None, NO_ORDERED_OUTPUTS, 5_000);

    assert_eq!(
        resolved, 5_000,
        "non-Int outputSatoshis arg must fall through to legacy"
    );
}

// --- New rung: an explicit single `this.addOutput(<sats>, ...)` recorded by the
// ANF interpreter drives the continuation amount ahead of the input-value
// fallback (generalizes finding G1 to the no-raw single-continuation path). ---

use runar_lang::sdk::anf_interpreter::OrderedOutputKind;

fn state(satoshis: i64) -> OrderedOutputEntry {
    OrderedOutputEntry { kind: OrderedOutputKind::State, satoshis, script: None }
}

fn raw(satoshis: i64) -> OrderedOutputEntry {
    OrderedOutputEntry {
        kind: OrderedOutputKind::Raw,
        satoshis,
        script: Some("76a914".to_string()),
    }
}

#[test]
fn single_explicit_addoutput_drives_continuation_over_input_value() {
    // No options.satoshis, no outputSatoshis param, but the method emits a lone
    // `addOutput(1000, ...)`. Continuation must use 1000, not the 1-sat input.
    let names: [&str; 0] = [];
    let args: Vec<SdkValue> = vec![];
    let ordered = [state(1_000)];

    let resolved = resolve_continuation_satoshis(&names, &args, None, &ordered, 1);

    assert_eq!(
        resolved, 1_000,
        "single explicit addOutput must set the continuation amount, not the input value"
    );
}

#[test]
fn call_options_satoshis_beats_explicit_addoutput() {
    // CallOptions.satoshis still wins over the ANF-recorded addOutput amount.
    let names: [&str; 0] = [];
    let args: Vec<SdkValue> = vec![];
    let ordered = [state(1_000)];

    let resolved = resolve_continuation_satoshis(&names, &args, Some(7_000), &ordered, 1);

    assert_eq!(resolved, 7_000, "options.satoshis must override the addOutput amount");
}

#[test]
fn output_satoshis_param_beats_explicit_addoutput() {
    // The existing outputSatoshis ABI-param rung still outranks the ANF rung.
    let names = ["newBalance", "outputSatoshis"];
    let args = vec![SdkValue::Int(2_000), SdkValue::Int(3_000)];
    let ordered = [state(1_000)];

    let resolved = resolve_continuation_satoshis(&names, &args, None, &ordered, 1);

    assert_eq!(resolved, 3_000, "outputSatoshis ABI arg must outrank the addOutput amount");
}

#[test]
fn lone_raw_output_falls_through_to_input_value() {
    // A single raw output (no state continuation) is not a single-state layout;
    // it must fall through to the legacy input-value default (the raw-output
    // branch handles its own amount, finding G1).
    let names: [&str; 0] = [];
    let args: Vec<SdkValue> = vec![];
    let ordered = [raw(1_000)];

    let resolved = resolve_continuation_satoshis(&names, &args, None, &ordered, 42);

    assert_eq!(resolved, 42, "lone raw output must not drive the continuation amount");
}

#[test]
fn multiple_ordered_outputs_fall_through_to_input_value() {
    // More than one ordered output (e.g. raw + state) is not the single-state
    // case; the ordered-list branch handles that layout, so the resolver falls
    // back to the legacy input value here.
    let names: [&str; 0] = [];
    let args: Vec<SdkValue> = vec![];
    let ordered = [raw(1_000), state(500)];

    let resolved = resolve_continuation_satoshis(&names, &args, None, &ordered, 42);

    assert_eq!(resolved, 42, "multi-output layout must fall through to the input value");
}
