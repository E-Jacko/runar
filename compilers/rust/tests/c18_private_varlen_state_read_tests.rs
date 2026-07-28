//! Deep-review finding C18 (P1 funds-safety) — Rust tier.
//!
//! `method_reads_var_len_state` in `codegen/stack.rs` only walked a method's
//! OWN bindings (plus `if`/`loop` bodies) looking for a direct `load_prop` on a
//! mutable variable-length (ByteString) state field. It did NOT recurse into
//! private helper methods invoked via `method_call` — unlike its sibling walker
//! `method_uses_check_preimage`, which already does.
//!
//! Consequence: a PUBLIC method that reads a mutable ByteString state field
//! ONLY through a PRIVATE helper never set `uses_code_part`, so `_codePart` was
//! never pushed as an implicit parameter and `lower_deserialize_state` took the
//! "terminal method, skip variable-length deserialization" shortcut. The
//! private helper's `load_prop` then fell back to the deploy-time constant
//! (constructor placeholder) instead of the live on-chain state — a silent
//! wrong-result / funds-safety bug. Private methods are INLINED into the
//! caller's stack context, so the helper variant must lower identically to the
//! direct-read control.

use runar_compiler_rust::codegen::stack::lower_to_stack;
use runar_compiler_rust::frontend::diagnostic::Severity;
use runar_compiler_rust::frontend::{anf_lower::lower_to_anf, parser::parse_source};
use runar_compiler_rust::{compile_from_source_str_with_result, CompileOptions};

/// Control: the public method reads the mutable ByteString field directly.
const DIRECT: &str = r#"import { StatefulSmartContract, assert, len } from 'runar-lang';
import type { ByteString } from 'runar-lang';
class StateReadDirect extends StatefulSmartContract {
  tag: ByteString;
  constructor(tag: ByteString) { super(tag); this.tag = tag; }
  public check(expected: bigint): void { assert(len(this.tag) === expected); }
}"#;

/// Bug case: the public method reads the same field ONLY via a private helper.
const VIA_HELPER: &str = r#"import { StatefulSmartContract, assert, len } from 'runar-lang';
import type { ByteString } from 'runar-lang';
class StateReadViaHelper extends StatefulSmartContract {
  tag: ByteString;
  constructor(tag: ByteString) { super(tag); this.tag = tag; }
  private tagLen(): bigint { return len(this.tag); }
  public check(expected: bigint): void { assert(this.tagLen() === expected); }
}"#;

/// Mutual recursion between two private helpers: the cycle guard must keep the
/// walker from hanging, and the var-length read in the second helper must still
/// be found.
const MUTUAL_HELPERS: &str = r#"import { StatefulSmartContract, assert, len } from 'runar-lang';
import type { ByteString } from 'runar-lang';
class StateReadMutual extends StatefulSmartContract {
  tag: ByteString;
  constructor(tag: ByteString) { super(tag); this.tag = tag; }
  private a(): bigint { return this.b(); }
  private b(): bigint { return len(this.tag); }
  public check(expected: bigint): void { assert(this.a() === expected); }
}"#;

fn uses_code_part(src: &str) -> bool {
    let parsed = parse_source(src, Some("X.runar.ts"));
    let contract = parsed.contract.expect("parse failed");
    let anf = lower_to_anf(&contract);
    let methods = lower_to_stack(&anf).expect("stack lowering failed");
    let method = methods
        .iter()
        .find(|m| m.name == "check")
        .expect("no `check` method in stack program");
    method.uses_code_part
}

fn script_hex(src: &str, file: &str) -> String {
    let opts = CompileOptions {
        disable_constant_folding: true,
        ..CompileOptions::default()
    };
    let result = compile_from_source_str_with_result(src, Some(file), &opts);
    assert!(
        !result
            .diagnostics
            .iter()
            .any(|d| d.severity == Severity::Error),
        "compile errors for {}: {:?}",
        file,
        result.diagnostics
    );
    result.script_hex.expect("no script hex")
}

#[test]
fn control_direct_read_sets_uses_code_part() {
    assert!(
        uses_code_part(DIRECT),
        "control: a direct read of a mutable ByteString field must set uses_code_part"
    );
}

#[test]
fn read_via_private_helper_also_sets_uses_code_part() {
    assert!(
        uses_code_part(VIA_HELPER),
        "C18: a read of a mutable ByteString field inside a PRIVATE helper must \
         also set uses_code_part on the public entry point"
    );
}

#[test]
fn read_via_mutually_recursive_helpers_sets_uses_code_part() {
    assert!(
        uses_code_part(MUTUAL_HELPERS),
        "C18: the private-method recursion must reach a var-length read behind a \
         chain of helpers (and terminate on cycles)"
    );
}

#[test]
fn helper_variant_emits_the_same_script_as_the_direct_control() {
    let direct = script_hex(DIRECT, "StateReadDirect.runar.ts");
    let via_helper = script_hex(VIA_HELPER, "StateReadViaHelper.runar.ts");
    assert_eq!(
        direct, via_helper,
        "C18: private helpers are inlined, so the helper variant must emit the \
         same locking script as the direct-read control"
    );
}
