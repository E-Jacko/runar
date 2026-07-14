//! constructorArgs shape/key validation — port of the TypeScript
//! `constructor-args-validation.test.ts` (PR #113, fix 1).
//!
//! `compile*_with_options(opts.constructor_args)` must reject inputs that
//! would silently bake nothing and emit placeholder scripts that fail
//! opaquely at runtime:
//!
//!  (a) positional arrays — N/A for the Rust tier (constructor_args is a
//!      typed `HashMap<String, Value>`, so no positional array can reach it);
//!  (b) keys that don't match any contract property (typos);
//!  (c) referenced readonly properties left unbaked after applying the args.

use std::collections::HashMap;

use runar_compiler_rust::{compile_from_source_str_with_options, CompileOptions};

const HASH_LOCK_SOURCE: &str = r#"
class HashLock extends SmartContract {
  readonly hashValue: Sha256;

  constructor(hashValue: Sha256) {
    super(hashValue);
    this.hashValue = hashValue;
  }

  public unlock(preimage: ByteString) {
    assert(sha256(preimage) === this.hashValue);
  }
}
"#;

const TWO_PROP_SOURCE: &str = r#"
class TwoProp extends SmartContract {
  readonly target: bigint;
  readonly unused: bigint;

  constructor(target: bigint, unused: bigint) {
    super(target, unused);
    this.target = target;
    this.unused = unused;
  }

  public check(x: bigint) {
    assert(x === this.target);
  }
}
"#;

fn hash() -> String {
    "aa".repeat(32)
}

fn opts_with(args: HashMap<String, serde_json::Value>) -> CompileOptions {
    CompileOptions {
        constructor_args: args,
        ..Default::default()
    }
}

#[test]
fn rejects_keys_that_match_no_contract_property() {
    let mut args = HashMap::new();
    // typo: hashVal instead of hashValue
    args.insert("hashVal".to_string(), serde_json::Value::String(hash()));

    let result = compile_from_source_str_with_options(
        HASH_LOCK_SOURCE,
        Some("HashLock.runar.ts"),
        &opts_with(args),
    );

    let err = result.expect_err("typo key must be rejected");
    assert!(err.contains("hashVal"), "error should name the offending key: {}", err);
    assert!(
        err.contains("hashValue"),
        "error should list valid property names: {}",
        err
    );
}

#[test]
fn rejects_when_a_referenced_readonly_property_remains_unbaked() {
    let mut args = HashMap::new();
    // 'target' is referenced by check() but not provided.
    args.insert("unused".to_string(), serde_json::Value::from(1));

    let result = compile_from_source_str_with_options(
        TWO_PROP_SOURCE,
        Some("TwoProp.runar.ts"),
        &opts_with(args),
    );

    let err = result.expect_err("unbaked referenced readonly must be rejected");
    assert!(err.contains("target"), "error should name 'target': {}", err);
    assert!(
        err.contains("placeholder"),
        "error should mention the placeholder hazard: {}",
        err
    );
}

#[test]
fn accepts_an_unreferenced_readonly_property_left_unbaked() {
    let mut args = HashMap::new();
    // 'unused' is never referenced by a method — DCE eliminates it, so
    // leaving it unbaked is fine.
    args.insert("target".to_string(), serde_json::Value::from(42));

    let result = compile_from_source_str_with_options(
        TWO_PROP_SOURCE,
        Some("TwoProp.runar.ts"),
        &opts_with(args),
    );

    let artifact = result.expect("unreferenced unbaked readonly should be allowed");
    assert!(!artifact.script.is_empty(), "script hex should be present");
}

#[test]
fn accepts_a_complete_named_record() {
    let mut args = HashMap::new();
    args.insert("hashValue".to_string(), serde_json::Value::String(hash()));

    let result = compile_from_source_str_with_options(
        HASH_LOCK_SOURCE,
        Some("HashLock.runar.ts"),
        &opts_with(args),
    );

    let artifact = result.expect("complete record should compile");
    assert!(
        artifact.script.contains(&hash()),
        "baked script should contain the hash bytes"
    );
}

#[test]
fn still_compiles_placeholder_artifacts_when_no_constructor_args_given() {
    let result = compile_from_source_str_with_options(
        HASH_LOCK_SOURCE,
        Some("HashLock.runar.ts"),
        &CompileOptions::default(),
    );

    let artifact = result.expect("no-args placeholder compile should succeed");
    assert!(
        !artifact.constructor_slots.is_empty(),
        "placeholder artifact should carry constructor slots"
    );
}
