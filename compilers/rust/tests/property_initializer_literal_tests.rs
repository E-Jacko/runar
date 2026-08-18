//! Audit C3 — property initializers are restricted to literal values.
//!
//! `ts`, `go` and `java` enforced this; `rust`, `zig`, `python` and `ruby` did
//! not — they compiled e.g. `p: bigint = 1n + 2n;` and emitted a deployable
//! locking script for a program the language does not define.
//!
//! Mirrors `packages/runar-compiler/src/__tests__/property-initializer-literal.test.ts`.

use runar_compiler_rust::frontend_validate;

/// The cross-tier diagnostic substring.
const NON_LITERAL_INIT: &str = "initializer must be a literal value";

fn errors_of(source: &str) -> Vec<String> {
    let (errors, _warnings) = frontend_validate(source, Some("test.runar.ts"));
    errors
}

#[test]
fn rejects_arithmetic_property_initializer() {
    let source = r#"
import { StatefulSmartContract, Addr } from 'runar-lang';

class Bad extends StatefulSmartContract {
    count: bigint = 1n + 2n;
    readonly owner: Addr;

    constructor(owner: Addr) {
        super(owner);
        this.owner = owner;
    }

    public bump() {
        this.count = this.count + 1n;
    }
}
"#;
    let errors = errors_of(source);
    assert!(
        errors.iter().any(|e| e.contains(NON_LITERAL_INIT)),
        "expected a non-literal-initializer error, got: {errors:?}"
    );
}

#[test]
fn rejects_call_expression_property_initializer() {
    let source = r#"
import { StatefulSmartContract, Addr } from 'runar-lang';

class Bad2 extends StatefulSmartContract {
    count: bigint = abs(-3n);
    readonly owner: Addr;

    constructor(owner: Addr) {
        super(owner);
        this.owner = owner;
    }

    public bump() {
        this.count = this.count + 1n;
    }
}
"#;
    let errors = errors_of(source);
    assert!(
        errors.iter().any(|e| e.contains(NON_LITERAL_INIT)),
        "expected a non-literal-initializer error, got: {errors:?}"
    );
}

#[test]
fn accepts_literal_property_initializers() {
    let source = r#"
import { StatefulSmartContract, Addr, ByteString } from 'runar-lang';

class Good extends StatefulSmartContract {
    count: bigint = 7n;
    flag: boolean = true;
    tag: ByteString = 'deadbeef';
    offset: bigint = -3n;
    readonly owner: Addr;

    constructor(owner: Addr) {
        super(owner);
        this.owner = owner;
    }

    public bump() {
        this.count = this.count + 1n;
    }
}
"#;
    let errors = errors_of(source);
    assert!(errors.is_empty(), "expected no errors, got: {errors:?}");
}
