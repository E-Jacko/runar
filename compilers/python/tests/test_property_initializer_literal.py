"""Audit C3 -- property initializers are restricted to literal values.

``ts``, ``go`` and ``java`` enforced this; ``rust``, ``zig``, ``python`` and
``ruby`` did not -- they compiled e.g. ``p: bigint = 1n + 2n;`` and emitted a
deployable locking script for a program the language does not define.

Mirrors ``packages/runar-compiler/src/__tests__/property-initializer-literal.test.ts``.
"""

from __future__ import annotations

from runar_compiler.frontend.parser_dispatch import parse_source
from runar_compiler.frontend.validator import ValidationResult, validate

# The cross-tier diagnostic substring.
NON_LITERAL_INIT = "initializer must be a literal value"


def validate_source(source: str) -> ValidationResult:
    result = parse_source(source, "Test.runar.ts")
    assert result.contract is not None, f"parse failed: {result.errors}"
    return validate(result.contract)


def has_error(result: ValidationResult, needle: str) -> bool:
    return any(needle in d.message for d in result.errors)


def test_rejects_arithmetic_property_initializer():
    source = """
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
"""
    result = validate_source(source)
    assert has_error(result, NON_LITERAL_INIT), (
        f"expected a non-literal-initializer error, got: {result.error_strings()}"
    )


def test_rejects_call_expression_property_initializer():
    source = """
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
"""
    result = validate_source(source)
    assert has_error(result, NON_LITERAL_INIT), (
        f"expected a non-literal-initializer error, got: {result.error_strings()}"
    )


def test_accepts_literal_property_initializers():
    source = """
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
"""
    result = validate_source(source)
    assert result.errors == [], f"expected no errors, got: {result.error_strings()}"
