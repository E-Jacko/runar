# frozen_string_literal: true

# Audit C3 -- property initializers are restricted to literal values.
#
# `ts`, `go` and `java` enforced this; `rust`, `zig`, `python` and `ruby` did
# not -- they compiled e.g. `p: bigint = 1n + 2n;` and emitted a deployable
# locking script for a program the language does not define.
#
# Mirrors packages/runar-compiler/src/__tests__/property-initializer-literal.test.ts

require_relative "test_helper"

require "runar_compiler/frontend/ast_nodes"
require "runar_compiler/frontend/diagnostic"
require "runar_compiler/frontend/validator"
require "runar_compiler/frontend/parser_ts"

class TestPropertyInitializerLiteral < Minitest::Test
  include RunarCompiler::Frontend

  # The cross-tier diagnostic substring.
  NON_LITERAL_INIT = "initializer must be a literal value"

  def validate_source(source, file_name = "Test.runar.ts")
    result = RunarCompiler.send(:_parse_source, source, file_name)
    assert_empty result.errors.map(&:format_message), "unexpected parse errors"
    refute_nil result.contract, "expected a contract from parsing"
    RunarCompiler::Frontend.validate(result.contract)
  end

  def assert_non_literal_init_error(result)
    assert result.errors.any? { |e| e.message.include?(NON_LITERAL_INIT) },
           "expected a non-literal-initializer error, got: #{result.error_strings}"
  end

  def test_rejects_arithmetic_property_initializer
    source = <<~TS
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
    TS
    assert_non_literal_init_error(validate_source(source))
  end

  def test_rejects_call_expression_property_initializer
    source = <<~TS
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
    TS
    assert_non_literal_init_error(validate_source(source))
  end

  def test_accepts_literal_property_initializers
    source = <<~TS
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
    TS
    result = validate_source(source)
    assert_empty result.error_strings
  end
end
