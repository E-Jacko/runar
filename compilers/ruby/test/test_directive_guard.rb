# frozen_string_literal: true

require_relative 'test_helper'

# The @sighash (#123) and @embedAlways (#109) comment directives are
# implemented only in the TypeScript compiler. The Ruby compiler must fail
# closed rather than silently drop them.
class TestDirectiveGuard < Minitest::Test
  def parse(source, file_name = 'Counter.runar.ts')
    RunarCompiler.send(:_parse_source, source, file_name)
  end

  def test_sighash_directive_is_rejected
    source = <<~TS
      class Counter extends SmartContract {
        readonly x: bigint;
        constructor(x: bigint) { super(x); this.x = x; }
        /** @sighash SINGLE|FORKID */
        public unlock() {}
      }
    TS
    result = parse(source)
    joined = result.error_strings.join("\n")
    assert result.errors.any?, 'expected fail-closed error for @sighash'
    assert_includes joined, '@sighash'
    assert_includes joined, '#123'
  end

  def test_embed_always_directive_is_rejected
    source = <<~TS
      class Counter extends SmartContract {
        /** @embedAlways */
        readonly x: bigint;
        constructor(x: bigint) { super(x); this.x = x; }
        public unlock() {}
      }
    TS
    result = parse(source)
    joined = result.error_strings.join("\n")
    assert result.errors.any?, 'expected fail-closed error for @embedAlways'
    assert_includes joined, '@embedAlways'
    assert_includes joined, '#109'
  end

  def test_non_directive_identifier_does_not_trip_guard
    # A field named `sighashType` must NOT trip the word-boundary guard.
    source = <<~TS
      class Counter extends SmartContract {
        readonly sighashType: bigint;
        constructor(sighashType: bigint) { super(sighashType); this.sighashType = sighashType; }
        public unlock() {}
      }
    TS
    result = parse(source)
    refute(result.error_strings.any? { |m| m.include?('not yet supported') },
           "directive guard tripped on a non-directive identifier: #{result.error_strings}")
  end
end
