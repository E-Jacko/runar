# frozen_string_literal: true

# Audit C2 -- `readonly` property assignment must be rejected outside the
# constructor.
#
#   spec/semantics.md:247
#     <this.p = e, env, sigma> ==> ERROR: cannot assign to readonly property
#
# Without the rule a contract that reassigns its readonly owner before checking
# it compiles to `76a97ca9788777` -- hash160(pk) compared against hash160(pk),
# true for ANY pubkey, i.e. anyone can spend.
#
# The constructor MUST still be allowed to assign readonly properties.
#
# Mirrors packages/runar-compiler/src/__tests__/readonly-property-assignment.test.ts

require_relative "test_helper"

require "runar_compiler/frontend/ast_nodes"
require "runar_compiler/frontend/diagnostic"
require "runar_compiler/frontend/validator"
require "runar_compiler/frontend/parser_ts"

class TestReadonlyPropertyAssignment < Minitest::Test
  include RunarCompiler::Frontend

  # The cross-tier diagnostic substring.
  READONLY_WRITE = "assign to readonly property"

  def validate_source(source, file_name = "Test.runar.ts")
    result = RunarCompiler.send(:_parse_source, source, file_name)
    assert_empty result.errors.map(&:format_message), "unexpected parse errors"
    refute_nil result.contract, "expected a contract from parsing"
    RunarCompiler::Frontend.validate(result.contract)
  end

  def assert_readonly_write_error(result)
    assert result.errors.any? { |e| e.message.include?(READONLY_WRITE) },
           "expected a readonly-write error, got: #{result.error_strings}"
  end

  def test_rejects_owner_hijack_contract
    source = <<~TS
      import { SmartContract, Addr, PubKey } from 'runar-lang';

      class Hijack extends SmartContract {
        readonly ownerHash: Addr;

        constructor(ownerHash: Addr) {
          super(ownerHash);
          this.ownerHash = ownerHash;
        }

        public unlock(attackerPk: PubKey) {
          this.ownerHash = hash160(attackerPk);
          assert(hash160(attackerPk) === this.ownerHash);
        }
      }
    TS
    result = validate_source(source)
    assert_readonly_write_error(result)
    assert result.errors.any? { |e| e.message.include?("'ownerHash'") },
           "expected the offending property name, got: #{result.error_strings}"
  end

  def test_rejects_readonly_write_in_stateful_method
    source = <<~TS
      import { StatefulSmartContract, Addr } from 'runar-lang';

      class Vault extends StatefulSmartContract {
        readonly owner: Addr;
        count: bigint;

        constructor(owner: Addr, count: bigint) {
          super(owner, count);
          this.owner = owner;
          this.count = count;
        }

        public bump(newOwner: Addr) {
          this.owner = newOwner;
          this.count = this.count + 1n;
        }
      }
    TS
    assert_readonly_write_error(validate_source(source))
  end

  def test_rejects_readonly_write_nested_in_if
    source = <<~TS
      import { StatefulSmartContract, Addr } from 'runar-lang';

      class Nested extends StatefulSmartContract {
        readonly owner: Addr;
        count: bigint;

        constructor(owner: Addr, count: bigint) {
          super(owner, count);
          this.owner = owner;
          this.count = count;
        }

        public bump(newOwner: Addr, flag: boolean) {
          if (flag) {
            this.owner = newOwner;
          } else {
            this.count = this.count + 1n;
          }
        }
      }
    TS
    assert_readonly_write_error(validate_source(source))
  end

  def test_rejects_readonly_write_in_private_helper
    source = <<~TS
      import { StatefulSmartContract, Addr } from 'runar-lang';

      class Helper extends StatefulSmartContract {
        readonly owner: Addr;
        count: bigint;

        constructor(owner: Addr, count: bigint) {
          super(owner, count);
          this.owner = owner;
          this.count = count;
        }

        private steal(newOwner: Addr): void {
          this.owner = newOwner;
        }

        public bump(newOwner: Addr) {
          this.steal(newOwner);
          this.count = this.count + 1n;
        }
      }
    TS
    assert_readonly_write_error(validate_source(source))
  end

  def test_rejects_increment_of_readonly_property
    source = <<~TS
      import { StatefulSmartContract } from 'runar-lang';

      class Bump extends StatefulSmartContract {
        readonly limit: bigint;
        count: bigint;

        constructor(limit: bigint, count: bigint) {
          super(limit, count);
          this.limit = limit;
          this.count = count;
        }

        public go() {
          this.limit++;
          this.count = this.count + 1n;
        }
      }
    TS
    assert_readonly_write_error(validate_source(source))
  end

  # ---------------------------------------------------------------------------
  # The constructor must keep working -- every contract assigns its readonly
  # properties there.
  # ---------------------------------------------------------------------------

  def test_accepts_readonly_assignment_in_constructor
    source = <<~TS
      import { SmartContract, Addr, PubKey, Sig } from 'runar-lang';

      class P2PKH extends SmartContract {
        readonly pubKeyHash: Addr;

        constructor(pubKeyHash: Addr) {
          super(pubKeyHash);
          this.pubKeyHash = pubKeyHash;
        }

        public unlock(sig: Sig, pubKey: PubKey) {
          assert(hash160(pubKey) === this.pubKeyHash);
          assert(checkSig(sig, pubKey));
        }
      }
    TS
    result = validate_source(source)
    assert_empty result.error_strings
  end

  def test_accepts_mutable_state_mutation
    source = <<~TS
      import { StatefulSmartContract, Addr } from 'runar-lang';

      class Counter extends StatefulSmartContract {
        readonly owner: Addr;
        count: bigint;

        constructor(owner: Addr, count: bigint) {
          super(owner, count);
          this.owner = owner;
          this.count = count;
        }

        public increment() {
          this.count = this.count + 1n;
        }
      }
    TS
    result = validate_source(source)
    assert_empty result.error_strings
  end

  def test_accepts_local_shadowing_a_readonly_property_name
    source = <<~TS
      import { StatefulSmartContract } from 'runar-lang';

      class Shadow extends StatefulSmartContract {
        readonly limit: bigint;
        count: bigint;

        constructor(limit: bigint, count: bigint) {
          super(limit, count);
          this.limit = limit;
          this.count = count;
        }

        public increment() {
          let limit: bigint = 5n;
          limit = 6n;
          assert(this.count < limit);
          this.count = this.count + 1n;
        }
      }
    TS
    result = validate_source(source)
    assert_empty result.error_strings
  end
end
