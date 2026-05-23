# frozen_string_literal: true

require_relative 'codegen_helper'
require 'runar_compiler/codegen/emit'

# Dedicated emit-pass test for the Ruby compiler (GAP-m4).
#
# Mirrors compilers/python/tests/test_emit.py and
# compilers/go/codegen/emit_test.go: pins the Stack-IR -> Bitcoin Script
# hex emission for a canonical fixture so an emit-pass regression fails
# locally instead of surfacing only as a conformance-suite divergence.
#
# The fixture is the in-tree P2PKH example — the same source the
# `basic-p2pkh` conformance fixture compiles. Its locking script is the
# canonical 5-opcode P2PKH template `OP_DUP OP_HASH160 <20-byte slot>
# OP_EQUALVERIFY OP_CHECKSIG`, whose constructor-arg-free skeleton is the
# byte-frozen golden `76a90088ac`.
class TestEmitPass < Minitest::Test
  include CodegenTestHelpers

  P2PKH_SOURCE = File.expand_path(
    '../../../../examples/ruby/p2pkh/P2PKH.runar.rb', __dir__
  )

  # Byte-frozen golden: the constructor-slot skeleton of the P2PKH locking
  # script. Matches conformance/tests/basic-p2pkh/expected-script.hex.
  P2PKH_GOLDEN_HEX = '76a90088ac'

  def test_emit_produces_byte_frozen_p2pkh_locking_script
    source = File.read(P2PKH_SOURCE)
    artifact = compile_ts_source(source, 'P2PKH.runar.rb')

    assert_equal 'P2PKH', artifact.contract_name
    assert_equal P2PKH_GOLDEN_HEX, artifact.script.downcase,
                 'emit pass must produce the byte-frozen P2PKH locking script'
  end

  def test_emit_p2pkh_asm_has_canonical_opcode_shape
    source = File.read(P2PKH_SOURCE)
    artifact = compile_ts_source(source, 'P2PKH.runar.rb')

    asm = artifact.asm
    # Canonical P2PKH spend path: OP_DUP OP_HASH160 <pkh> OP_EQUALVERIFY OP_CHECKSIG
    assert_includes asm, 'OP_DUP'
    assert_includes asm, 'OP_HASH160'
    assert_includes asm, 'OP_EQUALVERIFY'
    assert_includes asm, 'OP_CHECKSIG'
  end
end

# Byte-frozen unit tests for the emit pass's low-level encoding primitives.
#
# The feature-level codegen tests (test_blake3, test_ec, test_sha256, ...) and
# the conformance suite exercise these functions indirectly, but the encoding
# primitives themselves — script-number sign-magnitude encoding, MINIMALDATA
# push selection, and the OP_PUSHDATA{1,2,4} length-prefix boundaries — were
# only covered transitively. A regression in any of them (e.g. a wrong pad
# byte or a missed boundary) would surface only as a cross-tier conformance
# divergence rather than a local Ruby failure. These pin them directly, the
# same way compilers/go/codegen/emit_test.go and compilers/python/tests/
# test_emit.py do for their tiers.
class TestEmitEncoding < Minitest::Test
  C = RunarCompiler::Codegen

  def hex(bytes)
    C.bytes_to_hex(bytes)
  end

  # --- encode_script_number: Bitcoin CScriptNum (little-endian sign-magnitude)

  def test_script_number_zero_is_empty
    assert_equal '', hex(C.encode_script_number(0))
  end

  def test_script_number_positive_no_pad
    assert_equal '01', hex(C.encode_script_number(1))
    assert_equal '7f', hex(C.encode_script_number(127))
    assert_equal '10', hex(C.encode_script_number(16))
  end

  def test_script_number_positive_high_bit_gets_zero_pad
    # 0x80 / 0xff have the sign bit set, so a 0x00 pad byte is appended to
    # keep the value positive.
    assert_equal '8000', hex(C.encode_script_number(128))
    assert_equal 'ff00', hex(C.encode_script_number(255))
  end

  def test_script_number_multibyte
    assert_equal '0001', hex(C.encode_script_number(256))
    assert_equal 'e803', hex(C.encode_script_number(1000))
  end

  def test_script_number_negative_sets_sign_bit
    assert_equal '81', hex(C.encode_script_number(-1))
    assert_equal 'ff', hex(C.encode_script_number(-127))
    assert_equal '0081', hex(C.encode_script_number(-256))
  end

  def test_script_number_negative_high_bit_gets_sign_pad
    # When the top byte already has the high bit set, a 0x80 pad carries the
    # sign instead of OR-ing into the magnitude byte.
    assert_equal '8080', hex(C.encode_script_number(-128))
    assert_equal 'ff80', hex(C.encode_script_number(-255))
  end

  # --- encode_push_big_int: [hex, asm], small-int opcodes where possible

  def test_push_big_int_zero_uses_op0
    assert_equal %w[00 OP_0], C.encode_push_big_int(0)
  end

  def test_push_big_int_minus_one_uses_op1negate
    assert_equal %w[4f OP_1NEGATE], C.encode_push_big_int(-1)
  end

  def test_push_big_int_one_to_sixteen_use_opn
    assert_equal %w[51 OP_1], C.encode_push_big_int(1)
    assert_equal %w[60 OP_16], C.encode_push_big_int(16)
  end

  def test_push_big_int_seventeen_is_minimal_length_prefixed_push
    # 17 is out of the OP_N range, so it becomes a 1-byte length-prefixed push.
    assert_equal ['0111', '<11>'], C.encode_push_big_int(17)
  end

  def test_push_big_int_multibyte
    assert_equal ['028000', '<8000>'], C.encode_push_big_int(128)
    assert_equal ['02e803', '<e803>'], C.encode_push_big_int(1000)
    assert_equal ['02ff00', '<ff00>'], C.encode_push_big_int(255)
  end

  def test_push_big_int_negative_small
    assert_equal ['0182', '<82>'], C.encode_push_big_int(-2)
  end

  # --- encode_push_data: MINIMALDATA + OP_PUSHDATA{1,2,4} boundaries

  def test_push_data_empty_is_op0
    assert_equal '00', hex(C.encode_push_data(''.b))
  end

  def test_push_data_single_byte_1_to_16_uses_opn
    assert_equal '55', hex(C.encode_push_data([5].pack('C')))     # OP_5
    assert_equal '51', hex(C.encode_push_data([1].pack('C')))     # OP_1
    assert_equal '60', hex(C.encode_push_data([16].pack('C')))    # OP_16
  end

  def test_push_data_single_byte_0x81_is_op1negate
    assert_equal '4f', hex(C.encode_push_data([0x81].pack('C')))
  end

  def test_push_data_single_byte_zero_is_length_prefixed
    # 0x00 is NOT folded to OP_0 — OP_0 pushes [] not [0x00].
    assert_equal '0100', hex(C.encode_push_data([0].pack('C')))
    assert_equal '01ff', hex(C.encode_push_data([0xff].pack('C')))
  end

  def test_push_data_direct_push_max_75
    encoded = C.encode_push_data('a'.b * 75)
    assert_equal '4b', hex(encoded)[0, 2]   # 0x4b == 75, direct push length byte
    assert_equal 76, encoded.bytesize       # 1 length byte + 75 data
  end

  def test_push_data_pushdata1_boundary_76
    encoded = C.encode_push_data('a'.b * 76)
    assert_equal '4c4c', hex(encoded)[0, 4] # OP_PUSHDATA1 (0x4c) + length 0x4c (76)
    assert_equal 78, encoded.bytesize       # 1 opcode + 1 length + 76 data
  end

  def test_push_data_pushdata1_max_255
    encoded = C.encode_push_data('a'.b * 255)
    assert_equal '4cff', hex(encoded)[0, 4]
    assert_equal 257, encoded.bytesize
  end

  def test_push_data_pushdata2_boundary_256
    encoded = C.encode_push_data('a'.b * 256)
    assert_equal '4d0001', hex(encoded)[0, 6] # OP_PUSHDATA2 + 256 little-endian
    assert_equal 259, encoded.bytesize        # 1 opcode + 2 length + 256 data
  end

  def test_push_data_pushdata2_max_65535
    encoded = C.encode_push_data('a'.b * 65_535)
    assert_equal '4dffff', hex(encoded)[0, 6]
    assert_equal 65_538, encoded.bytesize
  end

  def test_push_data_pushdata4_boundary_65536
    encoded = C.encode_push_data('a'.b * 65_536)
    assert_equal '4e00000100', hex(encoded)[0, 10] # OP_PUSHDATA4 + 65536 little-endian
    assert_equal 65_541, encoded.bytesize          # 1 opcode + 4 length + 65536 data
  end

  # --- encode_push_value: bool / bytes / bigint dispatch

  def test_push_value_bool
    assert_equal %w[51 OP_TRUE], C.encode_push_value(kind: 'bool', bool_val: true)
    assert_equal %w[00 OP_FALSE], C.encode_push_value(kind: 'bool', bool_val: false)
  end

  def test_push_value_bytes
    assert_equal %w[00 OP_0], C.encode_push_value(kind: 'bytes', bytes_val: ''.b)
    assert_equal ['01ab', '<ab>'], C.encode_push_value(kind: 'bytes', bytes_val: [0xab].pack('C'))
  end

  def test_push_value_bigint_delegates
    assert_equal C.encode_push_big_int(42), C.encode_push_value(kind: 'bigint', big_int: 42)
  end

  # --- opcode_byte + hex helpers

  def test_opcode_byte_known
    assert_equal 0x76, C.opcode_byte('OP_DUP')
    assert_equal 0x00, C.opcode_byte('OP_0')
    assert_equal 0x60, C.opcode_byte('OP_16')
    assert_equal 0x4c, C.opcode_byte('OP_PUSHDATA1')
    assert_equal 0xac, C.opcode_byte('OP_CHECKSIG')
    assert_equal 0x88, C.opcode_byte('OP_EQUALVERIFY')
  end

  def test_opcode_byte_unknown_is_nil
    assert_nil C.opcode_byte('OP_NOT_A_REAL_OPCODE')
  end

  def test_bytes_hex_roundtrip
    assert_equal 'deadbeef', C.bytes_to_hex(C.hex_to_bytes('deadbeef'))
    assert_equal C.encode_push_bytes_hex([0xab].pack('C')), hex(C.encode_push_data([0xab].pack('C')))
  end
end
