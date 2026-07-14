//! Regression test for MINIMALDATA-correct encoding of single-byte payloads
//! in `encode_push_data`.
//!
//! BSV consensus + relay policy (`SCRIPT_VERIFY_MINIMALDATA`) require that
//! a 1-byte data push whose payload is in `{0x00, 0x01..=0x10, 0x81}` MUST
//! use the corresponding minimal opcode (`OP_0` / `OP_1..OP_16` /
//! `OP_1NEGATE`) rather than the direct push `01 NN`. Non-minimal pushes
//! are rejected by ARC, TAAL ARC, and WhatsOnChain at the relay layer with:
//!   `non-mandatory-script-verify-flag (Data push larger than necessary)`
//!
//! Before the fix, `encode_push_data` always emitted the direct push form
//! for any payload of length 1, regardless of byte value. This worked for
//! the common case (ByteString args of length >= 2: sigs, pubkeys, hashes,
//! preimages, etc.) but tripped for any byte-string args that happened to
//! land on a single byte in the OP_N range — for example certain padding
//! patterns in Rabin signature schemes, or any user-supplied ByteString
//! that the consumer didn't pre-normalize.
//!
//! The encoder for `SdkValue::Int` (`encode_script_number`) already enforces
//! this rule; the fix brings `encode_push_data` for `SdkValue::Bytes` to
//! the same standard.

use runar_lang::sdk::state::encode_push_data;

#[test]
fn encode_push_data_minimaldata_op_0() {
    // Payload 0x00 (single zero byte) must encode as OP_0 (one byte: 0x00),
    // not direct push (two bytes: 0x01 0x00).
    assert_eq!(encode_push_data("00"), "00");
}

#[test]
fn encode_push_data_minimaldata_op_1_through_16() {
    // Payloads 0x01..=0x10 must encode as OP_1..OP_16 (opcodes 0x51..0x60).
    let cases: [(u8, &str); 16] = [
        (0x01, "51"), (0x02, "52"), (0x03, "53"), (0x04, "54"),
        (0x05, "55"), (0x06, "56"), (0x07, "57"), (0x08, "58"),
        (0x09, "59"), (0x0a, "5a"), (0x0b, "5b"), (0x0c, "5c"),
        (0x0d, "5d"), (0x0e, "5e"), (0x0f, "5f"), (0x10, "60"),
    ];
    for (byte, expected) in cases {
        let hex = format!("{:02x}", byte);
        let got = encode_push_data(&hex);
        assert_eq!(
            got, expected,
            "encode_push_data({:02x}) should emit {} (OP_{}), got {}",
            byte, expected, byte, got
        );
    }
}

#[test]
fn encode_push_data_minimaldata_op_1negate() {
    // Payload 0x81 (BSV's signed-magnitude representation of -1) must
    // encode as OP_1NEGATE (opcode 0x4f).
    assert_eq!(encode_push_data("81"), "4f");
}

#[test]
fn encode_push_data_single_byte_outside_op_n_range_still_direct_push() {
    // Bytes outside {0x00, 0x01..=0x10, 0x81} must still use the direct
    // push form (01 NN). This locks the regression boundary: the fix
    // should ONLY short-circuit the consensus-required cases.
    for byte in [0x11u8, 0x4f, 0x50, 0x60, 0x61, 0x80, 0x82, 0xff] {
        let hex = format!("{:02x}", byte);
        let expected = format!("01{:02x}", byte);
        let got = encode_push_data(&hex);
        assert_eq!(
            got, expected,
            "encode_push_data({:02x}) should emit direct push {}, got {}",
            byte, expected, got
        );
    }
}

#[test]
fn encode_push_data_multi_byte_unchanged() {
    // Payloads of length >= 2 are not affected by MINIMALDATA single-byte
    // rule. Encoding must match the pre-fix behaviour exactly.
    assert_eq!(encode_push_data("0001"), "020001");
    assert_eq!(encode_push_data("deadbeef"), "04deadbeef");
    // 75-byte payload: still direct push (max for direct push)
    let payload = "aa".repeat(75);
    let expected = format!("4b{}", payload);
    assert_eq!(encode_push_data(&payload), expected);
    // 76-byte payload: switches to OP_PUSHDATA1
    let payload = "bb".repeat(76);
    let expected = format!("4c4c{}", payload);
    assert_eq!(encode_push_data(&payload), expected);
}
