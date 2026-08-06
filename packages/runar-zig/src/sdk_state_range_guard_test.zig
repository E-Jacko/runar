//! A bigint state value whose MAGNITUDE does not fit the fixed 8-byte
//! little-endian sign-magnitude word must be REFUSED, not silently truncated.
//!
//! `num2bin-le8` gives a bigint state field exactly 63 bits of magnitude
//! (bytes 0..6 plus the low 7 bits of byte 7) and one sign bit (0x80 of byte
//! 7). `encodeBigNum2Bin` wrote the low 8 bytes and dropped everything above,
//! then OR-ed the sign bit in on top of whatever landed there. Measured in the
//! TS reference before the guard:
//!
//!     value       bytes written       reads back as
//!     2^63        0000000000000080    0    (negative zero)
//!     2^63 + 5    0500000000000080    -5   (SIGN FLIP)
//!     2^64        0000000000000000    0
//!
//! The deploy then succeeded and the UTXO was unspendable: the covenant
//! rebuilds the continuation with the compiler's own OP_NUM2BIN 8, which
//! cannot produce those bytes from that number, so hash256(outputs) never
//! matches.
//!
//! The Zig tier carries a SECOND defect on the `i64` path: `encodeNum2Bin`
//! computed `@intCast(-n)`, which is an illegal negation for `i64` minInt and
//! PANICS instead of returning an error. -2^63 is exactly the value whose
//! magnitude (2^63) is one past the word, so the range guard is what makes
//! that path total.
//!
//! Expected bytes below are derived BY HAND from the sign-magnitude rule,
//! never read off the serializer.

const std = @import("std");
const types = @import("sdk_types.zig");
const state_mod = @import("sdk_state.zig");

/// 2^63 — one past the largest magnitude the 63 magnitude bits can hold.
const TWO_63 = "9223372036854775808";
/// 2^63 - 1 — the largest magnitude that DOES fit.
const MAX_MAGNITUDE: i64 = 9223372036854775807;

const COUNT_FIELD = [_]types.StateField{
    .{ .name = "count", .type_name = "bigint", .index = 0 },
};

/// Serialize a single bigint state field and return the owned hex.
fn encodeOne(allocator: std.mem.Allocator, value: types.StateValue) ![]u8 {
    const values = [_]types.StateValue{value};
    return state_mod.serializeState(allocator, &COUNT_FIELD, &values);
}

fn expectRefused(value: types.StateValue) !void {
    const allocator = std.testing.allocator;
    try std.testing.expectError(error.StateValueOutOfRange, encodeOne(allocator, value));
}

fn expectBytes(value: types.StateValue, want: []const u8) !void {
    const allocator = std.testing.allocator;
    const got = try encodeOne(allocator, value);
    defer allocator.free(got);
    try std.testing.expectEqualStrings(want, got);
}

// ---------------------------------------------------------------------------
// Rejecting
// ---------------------------------------------------------------------------

test "state range guard: rejects exactly 2^63" {
    try expectRefused(.{ .big_int = TWO_63 });
}

test "state range guard: rejects exactly -(2^63) as a big_int" {
    try expectRefused(.{ .big_int = "-9223372036854775808" });
}

// -2^63 IS a valid i64, but its MAGNITUDE is 2^63 — one past the 63 magnitude
// bits. This is the input that used to PANIC in `@intCast(-n)`.
test "state range guard: rejects i64 minInt without panicking" {
    try expectRefused(.{ .int = std.math.minInt(i64) });
}

// The sign-flip case: used to write 0500000000000080, read back as -5.
test "state range guard: rejects 2^63 + 5" {
    try expectRefused(.{ .big_int = "9223372036854775813" });
}

test "state range guard: rejects 2^64" {
    try expectRefused(.{ .big_int = "18446744073709551616" });
}

test "state range guard: rejects 2^70, both signs" {
    try expectRefused(.{ .big_int = "1180591620717411303424" });
    try expectRefused(.{ .big_int = "-1180591620717411303424" });
}

// ---------------------------------------------------------------------------
// Accepting controls — byte-exact, and they must stay byte-exact
// ---------------------------------------------------------------------------

test "state range guard: accepts 2^63 - 1 and writes ffffffffffffff7f" {
    // magnitude bytes 0..6 all 0xff, byte 7 = 0x7f (all seven magnitude bits
    // set, sign bit clear).
    try expectBytes(.{ .int = MAX_MAGNITUDE }, "ffffffffffffff7f");
    try expectBytes(.{ .big_int = "9223372036854775807" }, "ffffffffffffff7f");
}

test "state range guard: accepts -(2^63 - 1) and writes ffffffffffffffff" {
    // same magnitude, sign bit set: 0x7f | 0x80 = 0xff.
    try expectBytes(.{ .int = -MAX_MAGNITUDE }, "ffffffffffffffff");
    try expectBytes(.{ .big_int = "-9223372036854775807" }, "ffffffffffffffff");
}

test "state range guard: accepts the small values every shipped contract uses" {
    try expectBytes(.{ .int = 0 }, "0000000000000000");
    try expectBytes(.{ .int = 1 }, "0100000000000000");
    try expectBytes(.{ .int = -1 }, "0100000000000080");
    try expectBytes(.{ .int = 127 }, "7f00000000000000");
    try expectBytes(.{ .int = -127 }, "7f00000000000080");
    try expectBytes(.{ .int = 128 }, "8000000000000000");
    try expectBytes(.{ .int = -128 }, "8000000000000080");
    // Same seven values through the arbitrary-precision path.
    try expectBytes(.{ .big_int = "0" }, "0000000000000000");
    try expectBytes(.{ .big_int = "1" }, "0100000000000000");
    try expectBytes(.{ .big_int = "-1" }, "0100000000000080");
    try expectBytes(.{ .big_int = "127" }, "7f00000000000000");
    try expectBytes(.{ .big_int = "-127" }, "7f00000000000080");
    try expectBytes(.{ .big_int = "128" }, "8000000000000000");
    try expectBytes(.{ .big_int = "-128" }, "8000000000000080");
}
