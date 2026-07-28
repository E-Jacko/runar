//! C9 + S1 — single-byte MINIMALDATA push data must round-trip (Zig SDK).
//!
//! C9 (state): `serializeState` routes a variable-length (ByteString) field
//! through `encodePushData`, which short-circuits single-byte payloads to
//! OP_0 / OP_1..OP_16 / OP_1NEGATE. `decodePushData` only understood direct
//! pushes (`opcode <= 75`) and OP_PUSHDATA1/2/4, so every one of those minimal
//! opcodes decoded as a zero-length push ("") — state restored from chain came
//! back EMPTY instead of the real byte.
//!
//! S1 (ctor): the same encoder backs `encodeArg` (constructor-arg splicing +
//! unlocking-script args), and `interpretScriptElement`'s default (non-numeric)
//! branch just forwarded `data_hex`, which `readScriptElement` leaves empty for
//! OP_N / OP_1NEGATE (they carry no separate data bytes — the opcode IS the
//! value). A 1-byte ByteString ctor arg restored as "".
//!
//! The 0x00 case is a distinct bug in the ENCODER: OP_0 pushes the EMPTY byte
//! array, not a 1-byte 0x00. The minimal encoding of a 1-byte 0x00 payload is
//! the direct push "01 00" — exactly what the compiler's `encodePushBytesHex`
//! (packages/runar-compiler/src/passes/push-encoding.ts) emits. Encoding it as
//! OP_0 changes the value.
//!
//! Mirrors the TypeScript reference fix in
//! packages/runar-sdk/src/{state,contract,script-utils}.ts.

const std = @import("std");
const types = @import("sdk_types.zig");
const state_mod = @import("sdk_state.zig");
const script_utils = @import("sdk_script_utils.zig");
const contract_mod = @import("sdk_contract.zig");

/// Payload set: the three MINIMALDATA short-circuit families (0x00 boundary,
/// OP_1..OP_16 low/mid/high, OP_1NEGATE).
const MINIMALDATA_PAYLOADS = [_][]const u8{ "00", "01", "05", "10", "81" };
/// ...plus a multi-byte and an empty control (state path only — a ctor slot
/// never carries an empty ByteString in practice).
const STATE_PAYLOADS = MINIMALDATA_PAYLOADS ++ [_][]const u8{ "aabbccdd", "" };
const CTOR_PAYLOADS = MINIMALDATA_PAYLOADS ++ [_][]const u8{"aabbccdd"};

// ---------------------------------------------------------------------------
// C9 — state serializer round-trip
// ---------------------------------------------------------------------------

test "C9: variable-length ByteString state field round-trips every MINIMALDATA payload" {
    const allocator = std.testing.allocator;

    const fields = [_]types.StateField{
        .{ .name = "b", .type_name = "ByteString", .index = 0 },
    };

    // Report EVERY mismatching payload rather than aborting on the first, so a
    // regression names the whole affected set.
    var mismatches: usize = 0;

    for (STATE_PAYLOADS) |payload| {
        const values = [_]types.StateValue{.{ .bytes = payload }};

        const encoded = try state_mod.serializeState(allocator, &fields, &values);
        defer allocator.free(encoded);

        const decoded = try state_mod.deserializeState(allocator, &fields, encoded);
        defer {
            for (decoded) |*v| v.deinit(allocator);
            allocator.free(decoded);
        }

        try std.testing.expect(decoded[0] == .bytes);
        if (!std.mem.eql(u8, payload, decoded[0].bytes)) {
            mismatches += 1;
            std.debug.print(
                "C9 state round-trip: payload \"{s}\" encoded \"{s}\" -> expected \"{s}\", got \"{s}\"\n",
                .{ payload, encoded, payload, decoded[0].bytes },
            );
        }
    }

    try std.testing.expectEqual(@as(usize, 0), mismatches);
}

// ---------------------------------------------------------------------------
// S1 — constructor-arg splice/restore round-trip
// ---------------------------------------------------------------------------

/// Template: OP_DUP <1-byte ctor slot placeholder> OP_SWAP.
const CTOR_ARTIFACT_JSON =
    \\{
    \\  "contractName": "CtorByteString",
    \\  "abi": { "constructor": { "params": [ { "name": "b", "type": "ByteString" } ] }, "methods": [] },
    \\  "script": "ab007c",
    \\  "stateFields": [],
    \\  "constructorSlots": [ { "paramIndex": 0, "byteOffset": 1 } ]
    \\}
;

test "S1: ByteString constructor arg round-trips every MINIMALDATA payload" {
    const allocator = std.testing.allocator;

    var mismatches: usize = 0;

    for (CTOR_PAYLOADS) |payload| {
        var artifact = try types.RunarArtifact.fromJson(allocator, CTOR_ARTIFACT_JSON);
        defer artifact.deinit();

        const args = [_]types.StateValue{.{ .bytes = payload }};
        var contract = try contract_mod.RunarContract.init(allocator, &artifact, &args);
        defer contract.deinit();

        const locking_script = try contract.getLockingScript();
        defer allocator.free(locking_script);

        var restored = try script_utils.extractConstructorArgs(&artifact, locking_script, allocator);
        defer {
            var it = restored.iterator();
            while (it.next()) |entry| {
                allocator.free(entry.key_ptr.*);
                entry.value_ptr.deinit(allocator);
            }
            restored.deinit();
        }

        const got = restored.get("b") orelse return error.MissingCtorArg;
        try std.testing.expect(got == .bytes);
        if (!std.mem.eql(u8, payload, got.bytes)) {
            mismatches += 1;
            std.debug.print(
                "S1 ctor round-trip: payload \"{s}\" script \"{s}\" -> expected \"{s}\", got \"{s}\"\n",
                .{ payload, locking_script, payload, got.bytes },
            );
        }
    }

    try std.testing.expectEqual(@as(usize, 0), mismatches);
}
