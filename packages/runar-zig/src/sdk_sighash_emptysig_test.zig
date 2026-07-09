//! Issue #123 (@sighash SDK threading) + #106 (EmptySig marker) — Zig SDK.

const std = @import("std");
const types = @import("sdk_types.zig");
const state_mod = @import("sdk_state.zig");
const oppushtx = @import("sdk_oppushtx.zig");

// ---------------------------------------------------------------------------
// #106 EmptySig — the deliberately-failing branch of an OR-CHECKSIG method must
// push an empty signature (OP_0) or BIP146 NULLFAIL rejects the spend. EMPTY_SIG
// is the producer-side sentinel: encodeArg emits OP_0 for it, and it is NOT
// `.int = 0` (the auto-sign sentinel) so the auto-sign collectors never sign it.
// Wire-byte parity with the TS SDK (contract.ts encodeArg emits "00").
// ---------------------------------------------------------------------------

test "EmptySig: encodeArg emits OP_0 (00)" {
    const a = std.testing.allocator;
    const enc = try state_mod.encodeArg(a, types.EMPTY_SIG);
    defer a.free(enc);
    try std.testing.expectEqualStrings("00", enc);
}

test "EmptySig: distinct from the .int=0 auto-sign sentinel" {
    // The auto-sign collectors trigger on `arg == .int and arg.int == 0`.
    // EMPTY_SIG is the `.empty_sig` tag, so those collectors skip it (never
    // signed) — it stays in the resolved args and encodes as OP_0.
    try std.testing.expect(types.EMPTY_SIG != .int);
    try std.testing.expect(std.meta.activeTag(types.EMPTY_SIG) == .empty_sig);
    // An explicit .int=0 (auto-sign) encodes as OP_0 too, but via a different
    // path — the point is the tags differ so the collector distinguishes them.
    const auto_sign = types.StateValue{ .int = 0 };
    try std.testing.expect(std.meta.activeTag(auto_sign) != std.meta.activeTag(types.EMPTY_SIG));
}

test "EmptySig: clone is identity and deinit is a no-op" {
    const a = std.testing.allocator;
    const c = try types.EMPTY_SIG.clone(a);
    try std.testing.expect(std.meta.activeTag(c) == .empty_sig);
    c.deinit(a); // must not crash / free anything
}

// OR-CHECKSIG [realSig, EmptySig] — the failing branch encodes OP_0 while the
// matching branch keeps its real signature push. Mirrors the TS wire output:
// a 72-byte sig direct-pushes as 0x48 <sig>, then OP_0 (00) for the EmptySig.
test "EmptySig: OR-CHECKSIG wire bytes [realSig, EmptySig] == <push sig> || 00" {
    const a = std.testing.allocator;
    const sig_hex = "aa" ** 72; // 72-byte placeholder signature
    const sig_push = try state_mod.encodeArg(a, .{ .bytes = sig_hex });
    defer a.free(sig_push);
    const empty_push = try state_mod.encodeArg(a, types.EMPTY_SIG);
    defer a.free(empty_push);

    // 72 bytes = 0x48 direct push, then OP_0 for the empty slot.
    const expected_sig = "48" ++ ("aa" ** 72);
    try std.testing.expectEqualStrings(expected_sig, sig_push);
    try std.testing.expectEqualStrings("00", empty_push);
}

// ---------------------------------------------------------------------------
// #123 SDK sighash threading — computeOpPushTxWithSigHash builds the BIP-143
// preimage + derives the DER sig under a caller-supplied mode. bsvz zeroes the
// right fields (hashPrevouts under ANYONECANPAY, hashSequence unless pure ALL,
// hashOutputs under NONE / same-index SINGLE) natively once the flag is passed.
// ---------------------------------------------------------------------------

const test_tx_hex = "01000000" ++ "01" ++
    "1111111111111111111111111111111111111111111111111111111111111111" ++
    "00000000" ++ "00" ++ "ffffffff" ++
    "01" ++ "e803000000000000" ++ "01" ++ "51" ++ "00000000";
const test_subscript = "76a914" ++ "0000000000000000000000000000000000000000" ++ "88ac";

fn sigTrailingByte(sig_hex: []const u8) u8 {
    // DER sig hex ends with the appended sighash flag byte (2 hex chars).
    return std.fmt.parseInt(u8, sig_hex[sig_hex.len - 2 ..], 16) catch 0;
}

fn preimageSigHashByte(preimage_hex: []const u8) u8 {
    // BIP-143 preimage ends with nLocktime(4) || sighashType(4) LE. The flag is
    // the first byte of the trailing sighashType uint32 = hex chars [-8..-6].
    return std.fmt.parseInt(u8, preimage_hex[preimage_hex.len - 8 .. preimage_hex.len - 6], 16) catch 0;
}

test "SDK sighash: default (0x41) == unparameterised computeOpPushTx" {
    const a = std.testing.allocator;
    var d = try oppushtx.computeOpPushTx(a, test_tx_hex, 0, test_subscript, 1000, -1);
    defer d.deinit(a);
    var v = try oppushtx.computeOpPushTxWithSigHash(a, test_tx_hex, 0, test_subscript, 1000, -1, 0x41);
    defer v.deinit(a);
    try std.testing.expectEqualStrings(d.sig_hex, v.sig_hex);
    try std.testing.expectEqualStrings(d.preimage_hex, v.preimage_hex);
    try std.testing.expectEqual(@as(u8, 0x41), sigTrailingByte(d.sig_hex));
    try std.testing.expectEqual(@as(u8, 0x41), preimageSigHashByte(d.preimage_hex));
}

test "SDK sighash: SINGLE(0x43) and ANYONECANPAY(0xC1) carry the flag + diverge from default" {
    const a = std.testing.allocator;
    var base = try oppushtx.computeOpPushTxWithSigHash(a, test_tx_hex, 0, test_subscript, 1000, -1, 0x41);
    defer base.deinit(a);

    inline for (.{ 0x43, 0xc1 }) |flag| {
        var r = try oppushtx.computeOpPushTxWithSigHash(a, test_tx_hex, 0, test_subscript, 1000, -1, flag);
        defer r.deinit(a);
        try std.testing.expectEqual(@as(u8, flag), sigTrailingByte(r.sig_hex));
        try std.testing.expectEqual(@as(u8, flag), preimageSigHashByte(r.preimage_hex));
        // The preimage must differ from ALL|FORKID (zeroed BIP-143 fields).
        try std.testing.expect(!std.mem.eql(u8, r.preimage_hex, base.preimage_hex));
    }
}

test "SDK sighash: ABIMethod parses sigHashType from the artifact JSON" {
    const a = std.testing.allocator;
    // A non-default @sighash method carries "sigHashType" in the ABI; a plain
    // method omits it (SDK falls back to 0x41). Verify fromJsonValue reads it.
    const parsed = try std.json.parseFromSlice(std.json.Value, a,
        \\{"name":"bump","isPublic":true,"sigHashType":67,"params":[]}
    , .{});
    defer parsed.deinit();
    var m = try types.ABIMethod.fromJsonValue(a, parsed.value.object);
    defer m.deinit(a);
    try std.testing.expect(m.sig_hash_type != null);
    try std.testing.expectEqual(@as(i64, 67), m.sig_hash_type.?);

    const parsed2 = try std.json.parseFromSlice(std.json.Value, a,
        \\{"name":"plain","isPublic":true,"params":[]}
    , .{});
    defer parsed2.deinit();
    var m2 = try types.ABIMethod.fromJsonValue(a, parsed2.value.object);
    defer m2.deinit(a);
    try std.testing.expect(m2.sig_hash_type == null);
}
