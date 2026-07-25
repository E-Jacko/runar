//! Deep-review finding G1 (P1) — Zig SDK.
//!
//! A method that calls `this.addRawOutput(...)` produces a state-class output
//! which the compiler folds into the covenant continuation `hashOutputs` IN
//! SOURCE ORDER, interleaved with the `this.addOutput(...)` state continuation.
//! The SDK call path must emit the outputs in that same source order, or the
//! built transaction's outputs mismatch `hashOutputs` → input 0's auto-injected
//! state-check `OP_VERIFY` rejects and the funds are stranded.
//!
//! The shipped example `examples/zig/add-raw-output/RawOutputTest.runar.zig`'s
//! `sendToScript` emits, in SOURCE order:
//!
//!     self.addRawOutput(1000, scriptBytes);  // raw output FIRST
//!     self.count = self.count + 1;
//!     self.addOutput(0, self.count);          // state continuation SECOND (0 sats)
//!
//! so the on-chain output layout the covenant reconstructs is
//! `[raw(1000, scriptBytes)] [stateContinuation(0)] [change]`. Emitting only the
//! state continuation (the pre-fix behaviour, which dropped raw outputs on the
//! call path) mismatches `hashOutputs`.
//!
//! Zig has NO ScriptVM (see CLAUDE.md — no usable upstream BSV script
//! interpreter), so the strongest available proof is a deterministic
//! output-byte assertion: this test deploys + calls `sendToScript` via
//! `MockProvider` and asserts the built call tx's outputs are exactly, in order,
//! `[0] raw = (1000, scriptBytes)`, `[1] state continuation = (0, codePart +
//! OP_RETURN + serialized count)`, `[2] change`, and that the SDK tracks the
//! continuation UTXO at its REAL index (1, not 0) with its real 0-sats value.
//!
//! The embedded artifact (`fixtures/g1-raw-output-artifact.json`) is the real
//! output of `runar-zig --source RawOutputTest.runar.zig` (sourceMap stripped).

const std = @import("std");
const types = @import("sdk_types.zig");
const provider_mod = @import("sdk_provider.zig");
const signer_mod = @import("sdk_signer.zig");
const contract_mod = @import("sdk_contract.zig");

const RunarContract = contract_mod.RunarContract;
const ContractError = contract_mod.ContractError;

const ARTIFACT_JSON = @embedFile("fixtures/g1-raw-output-artifact.json");

const DEPLOYER_KEY = "00" ** 31 ++ "03";
const CALLER_KEY = "00" ** 31 ++ "04";

// The caller-supplied raw locking script: a plain P2PKH (76a914 <20 bytes> 88ac).
const RAW_SCRIPT = "76a914" ++ "ab" ** 20 ++ "88ac";
// Funding UTXO locking script (arbitrary P2PKH — MockProvider never spends it).
const FUND_SCRIPT = "76a914" ++ "00" ** 20 ++ "88ac";

// ---------------------------------------------------------------------------
// Minimal raw-tx output parser (no ScriptVM available in this tier)
// ---------------------------------------------------------------------------

const ParsedOutput = struct {
    satoshis: i64,
    /// Locking-script hex; borrows from the parsed tx hex (kept alive by caller).
    script: []const u8,
};

/// Read one byte (2 hex chars) at byte offset `byte_off`.
fn hexByteAt(tx_hex: []const u8, byte_off: usize) u8 {
    return std.fmt.parseInt(u8, tx_hex[byte_off * 2 .. byte_off * 2 + 2], 16) catch 0;
}

/// Read a Bitcoin varint at `*cur` (byte cursor), advancing it past the varint.
fn readVarInt(tx_hex: []const u8, cur: *usize) u64 {
    const first = hexByteAt(tx_hex, cur.*);
    cur.* += 1;
    if (first < 0xfd) return first;
    const n: usize = if (first == 0xfd) 2 else if (first == 0xfe) 4 else 8;
    var val: u64 = 0;
    var b: usize = 0;
    while (b < n) : (b += 1) {
        val |= @as(u64, hexByteAt(tx_hex, cur.*)) << @as(u6, @intCast(8 * b));
        cur.* += 1;
    }
    return val;
}

/// Parse the outputs of a serialized (hex) legacy Bitcoin transaction. Returns
/// a caller-owned slice; each entry's `script` borrows from `tx_hex`.
fn parseOutputs(allocator: std.mem.Allocator, tx_hex: []const u8) ![]ParsedOutput {
    var cur: usize = 0; // byte cursor
    cur += 4; // version
    const in_count = readVarInt(tx_hex, &cur);
    var k: u64 = 0;
    while (k < in_count) : (k += 1) {
        cur += 32; // prev txid
        cur += 4; // prev vout
        const slen: usize = @intCast(readVarInt(tx_hex, &cur));
        cur += slen; // scriptSig
        cur += 4; // sequence
    }
    const out_count: usize = @intCast(readVarInt(tx_hex, &cur));
    const outs = try allocator.alloc(ParsedOutput, out_count);
    var j: usize = 0;
    while (j < out_count) : (j += 1) {
        var val: u64 = 0;
        var b: usize = 0;
        while (b < 8) : (b += 1) {
            val |= @as(u64, hexByteAt(tx_hex, cur + b)) << @as(u6, @intCast(8 * b));
        }
        cur += 8; // value (LE u64)
        const slen: usize = @intCast(readVarInt(tx_hex, &cur));
        outs[j] = .{
            .satoshis = @intCast(val),
            .script = tx_hex[cur * 2 .. (cur + slen) * 2],
        };
        cur += slen;
    }
    return outs;
}

// ---------------------------------------------------------------------------
// The G1 spend test
// ---------------------------------------------------------------------------

test "G1 (P1): sendToScript builds [raw(1000)][state(0)][change] in source order" {
    const allocator = std.testing.allocator;

    var artifact = try types.RunarArtifact.fromJson(allocator, ARTIFACT_JSON);
    defer artifact.deinit();

    var prov = provider_mod.MockProvider.init(allocator, "testnet");
    defer prov.deinit();

    var deployer = try signer_mod.LocalSigner.fromHex(DEPLOYER_KEY);
    var caller = try signer_mod.LocalSigner.fromHex(CALLER_KEY);

    // Fund the deployer (pays for deploy) and caller (change recipient) addresses.
    {
        const dep_addr = try deployer.signer().getAddress(allocator);
        defer allocator.free(dep_addr);
        try prov.addUtxo(dep_addr, .{ .txid = "aa" ** 32, .output_index = 0, .satoshis = 500_000, .script = FUND_SCRIPT });
        const call_addr = try caller.signer().getAddress(allocator);
        defer allocator.free(call_addr);
        try prov.addUtxo(call_addr, .{ .txid = "bb" ** 32, .output_index = 0, .satoshis = 500_000, .script = FUND_SCRIPT });
    }

    const ctor = [_]types.StateValue{.{ .int = 0 }};
    var contract = try RunarContract.init(allocator, &artifact, &ctor);
    defer contract.deinit();

    const deploy_txid = try contract.deploy(prov.provider(), deployer.signer(), .{ .satoshis = 50_000 });
    defer allocator.free(deploy_txid);

    const args = [_]types.StateValue{.{ .bytes = RAW_SCRIPT }};
    const call_txid = try contract.call("sendToScript", &args, prov.provider(), caller.signer(), null);
    defer allocator.free(call_txid);

    // State advanced 0 -> 1 (self.count = self.count + 1).
    try std.testing.expectEqual(@as(i64, 1), contract.state[0].int);

    // The call tx is the 2nd broadcast (deploy is the 1st).
    const txs = prov.getBroadcastedTxs();
    try std.testing.expectEqual(@as(usize, 2), txs.len);
    const call_tx = txs[1];

    const outs = try parseOutputs(allocator, call_tx);
    defer allocator.free(outs);

    // Three outputs in source order: raw, state continuation, change.
    try std.testing.expectEqual(@as(usize, 3), outs.len);

    // [0] raw output: 1000 sats, script == the caller-supplied bytes.
    try std.testing.expectEqual(@as(i64, 1000), outs[0].satoshis);
    try std.testing.expectEqualStrings(RAW_SCRIPT, outs[0].script);

    // [1] state continuation: 0 sats, codePart + OP_RETURN (6a) + serialized count.
    try std.testing.expectEqual(@as(i64, 0), outs[1].satoshis);
    try std.testing.expect(!std.mem.eql(u8, outs[1].script, RAW_SCRIPT));
    try std.testing.expect(std.mem.indexOf(u8, outs[1].script, "6a") != null);

    // The SDK tracks the continuation at its REAL index (1) and real 0-sats value.
    const cu = contract.getCurrentUtxo().?;
    try std.testing.expectEqual(@as(i32, 1), cu.output_index);
    try std.testing.expectEqual(@as(i64, 0), cu.satoshis);
    try std.testing.expectEqualStrings(outs[1].script, cu.script);

    // [2] change: a P2PKH output (76a9…88ac) carrying the remainder.
    try std.testing.expect(std.mem.startsWith(u8, outs[2].script, "76a914"));
    try std.testing.expect(std.mem.endsWith(u8, outs[2].script, "88ac"));
    try std.testing.expect(outs[2].satoshis > 0);
}
