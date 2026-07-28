//! SDK continuation-satoshis fix (P1 funds-safety) — Zig SDK.
//!
//! On the stateful CALL path the SDK builds the state-continuation output at the
//! SPENT INPUT's satoshis, ignoring an explicit `this.addOutput(<N>, ...)` amount
//! that the ANF interpreter already records. A stateful method whose continuation
//! is `this.addOutput(1000, this.count)` therefore builds a continuation at the
//! deploy value (here 1 sat), not 1000 — the covenant's `hashOutputs` binding
//! then rejects the spend and the funds are stranded.
//!
//! Finding G1 (already fixed) reads the ANF-recorded satoshis but ONLY on the
//! raw-output-PRESENT branch. This test pins the generalization to the no-raw
//! single-continuation path: when the ANF interpreter's ordered outputs are
//! EXACTLY ONE entry of kind `state` (a single `addOutput`, no raw), the SDK must
//! use its recorded satoshis for the continuation amount (an explicit
//! `options.satoshis` still wins; a method with no `addOutput` keeps the
//! input-value default). Mirrors `packages/runar-sdk/src/__tests__/
//! continuation-satoshis.test.ts`.
//!
//! Zig has NO ScriptVM (see CLAUDE.md), so the strongest available proof is a
//! deterministic output-byte assertion: deploy `SatCounter` at 1 sat, call
//! `inc()` WITHOUT any satoshis option, and assert the built call tx's
//! continuation output (index 0) carries 1000 sats — not the 1-sat input value.
//!
//! The embedded artifact (`fixtures/satcounter-artifact.json`) is the real output
//! of `runar-zig --source SatCounter.runar.zig` (sourceMap + sourceLoc stripped),
//! whose `inc` body is `self.count = self.count + 1; self.addOutput(1000, self.count)`.

const std = @import("std");
const types = @import("sdk_types.zig");
const provider_mod = @import("sdk_provider.zig");
const signer_mod = @import("sdk_signer.zig");
const contract_mod = @import("sdk_contract.zig");

const RunarContract = contract_mod.RunarContract;

const ARTIFACT_JSON = @embedFile("fixtures/satcounter-artifact.json");

const DEPLOYER_KEY = "00" ** 31 ++ "05";
const CALLER_KEY = "00" ** 31 ++ "06";

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

fn hexByteAt(tx_hex: []const u8, byte_off: usize) u8 {
    return std.fmt.parseInt(u8, tx_hex[byte_off * 2 .. byte_off * 2 + 2], 16) catch 0;
}

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
// The continuation-satoshis test
// ---------------------------------------------------------------------------

test "continuation-satoshis (P1): inc() builds a 1000-sat continuation from addOutput, not the 1-sat input" {
    const allocator = std.testing.allocator;

    var artifact = try types.RunarArtifact.fromJson(allocator, ARTIFACT_JSON);
    defer artifact.deinit();

    var prov = provider_mod.MockProvider.init(allocator, "testnet");
    defer prov.deinit();

    var deployer = try signer_mod.LocalSigner.fromHex(DEPLOYER_KEY);
    var caller = try signer_mod.LocalSigner.fromHex(CALLER_KEY);

    // Fund the deployer (pays for deploy) and caller (funds the call + change).
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

    // Deploy at the default 1 sat — the pre-fix continuation would inherit THIS
    // value (1), not the addOutput amount (1000).
    const deploy_txid = try contract.deploy(prov.provider(), deployer.signer(), .{ .satoshis = 1 });
    defer allocator.free(deploy_txid);

    // Call inc() WITHOUT any satoshis option (options = null). inc has no user
    // params, so args is empty.
    const args = [_]types.StateValue{};
    const call_txid = try contract.call("inc", &args, prov.provider(), caller.signer(), null);
    defer allocator.free(call_txid);

    // Sanity: state advanced 0 -> 1 (self.count = self.count + 1).
    try std.testing.expectEqual(@as(i64, 1), contract.state[0].int);

    // The call tx is the 2nd broadcast (deploy is the 1st).
    const txs = prov.getBroadcastedTxs();
    try std.testing.expectEqual(@as(usize, 2), txs.len);
    const call_tx = txs[1];

    const outs = try parseOutputs(allocator, call_tx);
    defer allocator.free(outs);

    // Two outputs: [0] state continuation, [1] change.
    try std.testing.expectEqual(@as(usize, 2), outs.len);

    // [0] continuation MUST carry the addOutput(1000, ...) amount — NOT the
    // 1-sat spent-input value the pre-fix single-continuation path defaulted to.
    try std.testing.expectEqual(@as(i64, 1000), outs[0].satoshis);
    // It is the contract's own continuation script (codePart + OP_RETURN + state),
    // not a P2PKH change output.
    try std.testing.expect(std.mem.indexOf(u8, outs[0].script, "6a") != null);

    // The SDK tracks the continuation UTXO at its real 1000-sat value.
    const cu = contract.getCurrentUtxo().?;
    try std.testing.expectEqual(@as(i64, 1000), cu.satoshis);

    // [1] change: a P2PKH output carrying the remainder.
    try std.testing.expect(std.mem.startsWith(u8, outs[1].script, "76a914"));
    try std.testing.expect(std.mem.endsWith(u8, outs[1].script, "88ac"));
}
