//! G6 — the `.int = 0` "auto-resolve" sentinel must be gated on the well-known
//! `allPrevouts` param name at BOTH arg-resolution sites.
//!
//! Zig has no null: the auto-resolve sentinel for a call arg is `.int = 0`,
//! which for a ByteString param is ALSO a perfectly legitimate value (the empty
//! byte string, encoded as OP_0). The primary resolution site in
//! `sdk_contract.zig` therefore gates the 36*n-zero-byte prevouts stub on the
//! parameter being named `allPrevouts`, with a comment saying exactly that.
//!
//! The per-input site that resolves `options.additional_contract_input_args`
//! dropped the name gate, so `.int = 0` for ANY ByteString param of an
//! additional contract input became the prevouts stub instead of an empty
//! push — the contract's own parameter silently receives outpoint bytes and the
//! spend fails at script execution with an opaque error.
//!
//! Two sites are involved: the placeholder pass that sizes the per-input
//! unlocking scripts, and the final pass that substitutes the REAL
//! `extractAllPrevoutsHex(tx)` bytes into every `.int = 0` ByteString/Ripemd160
//! slot. It is the second one whose bytes reach the chain.
//!
//! Zig has NO ScriptVM (see CLAUDE.md), so the proof is a byte assertion on the
//! built call tx: a 3-input call has 3 * 36 = 108 prevouts bytes, which push as
//! OP_PUSHDATA1 108 (`4c6c`). No parameter of this contract legitimately holds
//! 108 bytes, so that push appearing at all means the prevouts landed in the
//! extra input's `scriptBytes` slot.
//!
//! The embedded artifact is the same `RawOutputTest` fixture the G1 test uses;
//! its `sendToScript(scriptBytes: ByteString, ...)` gives us a ByteString param
//! that is NOT named `allPrevouts`.

const std = @import("std");
const types = @import("sdk_types.zig");
const provider_mod = @import("sdk_provider.zig");
const signer_mod = @import("sdk_signer.zig");
const contract_mod = @import("sdk_contract.zig");

const RunarContract = contract_mod.RunarContract;

const ARTIFACT_JSON = @embedFile("fixtures/g1-raw-output-artifact.json");

const DEPLOYER_KEY = "00" ** 31 ++ "0b";
const CALLER_KEY = "00" ** 31 ++ "0c";

const RAW_SCRIPT = "76a914" ++ "ab" ** 20 ++ "88ac";
const FUND_SCRIPT = "76a914" ++ "00" ** 20 ++ "88ac";

/// OP_PUSHDATA1 with length 108 — the width of a 3-input `allPrevouts` blob.
const PREVOUTS_PUSH_PREFIX = "4c6c";

test "G6: `.int = 0` for a non-allPrevouts ByteString param is not stubbed on additional contract inputs" {
    const allocator = std.testing.allocator;

    var artifact = try types.RunarArtifact.fromJson(allocator, ARTIFACT_JSON);
    defer artifact.deinit();

    var prov = provider_mod.MockProvider.init(allocator, "testnet");
    defer prov.deinit();

    var deployer = try signer_mod.LocalSigner.fromHex(DEPLOYER_KEY);
    var caller = try signer_mod.LocalSigner.fromHex(CALLER_KEY);

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

    // A second contract UTXO sharing this contract's locking script.
    const contract_script = contract.getCurrentUtxo().?.script;
    const extra = [_]types.UTXO{.{
        .txid = "cc" ** 32,
        .output_index = 0,
        .satoshis = 5_000,
        .script = contract_script,
    }};
    // Per-input args: `.int = 0` for `scriptBytes` — a legitimate empty
    // ByteString, NOT a prevouts auto-resolve request.
    const per_input = [_][]const types.StateValue{&[_]types.StateValue{.{ .int = 0 }}};

    const args = [_]types.StateValue{.{ .bytes = RAW_SCRIPT }};
    const call_txid = try contract.call("sendToScript", &args, prov.provider(), caller.signer(), .{
        .additional_contract_inputs = &extra,
        .additional_contract_input_args = &per_input,
    });
    defer allocator.free(call_txid);

    const txs = prov.getBroadcastedTxs();
    const call_tx = txs[txs.len - 1];
    try std.testing.expect(std.mem.indexOf(u8, call_tx, PREVOUTS_PUSH_PREFIX) == null);
}
