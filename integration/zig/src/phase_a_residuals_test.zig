const std = @import("std");
const runar = @import("runar");
const helpers = @import("helpers.zig");
const compile = @import("compile.zig");

fn deployCall(
    allocator: std.mem.Allocator,
    path: []const u8,
    ctor: []const runar.StateValue,
    method: []const u8,
    args: []const runar.StateValue,
    sats: i64,
) !void {
    helpers.requireNodeAvailable(allocator);

    var artifact = try compile.compileContract(allocator, path);
    defer artifact.deinit();

    var contract = try runar.RunarContract.init(allocator, &artifact, ctor);
    defer contract.deinit();

    var wallet = try helpers.newWallet(allocator);
    defer wallet.deinit();
    const fund_txid = try helpers.fundWallet(allocator, &wallet, 1.0);
    allocator.free(fund_txid);

    var rpc_provider = helpers.RPCProvider.init(allocator);
    var local_signer = try wallet.localSigner();

    const deploy_txid = try contract.deploy(rpc_provider.provider(), local_signer.signer(), .{ .satoshis = sats });
    defer allocator.free(deploy_txid);
    try std.testing.expect(deploy_txid.len == 64);

    const call_txid = try contract.call(method, args, rpc_provider.provider(), local_signer.signer(), .{});
    defer allocator.free(call_txid);
    try std.testing.expect(call_txid.len == 64);
    std.debug.print("PhaseA_PASS method={s} call_txid={s}\n", .{ method, call_txid });
}

test "PhaseA_BranchMergedLocals" {
    const allocator = std.testing.allocator;
    try deployCall(
        allocator,
        "integration/contracts/constructs/BranchMergedLocals.runar.ts",
        &[_]runar.StateValue{ .{ .int = 10 }, .{ .int = 20 } },
        "bid",
        &[_]runar.StateValue{ .{ .int = 99 }, .{ .int = 1 } },
        50_000,
    );
}

test "PhaseA_CondWriteMultiField" {
    const allocator = std.testing.allocator;
    try deployCall(
        allocator,
        "integration/contracts/constructs/CondWriteMultiField.runar.ts",
        &[_]runar.StateValue{ .{ .int = 1 }, .{ .int = 2 } },
        "bump",
        &[_]runar.StateValue{.{ .int = 1 }},
        50_000,
    );
}

test "PhaseA_StateByteString1B" {
    const allocator = std.testing.allocator;
    try deployCall(
        allocator,
        "integration/contracts/constructs/StateByteString1B.runar.ts",
        &[_]runar.StateValue{.{ .bytes = "05" }},
        "setTag",
        &[_]runar.StateValue{.{ .bytes = "ab" }},
        10_000,
    );
}

test "PhaseA_ConditionalDataOutput" {
    const allocator = std.testing.allocator;
    try deployCall(
        allocator,
        "integration/contracts/constructs/ConditionalDataOutput.runar.ts",
        &[_]runar.StateValue{.{ .int = 0 }},
        "pay",
        &[_]runar.StateValue{ .{ .boolean = true }, .{ .bytes = "6a096273766d2d74657374" } },
        20_000,
    );
}

test "PhaseA_RawOutput" {
    const allocator = std.testing.allocator;
    helpers.requireNodeAvailable(allocator);

    var artifact = try compile.compileContract(allocator, "integration/contracts/outputs/RawOutput.runar.ts");
    defer artifact.deinit();

    var contract = try runar.RunarContract.init(allocator, &artifact, &[_]runar.StateValue{.{ .int = 0 }});
    defer contract.deinit();

    var wallet = try helpers.newWallet(allocator);
    defer wallet.deinit();
    const fund_txid = try helpers.fundWallet(allocator, &wallet, 1.0);
    defer allocator.free(fund_txid);

    var rpc_provider = helpers.RPCProvider.init(allocator);
    var local_signer = try wallet.localSigner();

    const deploy_txid = try contract.deploy(rpc_provider.provider(), local_signer.signer(), .{ .satoshis = 50_000 });
    defer allocator.free(deploy_txid);
    std.debug.print("PhaseA_RawOutput deploy_txid={s}\n", .{deploy_txid});

    const pkh_hex = try wallet.pubKeyHashHex(allocator);
    defer allocator.free(pkh_hex);
    const p2pkh = try std.fmt.allocPrint(allocator, "76a914{s}88ac", .{pkh_hex});
    defer allocator.free(p2pkh);
    // Explicit new_state count=1 after sendToScript
    const call_txid = contract.call(
        "sendToScript",
        &[_]runar.StateValue{.{ .bytes = p2pkh }},
        rpc_provider.provider(),
        local_signer.signer(),
        .{ .new_state = &[_]runar.StateValue{.{ .int = 1 }} },
    ) catch |err| {
        std.debug.print("PhaseA_RawOutput call FAILED: {}\n", .{err});
        return err;
    };
    defer allocator.free(call_txid);
    try std.testing.expect(call_txid.len == 64);
    std.debug.print("PhaseA_PASS method=sendToScript call_txid={s}\n", .{call_txid});
}
