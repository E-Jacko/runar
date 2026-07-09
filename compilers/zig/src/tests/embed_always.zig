//! Issue #109 — `/** @embedAlways */` readonly-field DCE opt-out (Zig tier).
//!
//! A readonly field no method references is normally eliminated by ANF
//! dead-binding DCE (the dead load_prop is dropped, so no constructor slot is
//! emitted), silently removing deploy-time metadata an author intends to
//! recover from the on-chain script later. The @embedAlways directive forces
//! the field into the locking script (a constructor slot). Golden hexes are the
//! TypeScript reference output (fold-OFF); the Zig tier must be byte-identical.
//! These are the same goldens the Go tier pins (compilers/go/compiler
//! /embed_always_test.go).

const std = @import("std");
const compiler_api = @import("../compiler_api.zig");

/// A stateless contract with a metadata field the body never reads. `directive`
/// is spliced in immediately before the `metadataId` field.
fn metaSource(comptime directive: []const u8) []const u8 {
    return "import { SmartContract, assert, Addr, PubKey, Sig, ByteString, hash160, checkSig } from 'runar-lang';\n" ++
        "class Meta extends SmartContract {\n" ++
        "  readonly pubKeyHash: Addr;\n" ++
        "  " ++ directive ++ "\n" ++
        "  readonly metadataId: ByteString;\n" ++
        "  constructor(pubKeyHash: Addr, metadataId: ByteString) {\n" ++
        "    super(pubKeyHash, metadataId);\n" ++
        "    this.pubKeyHash = pubKeyHash;\n" ++
        "    this.metadataId = metadataId;\n" ++
        "  }\n" ++
        "  public unlock(sig: Sig, pubKey: PubKey) {\n" ++
        "    assert(hash160(pubKey) === this.pubKeyHash);\n" ++
        "    assert(checkSig(sig, pubKey));\n" ++
        "  }\n" ++
        "}\n";
}

// TS-reference golden scripts (fold-OFF; identical fold-ON for this contract —
// no foldable constants). Byte-identical to the Go tier's goldens.
const META_PLAIN_GOLDEN = "76a90088ac";
const META_EMBED_GOLDEN = "0078a900887b7bac77";

fn countConstructorSlots(json: []const u8) usize {
    // Count the "paramIndex" keys inside the constructorSlots array.
    const marker = "\"constructorSlots\":[";
    const start = std.mem.indexOf(u8, json, marker) orelse return 0;
    const arr = json[start + marker.len ..];
    const arr_end = std.mem.indexOfScalar(u8, arr, ']') orelse return 0;
    const body = arr[0..arr_end];
    var n: usize = 0;
    var i: usize = 0;
    while (std.mem.indexOfPos(u8, body, i, "\"paramIndex\"")) |p| : (i = p + 1) n += 1;
    return n;
}

test "embedAlways: un-annotated field is eliminated (byte-identical to TS, no slot)" {
    const a = std.testing.allocator;
    const r = try compiler_api.compileSource(a, metaSource(""), "Meta.runar.ts");
    defer r.deinit(a);
    try std.testing.expectEqualStrings(META_PLAIN_GOLDEN, r.script_hex);
    // Only pubKeyHash gets a constructor slot; metadataId is stripped.
    try std.testing.expectEqual(@as(usize, 1), countConstructorSlots(r.artifact_json.?));
}

test "embedAlways: /** @embedAlways */ field is preserved (byte-identical to TS)" {
    const a = std.testing.allocator;
    const r = try compiler_api.compileSource(a, metaSource("/** @embedAlways */"), "Meta.runar.ts");
    defer r.deinit(a);
    try std.testing.expectEqualStrings(META_EMBED_GOLDEN, r.script_hex);
    // Both metadataId and pubKeyHash get constructor slots.
    try std.testing.expectEqual(@as(usize, 2), countConstructorSlots(r.artifact_json.?));
}

test "embedAlways: // @embedAlways line-comment form is honoured too" {
    const a = std.testing.allocator;
    const r = try compiler_api.compileSource(a, metaSource("// @embedAlways"), "Meta.runar.ts");
    defer r.deinit(a);
    try std.testing.expectEqualStrings(META_EMBED_GOLDEN, r.script_hex);
}

test "embedAlways: annotated hex carries more bytes than un-annotated" {
    const a = std.testing.allocator;
    const off = try compiler_api.compileSource(a, metaSource(""), "Meta.runar.ts");
    defer off.deinit(a);
    const on = try compiler_api.compileSource(a, metaSource("/** @embedAlways */"), "Meta.runar.ts");
    defer on.deinit(a);
    try std.testing.expect(!std.mem.eql(u8, off.script_hex, on.script_hex));
    try std.testing.expect(on.script_hex.len > off.script_hex.len);
}
