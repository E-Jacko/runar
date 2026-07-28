//! C18: a public method whose ONLY read of a mutable variable-length
//! (ByteString) state field happens inside a PRIVATE helper must still take
//! the implicit `_codePart` stack parameter.
//!
//! Private methods are inlined into the caller's stack context, so the
//! helper's `load_prop` really does execute in the public method. When
//! `methodReadsVarLenState` did not recurse through `method_call` targets,
//! `usesCodePart` came out false, `lowerDeserializeState` took its
//! "terminal method, skip deserialization" shortcut, and the load fell back
//! to the deploy-time constructor placeholder instead of the live on-chain
//! state — a silent wrong-result / funds-safety bug.
//!
//! Lock: the helper variant must compile to the SAME script as the control
//! that reads the field directly, and its ABI must carry usesCodePart.

const std = @import("std");
const compiler_api = @import("../compiler_api.zig");

const helper_variant =
    \\class VarLenPrivateRead extends StatefulSmartContract {
    \\  tag: ByteString;
    \\
    \\  constructor(tag: ByteString) {
    \\    super(tag);
    \\    this.tag = tag;
    \\  }
    \\
    \\  private tagLen(): bigint {
    \\    return len(this.tag);
    \\  }
    \\
    \\  public check(expected: bigint) {
    \\    assert(this.tagLen() == expected);
    \\  }
    \\}
;

const direct_variant =
    \\class VarLenPrivateRead extends StatefulSmartContract {
    \\  tag: ByteString;
    \\
    \\  constructor(tag: ByteString) {
    \\    super(tag);
    \\    this.tag = tag;
    \\  }
    \\
    \\  public check(expected: bigint) {
    \\    assert(len(this.tag) == expected);
    \\  }
    \\}
;

fn artifactScriptHex(json: []const u8) ![]const u8 {
    const marker = "\"script\":\"";
    const idx = std.mem.indexOf(u8, json, marker) orelse return error.MissingHex;
    const after = idx + marker.len;
    const end = std.mem.indexOfPos(u8, json, after, "\"") orelse return error.MissingHex;
    return json[after..end];
}

test "C18: var-len state read behind a private helper still emits _codePart" {
    const allocator = std.testing.allocator;

    const helper = try compiler_api.compileSource(allocator, helper_variant, "VarLenPrivateRead.runar.ts");
    defer helper.deinit(allocator);
    const control = try compiler_api.compileSource(allocator, direct_variant, "VarLenPrivateRead.runar.ts");
    defer control.deinit(allocator);

    const helper_json = helper.artifact_json orelse return error.MissingArtifact;
    const control_json = control.artifact_json orelse return error.MissingArtifact;

    // The helper variant reads the live on-chain state, exactly like the
    // direct read does: same locking script, byte for byte.
    try std.testing.expectEqualStrings(
        try artifactScriptHex(control_json),
        try artifactScriptHex(helper_json),
    );

    // And the ABI advertises the implicit _codePart parameter so the SDK
    // provisions it in the unlocking script.
    try std.testing.expect(std.mem.indexOf(u8, helper_json, "\"usesCodePart\":true") != null);
}

test "C18: private-helper recursion does not disturb fixed-size state reads" {
    const allocator = std.testing.allocator;

    // `count` is a fixed-size (bigint) mutable field, so reading it through a
    // helper must NOT start demanding _codePart — the narrow var-length gate
    // from issue #100 stays narrow.
    const source =
        \\class FixedPrivateRead extends StatefulSmartContract {
        \\  count: bigint;
        \\
        \\  constructor(count: bigint) {
        \\    super(count);
        \\    this.count = count;
        \\  }
        \\
        \\  private current(): bigint {
        \\    return this.count;
        \\  }
        \\
        \\  public check(expected: bigint) {
        \\    assert(this.current() == expected);
        \\  }
        \\}
    ;

    const result = try compiler_api.compileSource(allocator, source, "FixedPrivateRead.runar.ts");
    defer result.deinit(allocator);
    const json = result.artifact_json orelse return error.MissingArtifact;
    try std.testing.expect(std.mem.indexOf(u8, json, "\"usesCodePart\":true") == null);
}
