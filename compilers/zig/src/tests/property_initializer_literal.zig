//! Audit C3 — property initializers are restricted to literal values.
//!
//! `ts`, `go` and `java` enforced this; `rust`, `zig`, `python` and `ruby` did
//! not — they compiled e.g. `p: bigint = 1n + 2n;` and emitted a deployable
//! locking script for a program the language does not define.
//!
//! Mirrors packages/runar-compiler/src/__tests__/property-initializer-literal.test.ts

const std = @import("std");
const parse_ts = @import("../passes/parse_ts.zig");
const validate = @import("../passes/validate.zig");

/// The cross-tier diagnostic substring.
const NON_LITERAL_INIT = "initializer must be a literal value";

fn hasError(a: std.mem.Allocator, src: []const u8, needle: []const u8) !bool {
    var arena = std.heap.ArenaAllocator.init(a);
    defer arena.deinit();
    const w = arena.allocator();
    const parsed = parse_ts.parseTs(w, src, "X.runar.ts");
    for (parsed.errors) |e| {
        if (std.mem.indexOf(u8, e, needle) != null) return true;
    }
    if (parsed.contract == null) return false;
    const res = try validate.validate(w, parsed.contract.?);
    for (res.errors) |d| {
        if (std.mem.indexOf(u8, d.message, needle) != null) return true;
    }
    return false;
}

fn errorCount(a: std.mem.Allocator, src: []const u8) !usize {
    var arena = std.heap.ArenaAllocator.init(a);
    defer arena.deinit();
    const w = arena.allocator();
    const parsed = parse_ts.parseTs(w, src, "X.runar.ts");
    if (parsed.errors.len > 0) return parsed.errors.len;
    if (parsed.contract == null) return 0;
    const res = try validate.validate(w, parsed.contract.?);
    return res.errors.len;
}

test "initializer-literal: arithmetic initializer is rejected" {
    const a = std.testing.allocator;
    const src =
        \\class Bad extends StatefulSmartContract {
        \\  count: bigint = 1n + 2n;
        \\  readonly owner: Addr;
        \\  constructor(owner: Addr) { super(owner); this.owner = owner; }
        \\  public bump() {
        \\    this.count = this.count + 1n;
        \\  }
        \\}
    ;
    try std.testing.expect(try hasError(a, src, NON_LITERAL_INIT));
}

test "initializer-literal: call-expression initializer is rejected" {
    const a = std.testing.allocator;
    const src =
        \\class Bad2 extends StatefulSmartContract {
        \\  count: bigint = abs(-3n);
        \\  readonly owner: Addr;
        \\  constructor(owner: Addr) { super(owner); this.owner = owner; }
        \\  public bump() {
        \\    this.count = this.count + 1n;
        \\  }
        \\}
    ;
    try std.testing.expect(try hasError(a, src, NON_LITERAL_INIT));
}

test "initializer-literal: literal initializers are accepted" {
    const a = std.testing.allocator;
    const src =
        \\class Good extends StatefulSmartContract {
        \\  count: bigint = 7n;
        \\  flag: boolean = true;
        \\  tag: ByteString = 'deadbeef';
        \\  offset: bigint = -3n;
        \\  readonly owner: Addr;
        \\  constructor(owner: Addr) { super(owner); this.owner = owner; }
        \\  public bump() {
        \\    this.count = this.count + 1n;
        \\  }
        \\}
    ;
    try std.testing.expectEqual(@as(usize, 0), try errorCount(a, src));
}
