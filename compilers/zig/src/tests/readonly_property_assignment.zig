//! Audit C2 — `readonly` property assignment must be rejected outside the
//! constructor.
//!
//! spec/semantics.md:247
//!   <this.p = e, env, sigma> ==> ERROR: cannot assign to readonly property
//!
//! Without the rule a contract that reassigns its readonly owner before
//! checking it compiles to `76a97ca9788777` — hash160(pk) compared against
//! hash160(pk), true for ANY pubkey, i.e. anyone can spend.
//!
//! The constructor MUST still be allowed to assign readonly properties (the
//! Zig tier's ConstructorNode carries `assignments`, not statements, so
//! constructor writes never reach the statement walk).
//!
//! Mirrors packages/runar-compiler/src/__tests__/readonly-property-assignment.test.ts

const std = @import("std");
const parse_ts = @import("../passes/parse_ts.zig");
const validate = @import("../passes/validate.zig");

/// The cross-tier diagnostic substring.
const READONLY_WRITE = "assign to readonly property";

/// Parse + validate a .runar.ts source, returning whether any ERROR diagnostic
/// contains `needle`. Uses an internal arena so the frontend's allocations are
/// freed (`a` is the leak-checking allocator).
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

test "readonly-write: owner-hijack contract is rejected" {
    const a = std.testing.allocator;
    const src =
        \\class Hijack extends SmartContract {
        \\  readonly ownerHash: Addr;
        \\  constructor(ownerHash: Addr) { super(ownerHash); this.ownerHash = ownerHash; }
        \\  public unlock(attackerPk: PubKey) {
        \\    this.ownerHash = hash160(attackerPk);
        \\    assert(hash160(attackerPk) == this.ownerHash);
        \\  }
        \\}
    ;
    try std.testing.expect(try hasError(a, src, READONLY_WRITE));
}

test "readonly-write: stateful method write is rejected" {
    const a = std.testing.allocator;
    const src =
        \\class Vault extends StatefulSmartContract {
        \\  readonly owner: Addr;
        \\  count: bigint;
        \\  constructor(owner: Addr, count: bigint) { super(owner, count); this.owner = owner; this.count = count; }
        \\  public bump(newOwner: Addr) {
        \\    this.owner = newOwner;
        \\    this.count = this.count + 1n;
        \\  }
        \\}
    ;
    try std.testing.expect(try hasError(a, src, READONLY_WRITE));
}

test "readonly-write: write nested in an if branch is rejected" {
    const a = std.testing.allocator;
    const src =
        \\class Nested extends StatefulSmartContract {
        \\  readonly owner: Addr;
        \\  count: bigint;
        \\  constructor(owner: Addr, count: bigint) { super(owner, count); this.owner = owner; this.count = count; }
        \\  public bump(newOwner: Addr, flag: boolean) {
        \\    if (flag) {
        \\      this.owner = newOwner;
        \\    } else {
        \\      this.count = this.count + 1n;
        \\    }
        \\  }
        \\}
    ;
    try std.testing.expect(try hasError(a, src, READONLY_WRITE));
}

test "readonly-write: write in a private helper is rejected" {
    const a = std.testing.allocator;
    const src =
        \\class Helper extends StatefulSmartContract {
        \\  readonly owner: Addr;
        \\  count: bigint;
        \\  constructor(owner: Addr, count: bigint) { super(owner, count); this.owner = owner; this.count = count; }
        \\  private steal(newOwner: Addr): void {
        \\    this.owner = newOwner;
        \\  }
        \\  public bump(newOwner: Addr) {
        \\    this.steal(newOwner);
        \\    this.count = this.count + 1n;
        \\  }
        \\}
    ;
    try std.testing.expect(try hasError(a, src, READONLY_WRITE));
}

test "readonly-write: increment of a readonly property is rejected" {
    const a = std.testing.allocator;
    const src =
        \\class Bump extends StatefulSmartContract {
        \\  readonly limit: bigint;
        \\  count: bigint;
        \\  constructor(limit: bigint, count: bigint) { super(limit, count); this.limit = limit; this.count = count; }
        \\  public go() {
        \\    this.limit++;
        \\    this.count = this.count + 1n;
        \\  }
        \\}
    ;
    try std.testing.expect(try hasError(a, src, READONLY_WRITE));
}

// ---------------------------------------------------------------------------
// The constructor must keep working — every contract assigns its readonly
// properties there.
// ---------------------------------------------------------------------------

test "readonly-write: constructor assignment is accepted" {
    const a = std.testing.allocator;
    const src =
        \\class P2PKH extends SmartContract {
        \\  readonly pubKeyHash: Addr;
        \\  constructor(pubKeyHash: Addr) { super(pubKeyHash); this.pubKeyHash = pubKeyHash; }
        \\  public unlock(sig: Sig, pubKey: PubKey) {
        \\    assert(hash160(pubKey) == this.pubKeyHash);
        \\    assert(checkSig(sig, pubKey));
        \\  }
        \\}
    ;
    try std.testing.expectEqual(@as(usize, 0), try errorCount(a, src));
}

test "readonly-write: mutable state mutation is accepted" {
    const a = std.testing.allocator;
    const src =
        \\class Counter extends StatefulSmartContract {
        \\  readonly owner: Addr;
        \\  count: bigint;
        \\  constructor(owner: Addr, count: bigint) { super(owner, count); this.owner = owner; this.count = count; }
        \\  public increment() {
        \\    this.count = this.count + 1n;
        \\  }
        \\}
    ;
    try std.testing.expectEqual(@as(usize, 0), try errorCount(a, src));
}

test "readonly-write: a local shadowing a readonly property name is accepted" {
    const a = std.testing.allocator;
    const src =
        \\class Shadow extends StatefulSmartContract {
        \\  readonly limit: bigint;
        \\  count: bigint;
        \\  constructor(limit: bigint, count: bigint) { super(limit, count); this.limit = limit; this.count = count; }
        \\  public increment() {
        \\    let limit: bigint = 5n;
        \\    limit = 6n;
        \\    assert(this.count < limit);
        \\    this.count = this.count + 1n;
        \\  }
        \\}
    ;
    try std.testing.expectEqual(@as(usize, 0), try errorCount(a, src));
}
