//! Testing-gap remediation Phase A5 (Zig tier): machine-checked gate on the
//! always-ack `MockProvider` escape hatches (`MockProvider.initAlwaysAck`,
//! `disableBroadcastValidation`, `enableBroadcastValidation(false)`).
//!
//! A source file may only use one of those escape hatches if it has a matching
//! entry in `always_ack_allowlist.json`. Enforced in BOTH directions: it fails
//! on unlisted always-ack usage (someone quietly re-disabling the fund-safety
//! net) AND on stale entries (a file that no longer needs always-ack, or that
//! was deleted) — so the list can only shrink.
//!
//! Mirrors packages/runar-sdk/src/__tests__/always-ack-allowlist.test.ts,
//! packages/runar-go/always_ack_allowlist_test.go,
//! packages/runar-rs/tests/always_ack_allowlist.rs,
//! packages/runar-py/tests/test_always_ack_allowlist.py and
//! packages/runar-rb/spec/sdk/always_ack_allowlist_spec.rb.

const std = @import("std");

const SELF = "src/sdk_always_ack_allowlist_test.zig";
/// The definition site. `sdk_provider.zig` declares the escape hatches; it is
/// not a test file and is never itself allowlisted.
const PROVIDER = "src/sdk_provider.zig";

const VALID_CATEGORIES = [_][]const u8{
    "structure-only", "negative-api", "fixture-shape", "pending-a3",
};

/// Call-site patterns.
const PATTERNS = [_][]const u8{
    "MockProvider.initAlwaysAck(",
    ".disableBroadcastValidation()",
    ".enableBroadcastValidation(false)",
};

fn packageRoot(allocator: std.mem.Allocator) ![]u8 {
    const z = try std.Io.Dir.cwd().realPathFileAlloc(std.testing.io, ".", allocator);
    defer allocator.free(z);
    return try allocator.dupe(u8, z);
}

fn readAllowlist(allocator: std.mem.Allocator, root: []const u8) !std.json.Parsed(std.json.Value) {
    const path = try std.fs.path.join(allocator, &.{ root, "always_ack_allowlist.json" });
    defer allocator.free(path);
    const raw = try std.Io.Dir.cwd().readFileAlloc(std.testing.io, path, allocator, .limited(1024 * 1024));
    defer allocator.free(raw);
    return std.json.parseFromSlice(std.json.Value, allocator, raw, .{});
}

/// Package-relative paths of every `src/**.zig` that calls an escape hatch.
fn filesUsingAlwaysAck(allocator: std.mem.Allocator, root: []const u8) ![][]u8 {
    var found: std.ArrayListUnmanaged([]u8) = .empty;
    errdefer {
        for (found.items) |f| allocator.free(f);
        found.deinit(allocator);
    }

    const src_path = try std.fs.path.join(allocator, &.{ root, "src" });
    defer allocator.free(src_path);

    const io = std.testing.io;
    const dir = try std.Io.Dir.cwd().openDir(io, src_path, .{ .iterate = true });
    defer dir.close(io);
    var it = dir.iterate();
    while (try it.next(io)) |entry| {
        if (entry.kind != .file) continue;
        if (!std.mem.endsWith(u8, entry.name, ".zig")) continue;

        const rel = try std.fmt.allocPrint(allocator, "src/{s}", .{entry.name});
        errdefer allocator.free(rel);
        if (std.mem.eql(u8, rel, SELF) or std.mem.eql(u8, rel, PROVIDER)) {
            allocator.free(rel);
            continue;
        }

        const abs = try std.fs.path.join(allocator, &.{ root, rel });
        defer allocator.free(abs);
        const body = std.Io.Dir.cwd().readFileAlloc(std.testing.io, abs, allocator, .limited(32 * 1024 * 1024)) catch {
            allocator.free(rel);
            continue;
        };
        defer allocator.free(body);

        var hit = false;
        for (PATTERNS) |pat| {
            if (std.mem.indexOf(u8, body, pat) != null) hit = true;
        }
        if (hit) {
            try found.append(allocator, rel);
        } else {
            allocator.free(rel);
        }
    }
    return found.toOwnedSlice(allocator);
}

fn freeList(allocator: std.mem.Allocator, list: [][]u8) void {
    for (list) |f| allocator.free(f);
    allocator.free(list);
}

test "always-ack allowlist: every entry is well formed and names an existing file" {
    const allocator = std.testing.allocator;
    const root = try packageRoot(allocator);
    defer allocator.free(root);

    var parsed = try readAllowlist(allocator, root);
    defer parsed.deinit();

    const entries = parsed.value.object.get("entries").?.array;
    for (entries.items) |e| {
        const file = e.object.get("file").?.string;
        const reason = e.object.get("reason").?.string;
        const category = e.object.get("category").?.string;
        try std.testing.expect(file.len > 0);
        try std.testing.expect(reason.len > 0);

        var category_ok = false;
        for (VALID_CATEGORIES) |c| {
            if (std.mem.eql(u8, c, category)) category_ok = true;
        }
        try std.testing.expect(category_ok);

        const abs = try std.fs.path.join(allocator, &.{ root, file });
        defer allocator.free(abs);
        std.Io.Dir.cwd().access(std.testing.io, abs, .{}) catch {
            std.debug.print(
                "always_ack_allowlist.json names '{s}', which does not exist; remove the entry\n",
                .{file},
            );
            return error.AllowlistEntryMissingFile;
        };
    }
}

test "always-ack allowlist: no stale entries and no ungoverned opt-out" {
    const allocator = std.testing.allocator;
    const root = try packageRoot(allocator);
    defer allocator.free(root);

    var parsed = try readAllowlist(allocator, root);
    defer parsed.deinit();
    const entries = parsed.value.object.get("entries").?.array;

    const usage = try filesUsingAlwaysAck(allocator, root);
    defer freeList(allocator, usage);

    // Stale: an entry whose file no longer uses an escape hatch.
    for (entries.items) |e| {
        const file = e.object.get("file").?.string;
        var still_uses = false;
        for (usage) |u| {
            if (std.mem.eql(u8, u, file)) still_uses = true;
        }
        if (!still_uses) {
            std.debug.print(
                "STALE always_ack_allowlist.json entry '{s}' — the file no longer uses " ++
                    "MockProvider.initAlwaysAck / disableBroadcastValidation / " ++
                    "enableBroadcastValidation(false). Remove it: the allowlist must only shrink.\n",
                .{file},
            );
            return error.StaleAllowlistEntry;
        }
    }

    // Ungoverned: a file that uses an escape hatch without an entry.
    for (usage) |u| {
        var listed = false;
        for (entries.items) |e| {
            if (std.mem.eql(u8, e.object.get("file").?.string, u)) listed = true;
        }
        if (!listed) {
            std.debug.print(
                "Unlisted always-ack MockProvider usage in '{s}'. Add an entry to " ++
                    "always_ack_allowlist.json with a file, reason and category " ++
                    "(structure-only | negative-api | fixture-shape | pending-a3), or fix the " ++
                    "test to run under the default validating provider instead.\n",
                .{u},
            );
            return error.UngovernedAlwaysAckUsage;
        }
    }
}
