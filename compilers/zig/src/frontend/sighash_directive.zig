//! `@sighash` directive parsing (issue #123).
//!
//! A public method may carry a `/** @sighash <FLAGS> */` comment directive that
//! declares which BIP-143 sighash type its auto-injected covenant (and the
//! SDK-built preimage) commits to. `<FLAGS>` is a `|`-separated set of SigHash
//! names, e.g. `SINGLE|FORKID`, `ALL|ANYONECANPAY|FORKID`, `NONE|FORKID`.
//!
//! The default (no directive) is `ALL|FORKID` (0x41) — byte-identical to the
//! historically-pinned mode, so existing fixtures see ZERO change.
//!
//! This is a faithful port of the TypeScript reference module
//! packages/runar-compiler/src/passes/sighash-directive.ts and its Go peer
//! (compilers/go/frontend/sighash_directive.go): the flag grammar (name ->
//! value, combo validity) plus the FORKID-mandatory guard.

const std = @import("std");

/// SIGHASH_ALL | SIGHASH_FORKID — the default when no directive is present.
pub const SIGHASH_DEFAULT: i32 = 0x41;

// Base-type mask and flag constants shared with the field-usage validator.
pub const BASE_TYPE_MASK: i32 = 0x1f;
pub const BASE_ALL: i32 = 0x01;
pub const BASE_NONE: i32 = 0x02;
pub const BASE_SINGLE: i32 = 0x03;
pub const FLAG_FORKID: i32 = 0x40;
pub const FLAG_ANYONECANPAY: i32 = 0x80;

/// Numeric value of each sighash flag name.
fn flagValue(name: []const u8) ?i32 {
    const map = std.StaticStringMap(i32).initComptime(.{
        .{ "ALL", @as(i32, 0x01) },
        .{ "NONE", @as(i32, 0x02) },
        .{ "SINGLE", @as(i32, 0x03) },
        .{ "FORKID", @as(i32, 0x40) },
        .{ "ANYONECANPAY", @as(i32, 0x80) },
    });
    return map.get(name);
}

fn isBaseTypeName(name: []const u8) bool {
    return std.mem.eql(u8, name, "ALL") or std.mem.eql(u8, name, "NONE") or std.mem.eql(u8, name, "SINGLE");
}

/// Result of parsing a flag list — either a numeric value or an error message.
/// Mirrors the TS discriminated union `{ value } | { error }`. `err` is a
/// borrowed static string OR an allocator-owned message (the caller decides
/// how long to keep it); it is null on success.
pub const ParseResult = union(enum) {
    value: i32,
    err: []const u8,
};

/// Parse the flag list of an `@sighash` directive.
///
/// `flags_text` is the raw text following `@sighash` (e.g. "SINGLE|FORKID"),
/// with any trailing comment punctuation already stripped by the caller. When
/// an error message must be formatted, it is allocated with `allocator`.
///
/// Validation (security-relevant — a mis-declared mode is an exploit class):
///   - every name must be a known flag (reject typos like FORKD)
///   - EXACTLY ONE base type (ALL/NONE/SINGLE) — reject zero, and reject
///     nonsensical combos such as ALL|NONE. This is checked on NAMES, not on
///     the OR-ed numeric value, because ALL|NONE (0x01|0x02) collides with the
///     numeric value of SINGLE (0x03) — a silent, dangerous aliasing a purely
///     numeric check would miss.
///   - reject a duplicated flag name (signals a copy/paste error).
///   - FORKID is mandatory on BSV (the whole OP_PUSH_TX / BIP-143 machinery is
///     FORKID-only, so a FORKID-less mode deploys to brick).
pub fn parseFlags(allocator: std.mem.Allocator, flags_text: []const u8) ParseResult {
    const raw = std.mem.trim(u8, flags_text, " \t\r\n");
    if (raw.len == 0) {
        return .{ .err = "@sighash directive requires at least one flag (e.g. `@sighash ALL|FORKID`)" };
    }

    var value: i32 = 0;
    var base_type_count: usize = 0;
    var base_type_name: []const u8 = "";
    var seen: [5]bool = .{ false, false, false, false, false };

    var it = std.mem.splitScalar(u8, raw, '|');
    while (it.next()) |part| {
        const name = std.mem.trim(u8, part, " \t\r\n");
        if (name.len == 0) {
            return .{ .err = std.fmt.allocPrint(allocator, "@sighash directive has an empty flag in '{s}'", .{raw}) catch "@sighash directive has an empty flag" };
        }
        const v = flagValue(name) orelse {
            return .{ .err = std.fmt.allocPrint(allocator, "@sighash: unknown flag '{s}' (valid: ALL, NONE, SINGLE, FORKID, ANYONECANPAY)", .{name}) catch "@sighash: unknown flag" };
        };
        // Duplicate detection keyed on the numeric value's bit index.
        const idx: usize = switch (v) {
            0x01 => 0,
            0x02 => 1,
            0x03 => 2,
            0x40 => 3,
            0x80 => 4,
            else => unreachable,
        };
        if (seen[idx]) {
            return .{ .err = std.fmt.allocPrint(allocator, "@sighash: duplicate flag '{s}' in '{s}'", .{ name, raw }) catch "@sighash: duplicate flag" };
        }
        seen[idx] = true;
        if (isBaseTypeName(name)) {
            base_type_count += 1;
            base_type_name = name;
        }
        value |= v;
    }

    if (base_type_count == 0) {
        return .{ .err = std.fmt.allocPrint(allocator, "@sighash: must specify exactly one base type (ALL, NONE, or SINGLE); got '{s}'", .{raw}) catch "@sighash: must specify exactly one base type (ALL, NONE, or SINGLE)" };
    }
    if (base_type_count > 1) {
        return .{ .err = std.fmt.allocPrint(allocator, "@sighash: cannot combine base types in '{s}' — pick exactly one of ALL/NONE/SINGLE", .{raw}) catch "@sighash: cannot combine base types — pick exactly one of ALL/NONE/SINGLE" };
    }

    // FORKID is mandatory on BSV: the entire OP_PUSH_TX / BIP-143 preimage
    // machinery is FORKID-only, so a FORKID-less flag set deploys a covenant
    // whose derived signature can never verify (deploy-to-brick).
    if (value & FLAG_FORKID == 0) {
        return .{ .err = std.fmt.allocPrint(allocator, "@sighash: FORKID is mandatory on BSV; write e.g. @sighash {s}|FORKID (got '{s}')", .{ base_type_name, raw }) catch "@sighash: FORKID is mandatory on BSV" };
    }

    return .{ .value = value };
}

/// Extract and parse an `@sighash` directive from a block of comment text.
/// Returns null when no `@sighash` token is present; otherwise the parse
/// result (which may itself be an error). Mirrors the TS SIGHASH_RE
/// `@sighash\s+([A-Za-z0-9_|\s]*?)(?:\*\/|\n|\r|$)`.
pub fn extractDirective(allocator: std.mem.Allocator, comment_text: []const u8) ?ParseResult {
    const marker = "@sighash";
    const pos = std.mem.indexOf(u8, comment_text, marker) orelse return null;
    const after = pos + marker.len;
    // Match the TS `@sighash\s+`: at least one whitespace must follow the
    // marker, otherwise `@sighashType`-style identifiers are NOT directives.
    if (after >= comment_text.len or !(comment_text[after] == ' ' or comment_text[after] == '\t' or comment_text[after] == '\n' or comment_text[after] == '\r')) {
        return null;
    }
    // Collect the flag text up to `*/`, newline, carriage return, EOF, or any
    // char outside the [A-Za-z0-9_| \t] flag alphabet (so trailing prose ends
    // the capture). Leading/trailing whitespace is trimmed by parseFlags.
    const rest = comment_text[after..];
    var end: usize = 0;
    while (end < rest.len) : (end += 1) {
        const c = rest[end];
        if (c == '\n' or c == '\r') break;
        if (c == '*' and end + 1 < rest.len and rest[end + 1] == '/') break;
        if (!(std.ascii.isAlphanumeric(c) or c == '_' or c == '|' or c == ' ' or c == '\t')) break;
    }
    return parseFlags(allocator, rest[0..end]);
}

/// Render a sighash value as a human-readable flag string (for diagnostics).
/// Caller owns the returned slice. Mirrors the TS describeSighash.
pub fn describe(allocator: std.mem.Allocator, value: i32) ![]const u8 {
    var parts: std.ArrayListUnmanaged(u8) = .empty;
    errdefer parts.deinit(allocator);
    const base = value & BASE_TYPE_MASK;
    switch (base) {
        BASE_ALL => try parts.appendSlice(allocator, "ALL"),
        BASE_NONE => try parts.appendSlice(allocator, "NONE"),
        BASE_SINGLE => try parts.appendSlice(allocator, "SINGLE"),
        else => {
            var buf: [16]u8 = undefined;
            const s = std.fmt.bufPrint(&buf, "0x{x}", .{base}) catch "0x?";
            try parts.appendSlice(allocator, s);
        },
    }
    if (value & FLAG_ANYONECANPAY != 0) try parts.appendSlice(allocator, "|ANYONECANPAY");
    if (value & FLAG_FORKID != 0) try parts.appendSlice(allocator, "|FORKID");
    return parts.toOwnedSlice(allocator);
}

// ============================================================================
// Tests — faithful port of sighash-directive.test.ts (via the Go peer).
// ============================================================================

test "parseFlags common combos" {
    const a = std.testing.allocator;
    const cases = .{
        .{ "ALL|FORKID", @as(i32, 0x41) },
        .{ "SINGLE|FORKID", @as(i32, 0x43) },
        .{ "NONE|FORKID", @as(i32, 0x42) },
        .{ "ALL|ANYONECANPAY|FORKID", @as(i32, 0xc1) },
    };
    inline for (cases) |c| {
        const r = parseFlags(a, c[0]);
        try std.testing.expect(r == .value);
        try std.testing.expectEqual(c[1], r.value);
    }
}

test "parseFlags order and whitespace" {
    const r = parseFlags(std.testing.allocator, " FORKID | SINGLE ");
    try std.testing.expect(r == .value);
    try std.testing.expectEqual(@as(i32, 0x43), r.value);
}

test "parseFlags default is 0x41" {
    try std.testing.expectEqual(@as(i32, 0x41), SIGHASH_DEFAULT);
    const r = parseFlags(std.testing.allocator, "ALL|FORKID");
    try std.testing.expect(r == .value and r.value == SIGHASH_DEFAULT);
}

test "parseFlags rejects unknown flag" {
    const a = std.testing.allocator;
    const r = parseFlags(a, "ALL|FORKD");
    try std.testing.expect(r == .err);
    try std.testing.expect(std.mem.indexOf(u8, r.err, "unknown flag") != null);
    a.free(r.err);
}

test "parseFlags rejects ALL|NONE on names (aliasing guard)" {
    const a = std.testing.allocator;
    const r = parseFlags(a, "ALL|NONE|FORKID");
    try std.testing.expect(r == .err);
    try std.testing.expect(std.mem.indexOf(u8, r.err, "cannot combine base types") != null);
    a.free(r.err);
}

test "parseFlags rejects two base types" {
    const a = std.testing.allocator;
    const r = parseFlags(a, "SINGLE|ALL");
    try std.testing.expect(r == .err);
    a.free(r.err);
}

test "parseFlags rejects no base type" {
    const a = std.testing.allocator;
    const r = parseFlags(a, "FORKID|ANYONECANPAY");
    try std.testing.expect(r == .err);
    try std.testing.expect(std.mem.indexOf(u8, r.err, "exactly one base type") != null);
    a.free(r.err);
}

test "parseFlags rejects duplicate" {
    const a = std.testing.allocator;
    const r = parseFlags(a, "SINGLE|SINGLE|FORKID");
    try std.testing.expect(r == .err);
    try std.testing.expect(std.mem.indexOf(u8, r.err, "duplicate flag") != null);
    a.free(r.err);
}

test "parseFlags rejects empty" {
    try std.testing.expect(parseFlags(std.testing.allocator, "") == .err);
    try std.testing.expect(parseFlags(std.testing.allocator, "   ") == .err);
}

test "parseFlags requires FORKID (deploy-to-brick guard)" {
    const a = std.testing.allocator;
    inline for (.{ "SINGLE", "ALL", "NONE", "ALL|ANYONECANPAY" }) |flags| {
        const r = parseFlags(a, flags);
        try std.testing.expect(r == .err);
        try std.testing.expect(std.mem.indexOf(u8, r.err, "FORKID is mandatory on BSV") != null);
        a.free(r.err);
    }
}

test "extractDirective JSDoc and line-comment" {
    const a = std.testing.allocator;
    const r1 = extractDirective(a, "/** @sighash SINGLE|FORKID */") orelse return error.MissingDirective;
    try std.testing.expect(r1 == .value and r1.value == 0x43);
    const r2 = extractDirective(a, "// @sighash NONE|FORKID") orelse return error.MissingDirective;
    try std.testing.expect(r2 == .value and r2.value == 0x42);
    try std.testing.expect(extractDirective(a, "/** no directive here */") == null);
}

test "describe renders flag string" {
    const a = std.testing.allocator;
    const cases = .{
        .{ @as(i32, 0x41), "ALL|FORKID" },
        .{ @as(i32, 0x43), "SINGLE|FORKID" },
        .{ @as(i32, 0xc1), "ALL|ANYONECANPAY|FORKID" },
        .{ @as(i32, 0x42), "NONE|FORKID" },
    };
    inline for (cases) |c| {
        const s = try describe(a, c[0]);
        defer a.free(s);
        try std.testing.expectEqualStrings(c[1], s);
    }
}
