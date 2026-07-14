// Zig-tier CLI shim for the cross-tier canonicalJson (RFC 8785 / JCS)
// differential fuzzer (conformance/fuzzer/canonical-json-differential.ts).
//
// Protocol (single-shot, stdin -> stdout), mirrors the Go / Rust / Python
// shims:
//
//   {"mode":"json","value":<any JSON>}
//       Parse `value` with std.json (which preserves the int-vs-float
//       distinction), convert to envelope.Value (mirrors jsonToValue in
//       sdk_envelope_interop_test.zig), run canonicalJson, print bytes, exit 0.
//   {"mode":"utf16","key":"<string>","units":[<int>,...]}
//       Build {key: <string from UTF-16 units>} where each unit is emitted as
//       its 3-byte WTF-8 form so canonicalJson's byte loop sees a lone
//       surrogate verbatim (mirrors the D6 rejection test).
//
//   On a typed rejection the shim prints "RUNAR_CANON_ERR:<error>" to stdout
//   and exits 3; any other failure exits 1.

const std = @import("std");
const envelope = @import("sdk_envelope.zig");

pub fn main(init: std.process.Init) !void {
    const io = init.io;
    // One-shot process: use an arena over the page allocator so we never have
    // to free, and the DebugAllocator's at-exit leak checker stays silent.
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var stdin_buf: [4096]u8 = undefined;
    var stdin_reader = std.Io.File.stdin().reader(io, &stdin_buf);
    const input_bytes = stdin_reader.interface.allocRemaining(allocator, .limited(16 * 1024 * 1024)) catch {
        try writeStderr(io, "read stdin failed\n");
        std.process.exit(1);
    };
    defer allocator.free(input_bytes);

    var parsed = std.json.parseFromSlice(std.json.Value, allocator, input_bytes, .{}) catch {
        try writeStderr(io, "parse request failed\n");
        std.process.exit(1);
    };
    defer parsed.deinit();

    const req = parsed.value.object;
    const mode = (req.get("mode") orelse {
        try writeStderr(io, "missing mode\n");
        std.process.exit(1);
    }).string;

    var input_value: envelope.Value = undefined;
    if (std.mem.eql(u8, mode, "json")) {
        const v = req.get("value") orelse std.json.Value{ .null = {} };
        input_value = try jsonToValue(allocator, v);
    } else if (std.mem.eql(u8, mode, "utf16")) {
        const key = (req.get("key") orelse std.json.Value{ .string = "" }).string;
        const units = (req.get("units") orelse {
            try writeStderr(io, "missing units\n");
            std.process.exit(1);
        }).array;
        var bad: std.ArrayListUnmanaged(u8) = .empty;
        defer bad.deinit(allocator);
        try encodeUtf16Units(allocator, &bad, units.items);
        const kvs = try allocator.alloc(envelope.Value.KeyValue, 1);
        kvs[0] = .{
            .key = try allocator.dupe(u8, key),
            .value = .{ .String = try allocator.dupe(u8, bad.items) },
        };
        input_value = .{ .Object = kvs };
    } else {
        try writeStderr(io, "unknown mode\n");
        std.process.exit(1);
    }

    if (envelope.canonicalJson(allocator, input_value)) |out| {
        defer allocator.free(out);
        try writeStdout(io, out);
    } else |err| {
        var buf: [256]u8 = undefined;
        const msg = std.fmt.bufPrint(&buf, "RUNAR_CANON_ERR:{s}", .{@errorName(err)}) catch "RUNAR_CANON_ERR:unknown";
        try writeStdout(io, msg);
        std.process.exit(3);
    }
}

/// Convert a std.json.Value into an envelope.Value tree. The arena is owned by
/// the caller's allocator; the process exits shortly after, so we never free.
fn jsonToValue(allocator: std.mem.Allocator, j: std.json.Value) !envelope.Value {
    switch (j) {
        .null => return .Null,
        .bool => |b| return .{ .Bool = b },
        .integer => |i| return .{ .Int = i },
        .float => |f| return .{ .Float = f },
        .number_string => |s| {
            const parsed = std.fmt.parseInt(i64, s, 10) catch null;
            if (parsed) |i| return .{ .Int = i };
            const f = try std.fmt.parseFloat(f64, s);
            return .{ .Float = f };
        },
        .string => |s| return .{ .String = try allocator.dupe(u8, s) },
        .array => |arr| {
            const out = try allocator.alloc(envelope.Value, arr.items.len);
            for (arr.items, 0..) |e, i| out[i] = try jsonToValue(allocator, e);
            return .{ .Array = out };
        },
        .object => |obj| {
            const out = try allocator.alloc(envelope.Value.KeyValue, obj.count());
            var it = obj.iterator();
            var i: usize = 0;
            while (it.next()) |entry| : (i += 1) {
                out[i] = .{
                    .key = try allocator.dupe(u8, entry.key_ptr.*),
                    .value = try jsonToValue(allocator, entry.value_ptr.*),
                };
            }
            return .{ .Object = out };
        },
    }
}

/// Encode UTF-16 code units to bytes. Surrogate pairs decode to their astral
/// rune; every other unit (including lone surrogates) is emitted as its 3-byte
/// (or shorter) UTF-8/WTF-8 form so canonicalJson sees the lone surrogate
/// pattern verbatim. Mirrors the D6 rejection test construction.
fn encodeUtf16Units(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), units: []const std.json.Value) !void {
    var i: usize = 0;
    while (i < units.len) : (i += 1) {
        const u: u32 = @intCast(units[i].integer);
        if (u >= 0xD800 and u <= 0xDBFF and i + 1 < units.len) {
            const lo: u32 = @intCast(units[i + 1].integer);
            if (lo >= 0xDC00 and lo <= 0xDFFF) {
                const cp = 0x10000 + ((u - 0xD800) << 10) + (lo - 0xDC00);
                try appendCodepointUtf8(allocator, out, cp);
                i += 1;
                continue;
            }
        }
        try appendCodepointUtf8(allocator, out, u);
    }
}

fn appendCodepointUtf8(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), cp: u32) !void {
    if (cp < 0x80) {
        try out.append(allocator, @intCast(cp));
    } else if (cp < 0x800) {
        try out.append(allocator, @intCast(0xC0 | (cp >> 6)));
        try out.append(allocator, @intCast(0x80 | (cp & 0x3F)));
    } else if (cp < 0x10000) {
        try out.append(allocator, @intCast(0xE0 | (cp >> 12)));
        try out.append(allocator, @intCast(0x80 | ((cp >> 6) & 0x3F)));
        try out.append(allocator, @intCast(0x80 | (cp & 0x3F)));
    } else {
        try out.append(allocator, @intCast(0xF0 | (cp >> 18)));
        try out.append(allocator, @intCast(0x80 | ((cp >> 12) & 0x3F)));
        try out.append(allocator, @intCast(0x80 | ((cp >> 6) & 0x3F)));
        try out.append(allocator, @intCast(0x80 | (cp & 0x3F)));
    }
}

fn writeStdout(io: std.Io, data: []const u8) !void {
    var buf: [4096]u8 = undefined;
    var w = std.Io.File.stdout().writer(io, &buf);
    try w.interface.writeAll(data);
    try w.interface.flush();
}

fn writeStderr(io: std.Io, data: []const u8) !void {
    var buf: [4096]u8 = undefined;
    var w = std.Io.File.stderr().writer(io, &buf);
    try w.interface.writeAll(data);
    try w.interface.flush();
}
