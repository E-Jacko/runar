const std = @import("std");
const helpers = @import("helpers.zig");

// Only Phase A residual tests (not the full integration suite).
comptime {
    _ = @import("phase_a_residuals_test.zig");
    _ = @import("compile.zig");
}

test "phase_a_only_setup" {
    const allocator = std.testing.allocator;
    helpers.requireNodeAvailable(allocator);
    std.debug.print("\nZIG_PHASE_A_SUITE_START\n", .{});
}
