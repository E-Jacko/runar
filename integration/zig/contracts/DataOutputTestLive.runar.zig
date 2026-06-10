const runar = @import("runar");

// Integration-only variant of examples/zig/add-data-output/DataOutputTest
// whose publish() emits a 1-satoshi (not 0) data output. The CI regtest node
// runs with acceptnonstdtxn=0 (oracle hardening, PR #49) and rejects
// 0-satoshi OP_RETURN outputs as "dust" at sendrawtransaction. The shared
// example contract is conformance-linked (conformance/tests/add-data-output),
// so it is deliberately left at 0 to keep its cross-tier hex goldens frozen;
// this dedicated source preserves the live-broadcast assertion without that
// golden churn. The 0-sat form remains valid on mainnet/ARC.
pub const DataOutputTest = struct {
    pub const Contract = runar.StatefulSmartContract;

    count: i64 = 0,

    pub fn init(count: i64) DataOutputTest {
        return .{ .count = count };
    }

    pub fn publish(self: *DataOutputTest, payload: runar.ByteString) void {
        self.count = self.count + 1;
        self.addDataOutput(1, payload);
    }
};
