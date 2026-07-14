pragma runar ^0.1.0;

/// @title CondWriteMultiField
/// @notice Regression fixture for GitHub issue #99 -- a conditional write of
/// two mutable state fields in an `if` without an `else`.
contract CondWriteMultiField is StatefulSmartContract {
    bigint a;
    bigint b;

    constructor(bigint _a, bigint _b) {
        a = _a;
        b = _b;
    }

    function bump(bigint flag) public {
        if (flag > 0) {
            this.a = this.a + 1;
            this.b = this.b + 2;
        }
        this.addOutput(1000, this.a, this.b);
    }
}
