// CondWriteMultiField -- regression fixture for GitHub issue #99: a
// conditional write of two mutable state fields in an `if` without an `else`.
module CondWriteMultiField {
    resource struct CondWriteMultiField {
        a: &mut bigint,
        b: &mut bigint,
    }

    public fun bump(contract: &mut CondWriteMultiField, flag: bigint) {
        if (flag > 0) {
            contract.a = contract.a + 1;
            contract.b = contract.b + 2;
        };
        contract.addOutput(1000, contract.a, contract.b);
    }
}
