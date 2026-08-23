use runar::prelude::*;

/// OversizeBigintShift -- a length-sensitive byte op whose operand is a bigint
/// const too large for a JSON number (NEW-008). `9007199254740993` is 2^53 + 1,
/// one past `Number.MAX_SAFE_INTEGER`, so the conformance runner cannot narrow
/// it back to a JSON number and the checked-in `expected-ir.json` really does
/// pin the `"<n>n"` STRING form that `runar-cli compile` writes to disk. On
/// chain the operand is the 7-byte script number `01 00 00 00 00 00 20`,
/// `OP_LSHIFT` is length-preserving, and `OP_INVERT` flips all seven bytes.
#[runar::stateful_contract]
pub struct OversizeBigintShift {
    pub out: Bigint,
}

impl OversizeBigintShift {
    /// Write the inverted, shifted oversize constant to state.
    pub fn shift(&mut self) {
        self.out = ~(9007199254740993 << 8);
    }
}
