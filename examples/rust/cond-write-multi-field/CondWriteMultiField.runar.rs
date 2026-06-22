use runar::prelude::*;

/// CondWriteMultiField -- regression fixture for GitHub issue #99: a
/// conditional write of two mutable state fields in an `if` without an `else`.
#[runar::contract]
pub struct CondWriteMultiField {
    pub a: Bigint,
    pub b: Bigint,
}

impl CondWriteMultiField {
    pub fn bump(&mut self, flag: Bigint) {
        if flag > 0 {
            self.a = self.a + 1;
            self.b = self.b + 2;
        }
        self.add_output(1000, self.a, self.b);
    }
}
