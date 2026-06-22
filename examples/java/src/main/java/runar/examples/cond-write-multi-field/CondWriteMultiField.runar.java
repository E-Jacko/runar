package runar.examples.condwritemultifield;

import runar.lang.StatefulSmartContract;
import runar.lang.annotations.Public;
import runar.lang.types.Bigint;

/**
 * CondWriteMultiField -- regression fixture for GitHub issue #99: a
 * conditional write of two mutable state fields in an {@code if} without an
 * {@code else}.
 */
class CondWriteMultiField extends StatefulSmartContract {

    Bigint a;
    Bigint b;

    CondWriteMultiField(Bigint a, Bigint b) {
        super(a, b);
        this.a = a;
        this.b = b;
    }

    @Public
    void bump(Bigint flag) {
        if (flag.gt(Bigint.ZERO)) {
            this.a = this.a.plus(Bigint.ONE);
            this.b = this.b.plus(Bigint.of(2));
        }
        this.addOutput(1000L, this.a, this.b);
    }
}
