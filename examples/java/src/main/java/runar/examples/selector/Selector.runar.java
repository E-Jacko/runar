package runar.examples.selector;

import runar.lang.StatefulSmartContract;
import runar.lang.annotations.Public;
import runar.lang.types.Bigint;
import static runar.lang.Builtins.assertThat;

/**
 * Selector -- regression fixture for deep-review finding C20: a dispatch method
 * whose branches each end in a single state update and whose terminal
 * {@code else} is {@code assertThat(false)}. The abort must survive ANF
 * lowering so an out-of-range selector fails the script instead of producing a
 * spendable no-op state continuation.
 */
class Selector extends StatefulSmartContract {

    Bigint a;
    Bigint b;

    Selector(Bigint a, Bigint b) {
        super(a, b);
        this.a = a;
        this.b = b;
    }

    @Public
    void set(Bigint i, Bigint v) {
        if (i.eq(Bigint.ZERO)) {
            this.a = v;
        } else if (i.eq(Bigint.ONE)) {
            this.b = v;
        } else {
            assertThat(false);
        }
    }
}
