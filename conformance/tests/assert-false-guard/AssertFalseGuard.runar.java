package runar.conformance.assertfalseguard;

import runar.lang.StatefulSmartContract;
import runar.lang.annotations.Public;
import runar.lang.types.Bigint;
import static runar.lang.Builtins.assertThat;

/**
 * AssertFalseGuard -- the {@code assertThat(false)}-else guard, in the two
 * positions the multi-result branch node originally missed. {@code bump} is a
 * single property written under a guard whose else is the dead abort --
 * recognised as a ONE-branch chain, so excluded from declaring its result, and
 * not rewritten either because the lift only rewrites chains of two or more.
 * {@code dispatch} is {@code Selector}'s exact chain one loop deeper, where the
 * lift never walks.
 */
class AssertFalseGuard extends StatefulSmartContract {

    Bigint count;
    Bigint a;
    Bigint b;

    AssertFalseGuard(Bigint count, Bigint a, Bigint b) {
        super(count, a, b);
        this.count = count;
        this.a = a;
        this.b = b;
    }

    @Public
    void bump(Bigint n) {
        if (n.gt(Bigint.ZERO)) {
            this.count = this.count.plus(n);
        } else {
            assertThat(false);
        }
    }

    @Public
    void dispatch(Bigint sel, Bigint v) {
        for (Bigint i = Bigint.ZERO; i.lt(Bigint.of(2)); i = i.plus(Bigint.ONE)) {
            if (sel.eq(Bigint.ZERO)) {
                this.a = v;
            } else if (sel.eq(Bigint.ONE)) {
                this.b = v;
            } else {
                assertThat(false);
            }
        }
    }
}
