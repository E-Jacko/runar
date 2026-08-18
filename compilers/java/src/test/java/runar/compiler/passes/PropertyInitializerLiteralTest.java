package runar.compiler.passes;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.Test;
import runar.compiler.frontend.ParserDispatch;
import runar.compiler.ir.ast.ContractNode;

/**
 * Audit C3 — property initializers are restricted to literal values.
 *
 * <p>{@code ts}, {@code go} and {@code java} enforced this; {@code rust},
 * {@code zig}, {@code python} and {@code ruby} did not — they compiled e.g.
 * {@code p: bigint = 1n + 2n;} and emitted a deployable locking script for a
 * program the language does not define.
 *
 * <p>Mirrors {@code packages/runar-compiler/src/__tests__/property-initializer-literal.test.ts}.
 */
class PropertyInitializerLiteralTest {

    /** The cross-tier diagnostic substring. */
    private static final String NON_LITERAL_INIT = "initializer must be a literal value";

    private static Validate.Result validateSource(String source, String fileName) throws Exception {
        ContractNode c = ParserDispatch.parse(source, fileName);
        return Validate.runCollecting(c);
    }

    private static void assertNonLiteralInitError(Validate.Result r) {
        assertTrue(
            r.errors().stream().anyMatch(m -> m.contains(NON_LITERAL_INIT)),
            "expected a non-literal-initializer error, got: " + r.errors()
        );
    }

    @Test
    void rejectsArithmeticPropertyInitializer() throws Exception {
        String src = """
            import { StatefulSmartContract, Addr } from 'runar-lang';

            class Bad extends StatefulSmartContract {
              count: bigint = 1n + 2n;
              readonly owner: Addr;

              constructor(owner: Addr) {
                super(owner);
                this.owner = owner;
              }

              public bump() {
                this.count = this.count + 1n;
              }
            }
            """;
        assertNonLiteralInitError(validateSource(src, "Bad.runar.ts"));
    }

    @Test
    void rejectsCallExpressionPropertyInitializer() throws Exception {
        String src = """
            import { StatefulSmartContract, Addr } from 'runar-lang';

            class Bad2 extends StatefulSmartContract {
              count: bigint = abs(-3n);
              readonly owner: Addr;

              constructor(owner: Addr) {
                super(owner);
                this.owner = owner;
              }

              public bump() {
                this.count = this.count + 1n;
              }
            }
            """;
        assertNonLiteralInitError(validateSource(src, "Bad2.runar.ts"));
    }

    @Test
    void acceptsLiteralPropertyInitializers() throws Exception {
        String src = """
            import { StatefulSmartContract, Addr, ByteString } from 'runar-lang';

            class Good extends StatefulSmartContract {
              count: bigint = 7n;
              flag: boolean = true;
              tag: ByteString = 'deadbeef';
              offset: bigint = -3n;
              readonly owner: Addr;

              constructor(owner: Addr) {
                super(owner);
                this.owner = owner;
              }

              public bump() {
                this.count = this.count + 1n;
              }
            }
            """;
        Validate.Result r = validateSource(src, "Good.runar.ts");
        assertTrue(r.errors().isEmpty(), "expected no errors, got: " + r.errors());
    }
}
