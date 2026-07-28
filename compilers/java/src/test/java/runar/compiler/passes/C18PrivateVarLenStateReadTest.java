package runar.compiler.passes;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

import org.junit.jupiter.api.Test;

/**
 * Regression test for deep-review finding C18 (P1 funds-safety bug).
 *
 * <p>{@code StackLower.methodReadsVarLenState} used to walk only a method's OWN
 * bindings (plus {@code if}/{@code loop} bodies) looking for a direct
 * {@code load_prop} on a mutable variable-length (ByteString) state field. It did
 * NOT recurse into private helper methods invoked via {@code method_call} — unlike
 * its sibling walker {@code methodUsesCheckPreimage}, which already did.
 *
 * <p>Consequence: a PUBLIC method that reads a mutable ByteString state field ONLY
 * through a PRIVATE helper never set {@code usesCodePart}, so {@code _codePart} was
 * never pushed as an implicit parameter and the var-length deserialization was
 * skipped. The private helper's {@code load_prop} then fell back to the deploy-time
 * constant instead of the live on-chain state — a silent wrong-result bug.
 */
class C18PrivateVarLenStateReadTest {

    /** Control: the public method reads the mutable ByteString field directly. */
    private static final String DIRECT =
        "import { StatefulSmartContract, assert, len } from 'runar-lang';\n"
        + "import type { ByteString } from 'runar-lang';\n"
        + "class StateReadDirect extends StatefulSmartContract {\n"
        + "  tag: ByteString;\n"
        + "  constructor(tag: ByteString) { super(tag); this.tag = tag; }\n"
        + "  public check(expected: bigint): void { assert(len(this.tag) === expected); }\n"
        + "}\n";

    /** Bug case: the public method reads the same field ONLY via a private helper. */
    private static final String VIA_HELPER =
        "import { StatefulSmartContract, assert, len } from 'runar-lang';\n"
        + "import type { ByteString } from 'runar-lang';\n"
        + "class StateReadDirect extends StatefulSmartContract {\n"
        + "  tag: ByteString;\n"
        + "  constructor(tag: ByteString) { super(tag); this.tag = tag; }\n"
        + "  private tagLen(): bigint { return len(this.tag); }\n"
        + "  public check(expected: bigint): void { assert(this.tagLen() === expected); }\n"
        + "}\n";

    /** Two private helpers calling each other must not hang the cycle guard. */
    private static final String VIA_HELPER_CHAIN =
        "import { StatefulSmartContract, assert, len } from 'runar-lang';\n"
        + "import type { ByteString } from 'runar-lang';\n"
        + "class StateReadDirect extends StatefulSmartContract {\n"
        + "  tag: ByteString;\n"
        + "  constructor(tag: ByteString) { super(tag); this.tag = tag; }\n"
        + "  private inner(): bigint { return len(this.tag); }\n"
        + "  private outer(): bigint { return this.inner(); }\n"
        + "  public check(expected: bigint): void { assert(this.outer() === expected); }\n"
        + "}\n";

    /** No var-length read at all — must keep the original terminal codegen. */
    private static final String NO_VARLEN_READ =
        "import { StatefulSmartContract, assert } from 'runar-lang';\n"
        + "import type { ByteString } from 'runar-lang';\n"
        + "class StateReadDirect extends StatefulSmartContract {\n"
        + "  tag: ByteString;\n"
        + "  constructor(tag: ByteString) { super(tag); this.tag = tag; }\n"
        + "  private twice(x: bigint): bigint { return x + x; }\n"
        + "  public check(expected: bigint): void { assert(this.twice(expected) === expected + expected); }\n"
        + "}\n";

    @Test
    void readViaPrivateHelperMatchesDirectRead() throws Exception {
        String direct = PipelineTestSupport.hex(DIRECT, "StateReadDirect.runar.ts");
        String viaHelper = PipelineTestSupport.hex(VIA_HELPER, "StateReadDirect.runar.ts");
        assertEquals(direct, viaHelper,
            "reading a mutable ByteString field through a private helper must lower "
            + "identically to reading it directly (both need _codePart)");
    }

    @Test
    void readViaChainedPrivateHelpersMatchesDirectRead() throws Exception {
        String direct = PipelineTestSupport.hex(DIRECT, "StateReadDirect.runar.ts");
        String viaChain = PipelineTestSupport.hex(VIA_HELPER_CHAIN, "StateReadDirect.runar.ts");
        assertEquals(direct, viaChain,
            "transitive private-helper reads must also force _codePart");
    }

    @Test
    void methodWithoutVarLenReadKeepsTerminalCodegen() throws Exception {
        String direct = PipelineTestSupport.hex(DIRECT, "StateReadDirect.runar.ts");
        String noRead = PipelineTestSupport.hex(NO_VARLEN_READ, "StateReadDirect.runar.ts");
        assertNotEquals(direct, noRead,
            "a method that never reads the mutable ByteString field must NOT gain _codePart");
    }
}
