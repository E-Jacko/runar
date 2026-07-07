package runar.compiler.frontend;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.junit.jupiter.api.Test;
import runar.compiler.frontend.ParserDispatch.ParseException;

/**
 * Fail-closed guard for the author-facing comment directives that only the
 * TypeScript compiler implements: {@code @sighash} (#123) and
 * {@code @embedAlways} (#109). The Java compiler must reject them rather than
 * silently drop them.
 */
class DirectiveGuardTest {

    @Test
    void rejectsSighashDirective() {
        String src =
            "class Counter extends SmartContract {\n"
            + "  readonly x: bigint;\n"
            + "  constructor(x: bigint) { super(x); this.x = x; }\n"
            + "  /** @sighash SINGLE|FORKID */\n"
            + "  public unlock() {}\n"
            + "}\n";
        ParseException ex = assertThrows(
            ParseException.class,
            () -> ParserDispatch.parse(src, "Counter.runar.ts"));
        assertTrue(ex.getMessage().contains("@sighash"), ex.getMessage());
        assertTrue(ex.getMessage().contains("#123"), ex.getMessage());
    }

    @Test
    void rejectsEmbedAlwaysDirective() {
        String src =
            "class Counter extends SmartContract {\n"
            + "  /** @embedAlways */\n"
            + "  readonly x: bigint;\n"
            + "  constructor(x: bigint) { super(x); this.x = x; }\n"
            + "  public unlock() {}\n"
            + "}\n";
        ParseException ex = assertThrows(
            ParseException.class,
            () -> ParserDispatch.parse(src, "Counter.runar.ts"));
        assertTrue(ex.getMessage().contains("@embedAlways"), ex.getMessage());
        assertTrue(ex.getMessage().contains("#109"), ex.getMessage());
    }

    @Test
    void doesNotTripOnNonDirectiveIdentifier() {
        // A field named `sighashType` must NOT trip the word-boundary guard.
        // The TS parser may still raise its own errors; we only assert the
        // directive guard message is not the failure reason.
        String src =
            "class Counter extends SmartContract {\n"
            + "  readonly sighashType: bigint;\n"
            + "  constructor(sighashType: bigint) { super(sighashType); this.sighashType = sighashType; }\n"
            + "  public unlock() {}\n"
            + "}\n";
        try {
            ParserDispatch.parse(src, "Counter.runar.ts");
        } catch (Exception e) {
            assertTrue(!e.getMessage().contains("not yet supported"),
                "directive guard tripped on a non-directive identifier: " + e.getMessage());
        }
    }
}
