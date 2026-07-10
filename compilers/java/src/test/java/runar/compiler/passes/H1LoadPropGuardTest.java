package runar.compiler.passes;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.List;
import org.junit.jupiter.api.Test;
import runar.compiler.ir.anf.AnfBinding;
import runar.compiler.ir.anf.AnfMethod;
import runar.compiler.ir.anf.AnfProgram;
import runar.compiler.ir.anf.AnfProperty;
import runar.compiler.ir.anf.Assert;
import runar.compiler.ir.anf.LoadProp;
import runar.compiler.ir.ast.SourceLocation;

/**
 * H1 (#119 tail): {@code lowerLoadProp} must NOT silently coerce an unknown
 * property onto constructor slot 0.
 *
 * <p>A {@code load_prop} binding whose name is not a declared constructor-param
 * property used to fall through to {@code paramIndex >= 0 ? paramIndex : 0},
 * emitting the placeholder for constructor slot 0 — an UNRELATED argument's
 * deploy-time bytes — with no diagnostic. That is a silent-wrong-code path: the
 * produced locking script splices the wrong value at that position.
 *
 * <p>The hardened behaviour is a HARD ERROR ({@link RuntimeException}) with a
 * clear diagnostic and the binding's source location, instead of the silent
 * placeholder. A real constructor-param property (readonly, or a mutable state
 * field spliced at deploy) is still lowered without error.
 *
 * <p>Port of {@code remediation-h1-loadprop-guard.test.ts}.
 */
class H1LoadPropGuardTest {

    /**
     * Minimal ANF program with a real readonly constructor-param property
     * {@code pk} (constructor slot 0) plus a public method that loads a
     * property {@code ghost} that is NOT declared on the contract. {@code ghost}
     * therefore reaches the placeholder fallback with no matching slot.
     */
    private static AnfProgram programWithUnknownLoadProp() {
        AnfMethod spend = new AnfMethod(
            "spend",
            List.of(),
            List.of(
                new AnfBinding("t0", new LoadProp("ghost"),
                    new SourceLocation("Ghost.runar.java", 7, 4)),
                new AnfBinding("t1", new Assert("t0"), null)
            ),
            true);
        return new AnfProgram(
            "Ghost",
            List.of(new AnfProperty("pk", "PubKey", true, null)),
            List.of(spend));
    }

    @Test
    void throwsOnLoadPropForPropertyWithNoConstructorSlot() {
        assertThrows(RuntimeException.class,
            () -> StackLower.run(programWithUnknownLoadProp()));
    }

    @Test
    void includesOffendingNameAndSourceLocationInDiagnostic() {
        RuntimeException err = assertThrows(RuntimeException.class,
            () -> StackLower.run(programWithUnknownLoadProp()));
        String message = err.getMessage();
        assertTrue(message.contains("ghost"),
            "diagnostic must name the offending property; got: " + message);
        assertTrue(message.contains("Ghost.runar.java"),
            "diagnostic must include the source file; got: " + message);
        assertTrue(message.contains("7"),
            "diagnostic must include the source line; got: " + message);
        // The list of legit constructor-param properties is surfaced so the
        // author can see what WAS resolvable.
        assertTrue(message.contains("pk"),
            "diagnostic must list the known constructor-param properties; got: " + message);
    }

    @Test
    void lowersRealConstructorParamPropertyWithoutError() {
        AnfMethod spend = new AnfMethod(
            "spend",
            List.of(),
            List.of(
                new AnfBinding("t0", new LoadProp("pk"), null),
                new AnfBinding("t1", new Assert("t0"), null)
            ),
            true);
        AnfProgram program = new AnfProgram(
            "Ok",
            List.of(new AnfProperty("pk", "PubKey", true, null)),
            List.of(spend));
        assertDoesNotThrow(() -> StackLower.run(program));
    }
}
