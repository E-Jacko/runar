package runar.compiler.ir.anf;

import java.util.List;
import runar.compiler.canonical.JsonName;

/**
 * The {@code else} branch uses a Java-safe component name
 * ({@code elseBranch}) because {@code else} is a reserved keyword;
 * serialisation emits it under the {@code else} key.
 */
public record If(
    String cond,
    @JsonName("then") List<AnfBinding> thenBranch,
    @JsonName("else") List<AnfBinding> elseBranch,
    /**
     * Ordered named result slots both arms leave ({@code results[0]} deepest).
     * Entries name a branch-merged local or an arm-written contract property;
     * stack lowering tells the two apart from the contract's property list, so
     * the wire format stays a plain array of strings. {@code null} (not an
     * empty list) when the {@code if} carries at most one result — see the
     * TypeScript reference in {@code packages/runar-compiler/src/ir/anf-ir.ts}
     * for the full contract.
     */
    List<String> results
) implements AnfValue {
    /** Convenience constructor for an {@code if} with no declared results. */
    public If(String cond, List<AnfBinding> thenBranch, List<AnfBinding> elseBranch) {
        this(cond, thenBranch, elseBranch, null);
    }

    @Override
    public String kind() {
        return "if";
    }
}
