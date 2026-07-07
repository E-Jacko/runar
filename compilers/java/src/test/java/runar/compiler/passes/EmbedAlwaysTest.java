package runar.compiler.passes;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.junit.jupiter.api.Test;
import runar.compiler.frontend.ParserDispatch;
import runar.compiler.ir.ast.ContractNode;
import runar.compiler.ir.ast.PropertyNode;

/**
 * Issue #109 — {@code /** @embedAlways *&#47;} readonly-field DCE opt-out. Port
 * of embed-always.test.ts: parser flag, DCE preservation into a constructor
 * slot (byte parity with the TypeScript reference), and the strip warning.
 */
class EmbedAlwaysTest {

    private static String source(String directive) {
        return "class Meta extends SmartContract {\n"
            + "  readonly pubKeyHash: Addr;\n"
            + "  " + directive + "\n"
            + "  readonly metadataId: ByteString;\n"
            + "  constructor(pubKeyHash: Addr, metadataId: ByteString) {\n"
            + "    super(pubKeyHash, metadataId); this.pubKeyHash = pubKeyHash; this.metadataId = metadataId;\n"
            + "  }\n"
            + "  public unlock(sig: Sig, pubKey: PubKey) {\n"
            + "    assert(hash160(pubKey) === this.pubKeyHash); assert(checkSig(sig, pubKey));\n"
            + "  }\n"
            + "}\n";
    }

    private static PropertyNode prop(ContractNode c, String name) {
        return c.properties().stream().filter(p -> p.name().equals(name)).findFirst().orElseThrow();
    }

    // ---- Parser ---------------------------------------------------------------

    @Test
    void setsEmbedAlwaysOnJsdocDirective() throws Exception {
        ContractNode c = ParserDispatch.parse(source("/** @embedAlways */"), "Meta.runar.ts");
        assertTrue(prop(c, "metadataId").embedAlways());
        assertFalse(prop(c, "pubKeyHash").embedAlways());
    }

    @Test
    void recognizesLineCommentDirective() throws Exception {
        ContractNode c = ParserDispatch.parse(source("// @embedAlways"), "Meta.runar.ts");
        assertTrue(prop(c, "metadataId").embedAlways());
    }

    @Test
    void leavesEmbedAlwaysUnsetWithNoDirective() throws Exception {
        ContractNode c = ParserDispatch.parse(source(""), "Meta.runar.ts");
        assertFalse(prop(c, "metadataId").embedAlways());
    }

    // ---- Preservation (byte parity with the TypeScript reference) ------------

    // Fold-OFF locking-script templates captured from the TS compiler
    // (packages/runar-compiler) compile(src, { disableConstantFolding: true }).scriptHex.
    private static final String TS_PLAIN_HEX = "76a90088ac";
    private static final String TS_EMBED_HEX = "0078a900887b7bac77";

    @Test
    void unannotatedFieldIsEliminated() throws Exception {
        String plain = PipelineTestSupport.hex(source(""), "Meta.runar.ts");
        assertEquals(TS_PLAIN_HEX, plain, "un-annotated template must match the TS reference");
    }

    @Test
    void annotatedFieldIsPreservedByteIdenticalToTs() throws Exception {
        String embed = PipelineTestSupport.hex(source("/** @embedAlways */"), "Meta.runar.ts");
        assertEquals(TS_EMBED_HEX, embed, "@embedAlways template must match the TS reference");
    }

    @Test
    void annotatedHexCarriesMoreBytesThanUnannotated() throws Exception {
        String plain = PipelineTestSupport.hex(source(""), "Meta.runar.ts");
        String embed = PipelineTestSupport.hex(source("/** @embedAlways */"), "Meta.runar.ts");
        assertNotEquals(plain, embed);
        assertTrue(embed.length() > plain.length(), "embed template must carry the extra field bytes");
    }

    // ---- Warning (Option 4) ---------------------------------------------------

    @Test
    void warnsForEliminatedUnannotatedReadonlyField() throws Exception {
        var diags = PipelineTestSupport.diagnostics(source(""), "Meta.runar.ts");
        assertTrue(diags.warnings().stream().anyMatch(w ->
            w.contains("metadataId") && w.contains("eliminated by DCE") && w.contains("@embedAlways")),
            diags.warnings().toString());
    }

    @Test
    void doesNotWarnWhenFieldIsAnnotated() throws Exception {
        var diags = PipelineTestSupport.diagnostics(source("/** @embedAlways */"), "Meta.runar.ts");
        assertFalse(diags.warnings().stream().anyMatch(w -> w.contains("metadataId")),
            diags.warnings().toString());
    }

    @Test
    void doesNotWarnForReferencedReadonlyField() throws Exception {
        String referenced =
            "class P2PKH extends SmartContract {\n"
            + "  readonly pubKeyHash: Addr;\n"
            + "  constructor(pubKeyHash: Addr) { super(pubKeyHash); this.pubKeyHash = pubKeyHash; }\n"
            + "  public unlock(sig: Sig, pubKey: PubKey) {\n"
            + "    assert(hash160(pubKey) === this.pubKeyHash); assert(checkSig(sig, pubKey));\n"
            + "  }\n"
            + "}\n";
        var diags = PipelineTestSupport.diagnostics(referenced, "P2PKH.runar.ts");
        assertFalse(diags.warnings().stream().anyMatch(w -> w.contains("pubKeyHash")),
            diags.warnings().toString());
    }
}
