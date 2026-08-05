package runar.compiler.ir.anf;

/**
 * The right-hand side of a single ANF {@code let}-binding. Sealed over
 * the full set of value kinds from
 * {@code packages/runar-ir-schema/src/anf-ir.ts}.
 */
public sealed interface AnfValue
    permits LoadParam, LoadProp, LoadConst, BinOp, UnaryOp, Call, MethodCall,
            If, Loop, Assert, UpdateProp, GetStateScript, CheckPreimage,
            DeserializeState, AddOutput, AddRawOutput, AddDataOutput,
            ArrayLiteral, RawScript,
            // Test-only stub used by UnknownAnfKindTest to drive every
            // dispatcher with a kind that is not in the production schema.
            // No production dispatch site handles this variant — that is
            // the whole point of the F-003 regression guard.
            SyntheticAnfValueForTests {
    /**
     * Name prefix for the temporaries ANF lowering appends to BOTH arms of an
     * if-statement that merges two or more locals.
     *
     * <p>An {@code if} carries one value, so post-branch references to a
     * merged local can only be rewired by aliasing when there is exactly ONE of
     * them. For two or more, both arms instead end with an identical K-binding
     * block — K copies into {@code __merge$0..K-1}, then K rebinds of the
     * locals from those temps — which leaves the merged values on top in the
     * same canonical order whichever branch runs. Stack lowering recognises
     * that trailing block by this prefix, trims each arm down to the K results,
     * and adopts them by name.
     *
     * <p>The prefix is part of the ANF wire format: all seven compilers emit
     * and recognise the same block.
     */
    String MERGED_LOCAL_TEMP_PREFIX = "__merge$";

    String kind();
}
