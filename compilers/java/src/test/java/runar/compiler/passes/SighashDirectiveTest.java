package runar.compiler.passes;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.junit.jupiter.api.Test;
import runar.compiler.passes.SighashDirective.Result;

/** Issue #123 — {@code @sighash} flag grammar (port of sighash-directive.test.ts). */
class SighashDirectiveTest {

    private static int value(String flags) {
        Result r = SighashDirective.parseSighashFlags(flags);
        assertFalse(r.isError(), () -> "unexpected error: " + r.error());
        return r.value();
    }

    @Test
    void parsesCommonSingleBaseCombos() {
        assertEquals(0x41, value("ALL|FORKID"));
        assertEquals(0x43, value("SINGLE|FORKID"));
        assertEquals(0x42, value("NONE|FORKID"));
        assertEquals(0xc1, value("ALL|ANYONECANPAY|FORKID"));
    }

    @Test
    void orderIndependentAndWhitespaceTolerant() {
        assertEquals(0x43, value(" FORKID | SINGLE "));
    }

    @Test
    void defaultConstantIsAllForkid() {
        assertEquals(0x41, SighashDirective.SIGHASH_DEFAULT);
        assertEquals(SighashDirective.SIGHASH_DEFAULT, value("ALL|FORKID"));
    }

    @Test
    void rejectsUnknownFlag() {
        Result r = SighashDirective.parseSighashFlags("ALL|FORKD");
        assertTrue(r.isError());
        assertTrue(r.error().contains("unknown flag \"FORKD\""), r.error());
    }

    @Test
    void rejectsAllNoneComboOnNames() {
        Result r = SighashDirective.parseSighashFlags("ALL|NONE|FORKID");
        assertTrue(r.isError());
        assertTrue(r.error().contains("cannot combine base types"), r.error());
    }

    @Test
    void rejectsTwoBaseTypes() {
        assertTrue(SighashDirective.parseSighashFlags("SINGLE|ALL").isError());
    }

    @Test
    void rejectsNoBaseType() {
        Result r = SighashDirective.parseSighashFlags("FORKID|ANYONECANPAY");
        assertTrue(r.isError());
        assertTrue(r.error().contains("exactly one base type"), r.error());
    }

    @Test
    void rejectsDuplicateFlags() {
        Result r = SighashDirective.parseSighashFlags("SINGLE|SINGLE|FORKID");
        assertTrue(r.isError());
        assertTrue(r.error().contains("duplicate flag"), r.error());
    }

    @Test
    void rejectsEmptyFlagLists() {
        assertTrue(SighashDirective.parseSighashFlags("").isError());
        assertTrue(SighashDirective.parseSighashFlags("   ").isError());
    }

    @Test
    void rejectsBaseTypeWithoutForkid() {
        for (String flags : new String[] {"SINGLE", "ALL", "NONE", "ALL|ANYONECANPAY"}) {
            Result r = SighashDirective.parseSighashFlags(flags);
            assertTrue(r.isError(), flags);
            assertTrue(r.error().contains("FORKID is mandatory on BSV"), r.error());
        }
    }

    @Test
    void acceptsSameFlagSetsOnceForkidAdded() {
        assertEquals(0x43, value("SINGLE|FORKID"));
        assertEquals(0xc1, value("ALL|ANYONECANPAY|FORKID"));
    }

    @Test
    void extractsFromCommentText() {
        assertEquals(0x43, SighashDirective.extractSighashDirective("/** @sighash SINGLE|FORKID */").value());
        assertEquals(0x42, SighashDirective.extractSighashDirective("// @sighash NONE|FORKID").value());
        assertNull(SighashDirective.extractSighashDirective("/** no directive here */"));
    }

    @Test
    void describeSighashRoundTrips() {
        assertEquals("ALL|FORKID", SighashDirective.describeSighash(0x41));
        assertEquals("SINGLE|FORKID", SighashDirective.describeSighash(0x43));
        assertEquals("ALL|ANYONECANPAY|FORKID", SighashDirective.describeSighash(0xc1));
        assertEquals("NONE|FORKID", SighashDirective.describeSighash(0x42));
    }
}
