package runar.compiler.passes;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.Test;
import runar.compiler.frontend.ParserDispatch;
import runar.compiler.ir.ast.ContractNode;

/**
 * Audit C2 — {@code readonly} property assignment must be rejected outside the
 * constructor.
 *
 * <p>{@code spec/semantics.md:247}:
 * {@code <this.p = e, env, sigma> ==> ERROR: cannot assign to readonly property}
 *
 * <p>Without the rule a contract that reassigns its readonly owner before
 * checking it compiles to {@code 76a97ca9788777} — hash160(pk) compared against
 * hash160(pk), true for ANY pubkey, i.e. anyone can spend.
 *
 * <p>The constructor MUST still be allowed to assign readonly properties.
 *
 * <p>Mirrors {@code packages/runar-compiler/src/__tests__/readonly-property-assignment.test.ts}.
 */
class ReadonlyPropertyAssignmentTest {

    /** The cross-tier diagnostic substring. */
    private static final String READONLY_WRITE = "assign to readonly property";

    private static Validate.Result validateSource(String source, String fileName) throws Exception {
        ContractNode c = ParserDispatch.parse(source, fileName);
        return Validate.runCollecting(c);
    }

    private static void assertReadonlyWriteError(Validate.Result r) {
        assertTrue(
            r.errors().stream().anyMatch(m -> m.contains(READONLY_WRITE)),
            "expected a readonly-write error, got: " + r.errors()
        );
    }

    @Test
    void rejectsOwnerHijackContract() throws Exception {
        String src = """
            import { SmartContract, Addr, PubKey } from 'runar-lang';

            class Hijack extends SmartContract {
              readonly ownerHash: Addr;

              constructor(ownerHash: Addr) {
                super(ownerHash);
                this.ownerHash = ownerHash;
              }

              public unlock(attackerPk: PubKey) {
                this.ownerHash = hash160(attackerPk);
                assert(hash160(attackerPk) === this.ownerHash);
              }
            }
            """;
        Validate.Result r = validateSource(src, "Hijack.runar.ts");
        assertReadonlyWriteError(r);
        assertTrue(
            r.errors().stream().anyMatch(m -> m.contains("'ownerHash'")),
            "expected the offending property name, got: " + r.errors()
        );
    }

    @Test
    void rejectsReadonlyWriteInStatefulMethod() throws Exception {
        String src = """
            import { StatefulSmartContract, Addr } from 'runar-lang';

            class Vault extends StatefulSmartContract {
              readonly owner: Addr;
              count: bigint;

              constructor(owner: Addr, count: bigint) {
                super(owner, count);
                this.owner = owner;
                this.count = count;
              }

              public bump(newOwner: Addr) {
                this.owner = newOwner;
                this.count = this.count + 1n;
              }
            }
            """;
        assertReadonlyWriteError(validateSource(src, "Vault.runar.ts"));
    }

    @Test
    void rejectsReadonlyWriteNestedInIf() throws Exception {
        String src = """
            import { StatefulSmartContract, Addr } from 'runar-lang';

            class Nested extends StatefulSmartContract {
              readonly owner: Addr;
              count: bigint;

              constructor(owner: Addr, count: bigint) {
                super(owner, count);
                this.owner = owner;
                this.count = count;
              }

              public bump(newOwner: Addr, flag: boolean) {
                if (flag) {
                  this.owner = newOwner;
                } else {
                  this.count = this.count + 1n;
                }
              }
            }
            """;
        assertReadonlyWriteError(validateSource(src, "Nested.runar.ts"));
    }

    @Test
    void rejectsReadonlyWriteInPrivateHelper() throws Exception {
        String src = """
            import { StatefulSmartContract, Addr } from 'runar-lang';

            class Helper extends StatefulSmartContract {
              readonly owner: Addr;
              count: bigint;

              constructor(owner: Addr, count: bigint) {
                super(owner, count);
                this.owner = owner;
                this.count = count;
              }

              private steal(newOwner: Addr): void {
                this.owner = newOwner;
              }

              public bump(newOwner: Addr) {
                this.steal(newOwner);
                this.count = this.count + 1n;
              }
            }
            """;
        assertReadonlyWriteError(validateSource(src, "Helper.runar.ts"));
    }

    @Test
    void rejectsIncrementOfReadonlyProperty() throws Exception {
        String src = """
            import { StatefulSmartContract } from 'runar-lang';

            class Bump extends StatefulSmartContract {
              readonly limit: bigint;
              count: bigint;

              constructor(limit: bigint, count: bigint) {
                super(limit, count);
                this.limit = limit;
                this.count = count;
              }

              public go() {
                this.limit++;
                this.count = this.count + 1n;
              }
            }
            """;
        assertReadonlyWriteError(validateSource(src, "Bump.runar.ts"));
    }

    @Test
    void rejectsPythonSurfaceHijackContract() throws Exception {
        String src = """
            from runar import SmartContract, assert_, hash160, Readonly, ByteString, PubKey

            class Hijack(SmartContract):
                owner_hash: Readonly[ByteString]

                def __init__(self, owner_hash: ByteString):
                    super().__init__(owner_hash)
                    self.owner_hash = owner_hash

                @public
                def unlock(self, attacker_pk: PubKey):
                    self.owner_hash = hash160(attacker_pk)
                    assert_(hash160(attacker_pk) == self.owner_hash)
            """;
        assertReadonlyWriteError(validateSource(src, "Hijack.runar.py"));
    }

    @Test
    void rejectsJavaSurfaceHijackContract() throws Exception {
        String src = """
            class Hijack extends SmartContract {
                @Readonly Addr ownerHash;

                Hijack(Addr ownerHash) {
                    super(ownerHash);
                    this.ownerHash = ownerHash;
                }

                @Public
                void unlock(PubKey attackerPk) {
                    this.ownerHash = hash160(attackerPk);
                    assertThat(hash160(attackerPk).equals(ownerHash));
                }
            }
            """;
        assertReadonlyWriteError(validateSource(src, "Hijack.runar.java"));
    }

    // -------------------------------------------------------------------------
    // The constructor must keep working — every contract assigns its readonly
    // properties there.
    // -------------------------------------------------------------------------

    @Test
    void acceptsReadonlyAssignmentInConstructor() throws Exception {
        String src = """
            import { SmartContract, Addr, PubKey, Sig } from 'runar-lang';

            class P2PKH extends SmartContract {
              readonly pubKeyHash: Addr;

              constructor(pubKeyHash: Addr) {
                super(pubKeyHash);
                this.pubKeyHash = pubKeyHash;
              }

              public unlock(sig: Sig, pubKey: PubKey) {
                assert(hash160(pubKey) === this.pubKeyHash);
                assert(checkSig(sig, pubKey));
              }
            }
            """;
        Validate.Result r = validateSource(src, "P2PKH.runar.ts");
        assertTrue(r.errors().isEmpty(), "expected no errors, got: " + r.errors());
    }

    @Test
    void acceptsMutableStateMutation() throws Exception {
        String src = """
            import { StatefulSmartContract, Addr } from 'runar-lang';

            class Counter extends StatefulSmartContract {
              readonly owner: Addr;
              count: bigint;

              constructor(owner: Addr, count: bigint) {
                super(owner, count);
                this.owner = owner;
                this.count = count;
              }

              public increment() {
                this.count = this.count + 1n;
              }
            }
            """;
        Validate.Result r = validateSource(src, "Counter.runar.ts");
        assertTrue(r.errors().isEmpty(), "expected no errors, got: " + r.errors());
    }

    @Test
    void acceptsLocalShadowingAReadonlyPropertyName() throws Exception {
        String src = """
            import { StatefulSmartContract } from 'runar-lang';

            class Shadow extends StatefulSmartContract {
              readonly limit: bigint;
              count: bigint;

              constructor(limit: bigint, count: bigint) {
                super(limit, count);
                this.limit = limit;
                this.count = count;
              }

              public increment() {
                let limit: bigint = 5n;
                limit = 6n;
                assert(this.count < limit);
                this.count = this.count + 1n;
              }
            }
            """;
        Validate.Result r = validateSource(src, "Shadow.runar.ts");
        assertTrue(r.errors().isEmpty(), "expected no errors, got: " + r.errors());
    }
}
