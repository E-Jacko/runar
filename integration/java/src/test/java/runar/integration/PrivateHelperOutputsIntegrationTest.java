package runar.integration;

import java.io.IOException;
import java.math.BigInteger;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import runar.integration.helpers.ContractCompiler;
import runar.integration.helpers.IntegrationBase;
import runar.integration.helpers.IntegrationWallet;
import runar.integration.helpers.RpcProvider;
import runar.lang.sdk.RunarArtifact;
import runar.lang.sdk.RunarContract;

import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * PrivateHelperOutputs integration test — 2026-04-30 audit regression
 * (F1 + F3).
 *
 * <p>The contract delegates state mutation, addDataOutput, and
 * addOutput to private helpers. Before the F1 fix the auto-injection
 * was a shallow scan of the public method body, so these methods
 * were silently classified as terminal and the deploy + call cycle
 * would fail.
 *
 * <p>Mirrors the TS / Go / Rust / Python / Ruby / Zig integration
 * tests for the same contract.
 */
class PrivateHelperOutputsIntegrationTest extends IntegrationBase {

    // Inline private-helper variant whose record() helper emits a 1-satoshi
    // (not 0) data output. The CI regtest node runs with acceptnonstdtxn=0
    // (oracle hardening, PR #49) and rejects 0-satoshi OP_RETURN outputs as
    // "dust" at sendrawtransaction. The shared conformance contract
    // (examples/ts/private-helper-outputs/PrivateHelperOutputs.runar.ts) is
    // deliberately left at 0n so its cross-tier hex goldens stay frozen; this
    // inline source preserves the exact "data output routed through a private
    // helper, broadcast to a live node" assertion without that golden churn.
    private static final String LOG_SOURCE = """
        import { StatefulSmartContract, ByteString, assert } from 'runar-lang';

        export class PrivateHelperLog extends StatefulSmartContract {
            counter: bigint;

            constructor(counter: bigint) {
                super(counter);
                this.counter = counter;
            }

            private record(payload: ByteString): void {
                this.addDataOutput(1n, payload);
            }

            public log(payload: ByteString): void {
                this.record(payload);
                assert(true);
            }
        }
        """;

    @Test
    @DisplayName("commit chain: three sequential calls each spend the previous continuation")
    void commitChain() {
        // Failure here means the runtime hashOutputs hash didn't
        // match the compiled continuation — exactly what F1's
        // shallow-scan miss would produce for state-mutation routed
        // through a private helper.
        RunarArtifact artifact = ContractCompiler.compileRelative(
            "examples/ts/private-helper-outputs/PrivateHelperOutputs.runar.ts"
        );

        RpcProvider provider = new RpcProvider(rpc);
        IntegrationWallet wallet = IntegrationWallet.createFunded(rpc, 1.0);

        RunarContract contract = new RunarContract(
            artifact, List.of(BigInteger.ZERO)
        );
        contract.deploy(provider, wallet.signer(), 5_000L);

        for (int i = 0; i < 3; i++) {
            RunarContract.CallOutcome out = contract.call(
                "commit", List.of(), null, provider, wallet.signer()
            );
            assertNotNull(out.txid(), "commit #" + (i + 1) + ": empty txid");
        }
    }

    @Test
    @DisplayName("log() routes a data output through a private helper")
    void logEmitsDataOutput() {
        Path tmp;
        try {
            tmp = Files.createTempFile("runar-private-helper-log-", "PrivateHelperLog.runar.ts");
            Files.writeString(tmp, LOG_SOURCE);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        RunarArtifact artifact = ContractCompiler.compileAbsolute(tmp);

        RpcProvider provider = new RpcProvider(rpc);
        IntegrationWallet wallet = IntegrationWallet.createFunded(rpc, 1.0);

        RunarContract contract = new RunarContract(
            artifact, List.of(BigInteger.ZERO)
        );
        contract.deploy(provider, wallet.signer(), 5_000L);

        // OP_RETURN-style payload (0x6a + 7-byte ASCII "hello!").
        String payload = "6a0768656c6c6f21";
        RunarContract.CallOutcome out = contract.call(
            "log", List.of(payload), null, provider, wallet.signer()
        );
        assertNotNull(out.txid());
    }
}
