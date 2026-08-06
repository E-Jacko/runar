package runar.integration;

import java.math.BigInteger;
import java.util.List;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import runar.integration.helpers.ContractCompiler;
import runar.integration.helpers.IntegrationBase;
import runar.integration.helpers.IntegrationWallet;
import runar.integration.helpers.RpcProvider;
import runar.lang.sdk.RunarArtifact;
import runar.lang.sdk.RunarContract;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Phase A residual contracts — deploy+spend on regtest (Java SDK).
 */
class PhaseAResidualsIntegrationTest extends IntegrationBase {

    private void deployCall(String path, List<Object> ctor, String method, List<Object> args, long sats) {
        RunarArtifact artifact = ContractCompiler.compileRelative(path);
        RpcProvider provider = new RpcProvider(rpc);
        IntegrationWallet wallet = IntegrationWallet.createFunded(rpc, 1.0);
        RunarContract contract = new RunarContract(artifact, ctor);
        RunarContract.DeployOutcome deploy = contract.deploy(provider, wallet.signer(), sats);
        assertNotNull(deploy.txid());
        assertEquals(64, deploy.txid().length());
        RunarContract.CallOutcome call = contract.call(method, args, null, provider, wallet.signer());
        assertNotNull(call.txid());
        assertEquals(64, call.txid().length());
    }

    @Test
    @DisplayName("BranchMergedLocals")
    void branchMergedLocals() {
        deployCall(
            "integration/contracts/constructs/BranchMergedLocals.runar.ts",
            List.of(BigInteger.TEN, BigInteger.valueOf(20)),
            "bid",
            List.of(BigInteger.valueOf(99), BigInteger.ONE),
            50_000L
        );
    }

    @Test
    @DisplayName("CondWriteMultiField")
    void condWriteMultiField() {
        deployCall(
            "integration/contracts/constructs/CondWriteMultiField.runar.ts",
            List.of(BigInteger.ONE, BigInteger.TWO),
            "bump",
            List.of(BigInteger.ONE),
            50_000L
        );
    }

    @Test
    @DisplayName("ConditionalDataOutput")
    void conditionalDataOutput() {
        String payload = "6a09" + "6273766d2d74657374";
        deployCall(
            "integration/contracts/constructs/ConditionalDataOutput.runar.ts",
            List.of(BigInteger.ZERO),
            "pay",
            List.of(Boolean.TRUE, payload),
            20_000L
        );
    }

    @Test
    @DisplayName("StateByteString1B")
    void stateByteString1B() {
        deployCall(
            "integration/contracts/constructs/StateByteString1B.runar.ts",
            List.of("05"),
            "setTag",
            List.of("ab"),
            10_000L
        );
    }

    @Test
    @DisplayName("RawOutput")
    void rawOutput() {
        RunarArtifact artifact = ContractCompiler.compileRelative(
            "integration/contracts/outputs/RawOutput.runar.ts"
        );
        RpcProvider provider = new RpcProvider(rpc);
        IntegrationWallet wallet = IntegrationWallet.createFunded(rpc, 1.0);
        RunarContract contract = new RunarContract(artifact, List.of(BigInteger.ZERO));
        contract.deploy(provider, wallet.signer(), 50_000L);
        String p2pkh = "76a914" + wallet.pubKeyHash() + "88ac";
        RunarContract.CallOutcome call = contract.call(
            "sendToScript", List.of(p2pkh), null, provider, wallet.signer()
        );
        assertEquals(64, call.txid().length());
    }

    @Test
    @DisplayName("MultiSig2of3 same-key SDK call")
    void multiSigSameKey() {
        RunarArtifact artifact = ContractCompiler.compileRelative(
            "integration/contracts/crypto/MultiSig2of3.runar.ts"
        );
        RpcProvider provider = new RpcProvider(rpc);
        IntegrationWallet wallet = IntegrationWallet.createFunded(rpc, 1.0);
        IntegrationWallet other = IntegrationWallet.createFunded(rpc, 0.1);
        String pk = wallet.pubKeyHex();
        RunarContract contract = new RunarContract(
            artifact,
            List.of(pk, pk, other.pubKeyHex())
        );
        contract.deploy(provider, wallet.signer(), 5_000L);
        RunarContract.CallOutcome call = contract.call(
            "unlock",
            java.util.Arrays.asList(null, null),
            null,
            provider,
            wallet.signer()
        );
        assertEquals(64, call.txid().length());
    }
}
