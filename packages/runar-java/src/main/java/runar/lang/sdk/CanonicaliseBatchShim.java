package runar.lang.sdk;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;

/**
 * Batched peer of {@link CanonicaliseShim}: reads newline-delimited
 * canonicalJson requests on stdin and writes one newline-delimited response per
 * request on stdout, all inside ONE JVM.
 *
 * <p>The single-shot shim ({@code gradle -q runCanonicalise}) forks a fresh JVM
 * per request, which the randomized differential fuzzer tolerates on the nightly
 * path but is too slow (JVM cold-start per case) for the PR gate. This batch
 * entrypoint lets the deterministic Java canonicalJson PR gate
 * ({@code conformance/fuzzer/canonical-java-gate.ts}) push a whole fixed corpus
 * through a single JVM and byte-compare each line against the TS reference.
 *
 * <p>Framing is line-based and safe because canonicalJson output never contains
 * a literal newline (control chars are {@code \\uXXXX}-escaped) and every
 * rejection message is single-line. Each non-empty input line yields exactly one
 * output line — either the canonical bytes or a {@link CanonicaliseShim#REJECT_PREFIX}
 * -tagged message (a malformed request is surfaced as a rejection line rather
 * than aborting the batch, so the response count stays aligned with the request
 * count).
 *
 * <p>Run via: {@code gradle -q runCanonicaliseBatch} (requests piped in).
 */
public final class CanonicaliseBatchShim {

    private CanonicaliseBatchShim() {
    }

    public static void main(String[] args) throws Exception {
        BufferedReader reader =
            new BufferedReader(new InputStreamReader(System.in, StandardCharsets.UTF_8));
        StringBuilder out = new StringBuilder();
        String line;
        while ((line = reader.readLine()) != null) {
            if (line.isEmpty()) {
                continue; // framing / trailing blank line, never a real request
            }
            String result;
            try {
                result = CanonicaliseShim.process(line);
            } catch (CanonicaliseShim.RequestError e) {
                // Surface a malformed request as a rejection token so the driver
                // still gets exactly one response line per request and flags the
                // divergence instead of the batch aborting mid-corpus.
                result = CanonicaliseShim.REJECT_PREFIX + e.getMessage();
            }
            out.append(result).append('\n');
        }
        System.out.print(out);
        System.out.flush();
    }
}
