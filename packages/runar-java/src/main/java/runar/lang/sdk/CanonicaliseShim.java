package runar.lang.sdk;

import java.io.ByteArrayOutputStream;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Java-tier CLI shim for the cross-tier canonicalJson (RFC 8785 / JCS)
 * differential fuzzer ({@code conformance/fuzzer/canonical-json-differential.ts}).
 *
 * <p>Protocol (single-shot, stdin -&gt; stdout), mirrors the Go / Rust / Python /
 * Zig / Ruby shims:
 *
 * <ul>
 *   <li>{@code {"mode":"json","value":<any JSON>}} — parse {@code value} with
 *       {@link Json#parse(String)} (Long / BigInteger / Double, preserving the
 *       int-vs-float distinction the interop test relies on), run
 *       {@link Envelope#canonicalJson(Object)}, print bytes, exit 0.</li>
 *   <li>{@code {"mode":"utf16","key":"<string>","units":[<int>,...]}} — build
 *       {@code {key: <string from UTF-16 code units>}}. Java {@code String} is a
 *       UTF-16 char sequence and can hold a lone surrogate, so the rejection
 *       happens inside {@link Envelope#canonicalJson} (mirrors the interop
 *       test's surrogate check).</li>
 * </ul>
 *
 * <p>On a typed canonicalJson rejection the shim prints
 * {@code "RUNAR_CANON_ERR:<message>"} to stdout and exits 3; any other failure
 * exits 1.
 *
 * <p>Run via: {@code gradle -q runCanonicalise} (stdin piped in).
 */
public final class CanonicaliseShim {

    private CanonicaliseShim() {
    }

    public static void main(String[] args) {
        String raw;
        try {
            raw = readAll(System.in);
        } catch (Exception e) {
            System.err.println("read stdin: " + e.getMessage());
            System.exit(1);
            return;
        }

        Object input;
        try {
            @SuppressWarnings("unchecked")
            Map<String, Object> req = (Map<String, Object>) Json.parse(raw);
            String mode = String.valueOf(req.get("mode"));
            if ("json".equals(mode)) {
                input = req.get("value");
            } else if ("utf16".equals(mode)) {
                String key = req.get("key") == null ? "" : String.valueOf(req.get("key"));
                @SuppressWarnings("unchecked")
                List<Object> units = (List<Object>) req.get("units");
                Map<String, Object> obj = new LinkedHashMap<>();
                obj.put(key, utf16UnitsToString(units));
                input = obj;
            } else {
                System.err.println("unknown mode " + mode);
                System.exit(1);
                return;
            }
        } catch (Exception e) {
            System.err.println("parse request: " + e.getMessage());
            System.exit(1);
            return;
        }

        try {
            String out = Envelope.canonicalJson(input);
            System.out.print(out);
            System.out.flush();
        } catch (RuntimeException e) {
            System.out.print("RUNAR_CANON_ERR:" + e.getMessage());
            System.out.flush();
            System.exit(3);
        }
    }

    /** Build a Java String from UTF-16 code units, leaving lone surrogates
     *  intact (Java char[] permits them). */
    private static String utf16UnitsToString(List<Object> units) {
        if (units == null) {
            return "";
        }
        StringBuilder sb = new StringBuilder();
        for (Object u : units) {
            long n = ((Number) u).longValue();
            sb.append((char) (n & 0xFFFF));
        }
        return sb.toString();
    }

    private static String readAll(InputStream in) throws Exception {
        ByteArrayOutputStream buf = new ByteArrayOutputStream();
        byte[] chunk = new byte[4096];
        int read;
        while ((read = in.read(chunk)) != -1) {
            buf.write(chunk, 0, read);
        }
        return buf.toString(StandardCharsets.UTF_8);
    }
}
