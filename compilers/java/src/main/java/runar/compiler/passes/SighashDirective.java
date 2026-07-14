package runar.compiler.passes;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * {@code @sighash} directive parsing (issue #123) — Java port of
 * {@code packages/runar-compiler/src/passes/sighash-directive.ts}.
 *
 * <p>A public method may carry a {@code /** @sighash <FLAGS> *&#47;} comment
 * directive that declares which BIP-143 sighash type its auto-injected covenant
 * (and the SDK-built preimage) commits to. {@code <FLAGS>} is a {@code |}-separated
 * set of SigHash names, e.g. {@code SINGLE|FORKID}, {@code ALL|ANYONECANPAY|FORKID},
 * {@code NONE|FORKID}.
 *
 * <p>The default (no directive) is {@code ALL|FORKID} (0x41) — byte-identical to
 * the historically-pinned mode, so existing fixtures see ZERO change. Detection
 * lives in the parser; this class owns the flag grammar (name -&gt; value, combo
 * validity, FORKID-mandatory).
 */
public final class SighashDirective {
    private SighashDirective() {}

    /** Numeric value of each sighash flag name. */
    private static final Map<String, Integer> FLAG_VALUES = new LinkedHashMap<>();
    static {
        FLAG_VALUES.put("ALL", 0x01);
        FLAG_VALUES.put("NONE", 0x02);
        FLAG_VALUES.put("SINGLE", 0x03);
        FLAG_VALUES.put("FORKID", 0x40);
        FLAG_VALUES.put("ANYONECANPAY", 0x80);
    }

    /** The base-type names. Exactly one MUST appear in a directive. */
    private static final Set<String> BASE_TYPE_NAMES = Set.of("ALL", "NONE", "SINGLE");

    /** SIGHASH_ALL | SIGHASH_FORKID — the default when no directive is present. */
    public static final int SIGHASH_DEFAULT = 0x41;

    /**
     * Base-type mask. {@code sigHashType & BASE_TYPE_MASK} recovers 1/2/3
     * (ALL/NONE/SINGLE) after the FORKID/ANYONECANPAY high bits are stripped.
     */
    public static final int BASE_TYPE_MASK = 0x1f;
    public static final int BASE_ALL = 0x01;
    public static final int BASE_NONE = 0x02;
    public static final int BASE_SINGLE = 0x03;
    public static final int FLAG_FORKID = 0x40;
    public static final int FLAG_ANYONECANPAY = 0x80;

    /** Parse result: exactly one of {@code value} / {@code error} is non-null. */
    public record Result(Integer value, String error) {
        static Result ok(int v) { return new Result(v, null); }
        static Result err(String e) { return new Result(null, e); }
        public boolean isError() { return error != null; }
    }

    /**
     * Parse the flag list of an {@code @sighash} directive.
     *
     * <p>{@code flagsText} is the raw text following {@code @sighash} (e.g.
     * {@code "SINGLE|FORKID"}). Validation (security-relevant — a mis-declared
     * mode is an exploit class):
     * <ul>
     *   <li>every name must be a known flag (reject typos like {@code FORKD})</li>
     *   <li>EXACTLY ONE base type (ALL/NONE/SINGLE) — reject zero, and reject
     *       nonsensical combos such as {@code ALL|NONE}. Checked on NAMES, not
     *       the OR-ed numeric value, because {@code ALL|NONE} (0x01|0x02)
     *       collides with the numeric value of SINGLE (0x03).</li>
     *   <li>reject a duplicated flag name.</li>
     *   <li>FORKID is mandatory on BSV (deploy-to-brick otherwise).</li>
     * </ul>
     */
    public static Result parseSighashFlags(String flagsText) {
        String raw = flagsText == null ? "" : flagsText.trim();
        if (raw.isEmpty()) {
            return Result.err("@sighash directive requires at least one flag (e.g. `@sighash ALL|FORKID`)");
        }

        String[] names = raw.split("\\|", -1);
        Set<String> seen = new LinkedHashSet<>();
        java.util.List<String> baseTypes = new java.util.ArrayList<>();
        int value = 0;

        for (String rawName : names) {
            String name = rawName.trim();
            if (name.isEmpty()) {
                return Result.err("@sighash directive has an empty flag in \"" + raw + "\"");
            }
            if (!FLAG_VALUES.containsKey(name)) {
                return Result.err(
                    "@sighash: unknown flag \"" + name
                    + "\" (valid: ALL, NONE, SINGLE, FORKID, ANYONECANPAY)");
            }
            if (seen.contains(name)) {
                return Result.err("@sighash: duplicate flag \"" + name + "\" in \"" + raw + "\"");
            }
            seen.add(name);
            if (BASE_TYPE_NAMES.contains(name)) {
                baseTypes.add(name);
            }
            value |= FLAG_VALUES.get(name);
        }

        if (baseTypes.isEmpty()) {
            return Result.err(
                "@sighash: must specify exactly one base type (ALL, NONE, or SINGLE); got \"" + raw + "\"");
        }
        if (baseTypes.size() > 1) {
            return Result.err(
                "@sighash: cannot combine base types (" + String.join("|", baseTypes)
                + ") — pick exactly one of ALL/NONE/SINGLE");
        }

        // FORKID is mandatory on BSV: the entire OP_PUSH_TX / BIP-143 preimage
        // machinery is FORKID-only, so a FORKID-less flag set deploys a covenant
        // whose derived signature can never verify (deploy-to-brick).
        if ((value & FLAG_VALUES.get("FORKID")) == 0) {
            return Result.err(
                "@sighash: FORKID is mandatory on BSV; write e.g. @sighash "
                + baseTypes.get(0) + "|FORKID (got \"" + raw + "\")");
        }

        return Result.ok(value);
    }

    private static final Pattern SIGHASH_RE =
        Pattern.compile("@sighash\\s+([A-Za-z0-9_|\\s]*?)(?:\\*/|\\n|\\r|$)");

    /**
     * Extract and parse an {@code @sighash} directive from a block of comment
     * text. Returns {@code null} when no {@code @sighash} token is present,
     * otherwise the parse result (value or error).
     */
    public static Result extractSighashDirective(String commentText) {
        if (commentText == null) {
            return null;
        }
        Matcher m = SIGHASH_RE.matcher(commentText);
        if (!m.find()) {
            return null;
        }
        return parseSighashFlags(m.group(1) == null ? "" : m.group(1));
    }

    /** Human-readable rendering of a sighash value (for diagnostics). */
    public static String describeSighash(int value) {
        java.util.List<String> parts = new java.util.ArrayList<>();
        int base = value & BASE_TYPE_MASK;
        if (base == BASE_ALL) {
            parts.add("ALL");
        } else if (base == BASE_NONE) {
            parts.add("NONE");
        } else if (base == BASE_SINGLE) {
            parts.add("SINGLE");
        } else {
            parts.add("0x" + Integer.toHexString(base));
        }
        if ((value & FLAG_ANYONECANPAY) != 0) {
            parts.add("ANYONECANPAY");
        }
        if ((value & FLAG_FORKID) != 0) {
            parts.add("FORKID");
        }
        return String.join("|", parts);
    }
}
