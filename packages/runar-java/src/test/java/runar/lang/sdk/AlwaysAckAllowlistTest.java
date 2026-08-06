package runar.lang.sdk;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Pattern;
import java.util.stream.Stream;

import org.junit.jupiter.api.Test;

/**
 * Testing-gap remediation Phase A5 (Java tier): machine-checked gate on the
 * always-ack {@link MockProvider} escape hatches
 * ({@code MockProvider.alwaysAck}, {@code disableBroadcastValidation},
 * {@code enableBroadcastValidation(false)}).
 *
 * <p>A test file may only use one of those escape hatches if it has a matching
 * entry in {@code always_ack_allowlist.json}. Enforced in BOTH directions: it
 * fails on unlisted always-ack usage (someone quietly re-disabling the
 * fund-safety net) AND on stale entries (a file that no longer needs
 * always-ack, or that was deleted) — so the list can only shrink.
 *
 * <p>Mirrors {@code packages/runar-sdk/src/__tests__/always-ack-allowlist.test.ts},
 * {@code packages/runar-go/always_ack_allowlist_test.go},
 * {@code packages/runar-rs/tests/always_ack_allowlist.rs},
 * {@code packages/runar-py/tests/test_always_ack_allowlist.py},
 * {@code packages/runar-rb/spec/sdk/always_ack_allowlist_spec.rb} and
 * {@code packages/runar-zig/src/sdk_always_ack_allowlist_test.zig}.
 */
class AlwaysAckAllowlistTest {

    private static final String SELF = "src/test/java/runar/lang/sdk/AlwaysAckAllowlistTest.java";
    private static final Set<String> VALID_CATEGORIES =
        Set.of("structure-only", "negative-api", "fixture-shape", "pending-a3");

    /** Call-site patterns only — the DEFINITIONS live in {@code src/main}. */
    private static final Pattern ALWAYS_ACK = Pattern.compile(
        "MockProvider\\.alwaysAck\\(|\\.disableBroadcastValidation\\(\\)"
        + "|\\.enableBroadcastValidation\\(\\s*false\\s*\\)");

    /**
     * The package root, whether the suite runs from {@code packages/runar-java}
     * (Gradle's default) or from the repo root.
     */
    private static Path packageRoot() {
        Path here = Path.of("").toAbsolutePath();
        if (Files.exists(here.resolve("always_ack_allowlist.json"))) return here;
        Path nested = here.resolve("packages/runar-java");
        if (Files.exists(nested.resolve("always_ack_allowlist.json"))) return nested;
        throw new IllegalStateException("cannot locate always_ack_allowlist.json from " + here);
    }

    @SuppressWarnings("unchecked")
    private static List<Map<String, Object>> allowlist() throws IOException {
        Path p = packageRoot().resolve("always_ack_allowlist.json");
        Map<String, Object> root = (Map<String, Object>) Json.parse(Files.readString(p));
        return (List<Map<String, Object>>) root.get("entries");
    }

    private static Set<String> filesUsingAlwaysAck() throws IOException {
        Path root = packageRoot();
        Path testDir = root.resolve("src/test/java");
        Set<String> found = new LinkedHashSet<>();
        try (Stream<Path> walk = Files.walk(testDir)) {
            for (Path p : walk.filter(Files::isRegularFile)
                              .filter(f -> f.toString().endsWith(".java")).toList()) {
                String rel = root.relativize(p).toString().replace('\\', '/');
                if (rel.equals(SELF)) continue;
                if (ALWAYS_ACK.matcher(Files.readString(p)).find()) found.add(rel);
            }
        }
        return found;
    }

    @Test
    void everyEntryIsWellFormedAndNamesAnExistingFile() throws Exception {
        Path root = packageRoot();
        for (Map<String, Object> e : allowlist()) {
            String file = (String) e.get("file");
            String reason = (String) e.get("reason");
            String category = (String) e.get("category");
            assertTrue(file != null && !file.isBlank(), "allowlist entry with an empty file");
            assertTrue(reason != null && !reason.isBlank(),
                "allowlist entry " + file + " has no reason");
            assertTrue(VALID_CATEGORIES.contains(category),
                "allowlist entry " + file + " has invalid category " + category
                + " (want one of " + VALID_CATEGORIES + ")");
            assertTrue(Files.exists(root.resolve(file)),
                "always_ack_allowlist.json names " + file + ", which does not exist; "
                + "remove the entry");
        }
    }

    @Test
    void noStaleEntries() throws Exception {
        Set<String> usage = filesUsingAlwaysAck();
        List<String> stale = new ArrayList<>();
        for (Map<String, Object> e : allowlist()) {
            String file = (String) e.get("file");
            if (Files.exists(packageRoot().resolve(file)) && !usage.contains(file)) stale.add(file);
        }
        assertTrue(stale.isEmpty(),
            "always_ack_allowlist.json has entries for files that no longer use "
            + "MockProvider.alwaysAck / disableBroadcastValidation / "
            + "enableBroadcastValidation(false) — remove them (the allowlist must only "
            + "shrink): " + stale);
    }

    @Test
    void noUngovernedAlwaysAckUsage() throws Exception {
        Set<String> listed = new LinkedHashSet<>();
        for (Map<String, Object> e : allowlist()) listed.add((String) e.get("file"));
        List<String> unlisted = new ArrayList<>(filesUsingAlwaysAck());
        unlisted.removeAll(listed);
        assertFalse(!unlisted.isEmpty(),
            "Unlisted always-ack MockProvider usage: " + unlisted
            + ". Add an entry to always_ack_allowlist.json with a file, reason and category "
            + VALID_CATEGORIES + ", or fix the test to run under the default validating "
            + "provider instead.");
    }
}
