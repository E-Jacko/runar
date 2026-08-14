//! Testing-gap remediation Phase A5 (Rust tier): machine-checked gate on the
//! always-ack `MockProvider` escape hatches (`MockProvider::always_ack`,
//! `disable_broadcast_validation()`, `enable_broadcast_validation(false)`).
//!
//! A file may only use one of those escape hatches if it has a matching entry
//! in `always_ack_allowlist.json`. Enforced in BOTH directions: it fails on
//! unlisted always-ack usage (someone quietly re-disabling the fund-safety
//! net) AND on stale entries (a file that no longer needs always-ack, or that
//! was deleted) — so the list can only shrink.
//!
//! Mirrors `packages/runar-sdk/src/__tests__/always-ack-allowlist.test.ts` and
//! `packages/runar-go/always_ack_allowlist_test.go`.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

const VALID_CATEGORIES: [&str; 4] =
    ["structure-only", "negative-api", "fixture-shape", "pending-a3"];

/// Call-site patterns only — the DEFINITIONS in `src/sdk/provider.rs`
/// (`pub fn always_ack`, `pub fn disable_broadcast_validation`) deliberately do
/// not match, so the provider itself is not self-referentially allowlisted.
const PATTERNS: [&str; 3] = [
    "MockProvider::always_ack(",
    ".disable_broadcast_validation()",
    ".enable_broadcast_validation(false)",
];

fn package_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// Minimal object-array reader for the allowlist. The SDK crate deliberately
/// avoids pulling `serde_json` into a test-only dependency graph it does not
/// otherwise need; the file shape is fixed and checked below.
fn read_allowlist() -> Vec<(String, String, String)> {
    let raw = fs::read_to_string(package_root().join("always_ack_allowlist.json"))
        .expect("always_ack_allowlist.json must exist");
    let json: serde_json::Value =
        serde_json::from_str(&raw).expect("always_ack_allowlist.json must be valid JSON");
    json["entries"]
        .as_array()
        .expect("always_ack_allowlist.json must have an `entries` array")
        .iter()
        .map(|e| {
            (
                e["file"].as_str().unwrap_or_default().to_string(),
                e["reason"].as_str().unwrap_or_default().to_string(),
                e["category"].as_str().unwrap_or_default().to_string(),
            )
        })
        .collect()
}

fn collect_rs_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(dir) else { return };
    for e in entries.flatten() {
        let p = e.path();
        if p.is_dir() {
            collect_rs_files(&p, out);
        } else if p.extension().and_then(|s| s.to_str()) == Some("rs") {
            out.push(p);
        }
    }
}

/// Package-relative paths of every `.rs` file under `src/` or `tests/` that
/// calls an always-ack escape hatch. This audit file is excluded: it names the
/// hatches in string literals, not at a call site.
fn files_using_always_ack() -> BTreeSet<String> {
    let root = package_root();
    let mut files = Vec::new();
    collect_rs_files(&root.join("src"), &mut files);
    collect_rs_files(&root.join("tests"), &mut files);

    let mut found = BTreeSet::new();
    for path in files {
        let rel = path.strip_prefix(&root).unwrap().to_string_lossy().replace('\\', "/");
        if rel == "tests/always_ack_allowlist.rs" {
            continue;
        }
        let Ok(body) = fs::read_to_string(&path) else { continue };
        if PATTERNS.iter().any(|p| body.contains(p)) {
            found.insert(rel);
        }
    }
    found
}

#[test]
fn allowlist_entries_are_well_formed() {
    for (file, reason, category) in read_allowlist() {
        assert!(!file.trim().is_empty(), "allowlist entry with an empty file");
        assert!(!reason.trim().is_empty(), "allowlist entry {} has no reason", file);
        assert!(
            VALID_CATEGORIES.contains(&category.as_str()),
            "allowlist entry {} has invalid category {:?} (want one of {:?})",
            file,
            category,
            VALID_CATEGORIES
        );
    }
}

#[test]
fn every_allowlist_entry_names_an_existing_file() {
    let root = package_root();
    for (file, _, _) in read_allowlist() {
        assert!(
            root.join(&file).exists(),
            "always_ack_allowlist.json names {:?}, which does not exist; remove the entry",
            file
        );
    }
}

#[test]
fn no_stale_allowlist_entries() {
    let usage = files_using_always_ack();
    let root = package_root();
    for (file, _, _) in read_allowlist() {
        if !root.join(&file).exists() {
            continue; // covered by the existence test
        }
        assert!(
            usage.contains(&file),
            "always_ack_allowlist.json has a STALE entry for {:?} — the file no longer uses \
             MockProvider::always_ack / disable_broadcast_validation / \
             enable_broadcast_validation(false). Remove it: the allowlist must only shrink.",
            file
        );
    }
}

#[test]
fn no_ungoverned_always_ack_usage() {
    let listed: BTreeSet<String> = read_allowlist().into_iter().map(|(f, _, _)| f).collect();
    let unlisted: Vec<String> =
        files_using_always_ack().into_iter().filter(|f| !listed.contains(f)).collect();
    assert!(
        unlisted.is_empty(),
        "Unlisted always-ack MockProvider usage:\n  - {}\nAdd an entry to \
         always_ack_allowlist.json with a file, reason and category ({:?}), or fix the test to \
         run under the default validating provider instead.",
        unlisted.join("\n  - "),
        VALID_CATEGORIES
    );
}
