import { describe, it, expect } from 'vitest';
import { execFileSync } from 'node:child_process';
import { readdirSync } from 'node:fs';
import { resolve, join } from 'node:path';
import {
  findGoBinary,
  findJavaJarPath,
  findRubyBinary,
  findRustBinary,
  findZigBinary,
} from '../runner/runner.js';

/**
 * Cross-tier REJECTION parity.
 *
 * CLAUDE.md's first invariant is frontend parity with no exceptions, but every
 * gate we had measured it on programs that COMPILE: the conformance corpus,
 * the parser-only matrix, the fuzzers. Nothing checked that the seven tiers
 * agree on what to REFUSE.
 *
 * That gap let a real defect reach RC. The Go tier's tree-sitter walk silently
 * dropped any statement it could not parse, so `this.value = ;` compiled to a
 * locking script with the state write missing, and `assert(claim ==)` to one
 * with the spending guard missing — while the other six tiers rejected both.
 * A corpus of programs that must NOT compile is the only thing that catches
 * that class, so it lives here as a gate rather than in an audit directory.
 *
 * Each fixture is malformed or violates the language subset. Every available
 * tier must refuse all of them. A tier that accepts one is either missing a
 * rule its peers enforce or, worse, silently discarding the offending code.
 */

const REPO = resolve(__dirname, '../..');
const DIR = __dirname;

/**
 * Tier binaries are resolved through the RUNNER's own finders, never by
 * hardcoded paths. CI does not lay the tree out the way a local build does: the
 * conformance job downloads compiler artifacts to the REPO ROOT (`runar-go`,
 * `runar-compiler-rust`, `runar-zig`) and the Java compiler as a jar under
 * `compilers/java/build/libs/`, while a local build leaves them under
 * `compilers/<tier>/`. Hardcoding the local layout found exactly one tier in
 * CI, which the vacuity self-check below caught.
 */
interface Tier {
  id: string;
  bin: string | null;
  argv: (bin: string, src: string) => string[];
  cwd?: string;
}

const javaJar = findJavaJarPath();

const TIERS: Tier[] = [
  { id: 'go', bin: findGoBinary(), argv: (b, s) => [b, '--source', s, '--hex'] },
  { id: 'rust', bin: findRustBinary(), argv: (b, s) => [b, '--source', s, '--hex'] },
  { id: 'zig', bin: findZigBinary(), argv: (b, s) => [b, 'compile', s, '--hex'] },
  {
    id: 'ruby',
    bin: findRubyBinary(),
    argv: (b, s) => [b, '--source', s, '--hex'],
    cwd: join(REPO, 'compilers/ruby'),
  },
  // Java ships as a jar, so the binary is `java` and the jar is an argument.
  {
    id: 'java',
    bin: javaJar ? 'java' : null,
    argv: (_b, s) => ['-jar', javaJar!, '--source', s, '--hex'],
  },
];

function accepts(tier: Tier, src: string): boolean {
  const [cmd, ...args] = tier.argv(tier.bin!, src);
  try {
    execFileSync(cmd!, args, {
      cwd: tier.cwd ?? REPO,
      stdio: 'pipe',
      timeout: 120_000,
    });
    return true;
  } catch {
    return false;
  }
}

const fixtures = readdirSync(DIR)
  .filter((f) => f.endsWith('.runar.ts'))
  .sort();

describe('cross-tier rejection parity', () => {
  it('the corpus is non-empty (a silently empty gate proves nothing)', () => {
    expect(fixtures.length).toBeGreaterThanOrEqual(12);
  });

  const available = TIERS.filter((t) => t.bin !== null);

  it('at least two tiers are built, or the comparison is vacuous', () => {
    expect(available.length).toBeGreaterThanOrEqual(2);
  });

  for (const fixture of fixtures) {
    const src = join(DIR, fixture);
    for (const tier of available) {
      it(`${tier.id} rejects ${fixture}`, () => {
        expect(
          accepts(tier, src),
          `${tier.id} ACCEPTED ${fixture}. Either the tier is missing a rule its ` +
            `peers enforce, or it is silently dropping the offending construct — ` +
            `the latter emits a locking script for a program no other tier accepts.`,
        ).toBe(false);
      });
    }
  }
});
