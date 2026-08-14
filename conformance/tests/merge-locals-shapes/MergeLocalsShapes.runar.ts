import { StatefulSmartContract } from 'runar-lang';

/**
 * MergeLocalsShapes -- the three branch-merge arities that had no REAL-CRYPTO
 * evidence: construct-ledger rows `merge-locals-k2-both-arms`,
 * `merge-locals-k3` and `merge-locals-nested-if`.
 *
 * `conformance/tests/branch-merged-locals` already pins the ASYMMETRIC k=2
 * shape (each arm rebinds a different local) end to end. These three were
 * backed only by a Script-VM unit test; the plan's Phase D1 asks for the same
 * real-secp256k1 / real-BIP-143 continuation proof the asymmetric case gets.
 *
 * Every method ends with `addOutput` AFTER the branch -- an `addOutput` INSIDE
 * a branch that also merges locals is unrepresentable and a hard compile error
 * in all seven tiers (see
 * packages/runar-compiler/src/__tests__/branch-outputs-merged-locals.test.ts).
 *
 *   bothArms -- k=2, BOTH arms reassign BOTH locals (the symmetric case).
 *   three    -- k=3, both arms reassign all three (the arity that proves the
 *               fix generalises instead of special-casing k=2).
 *   nested   -- an OUTER `if` without an `else` whose then-arm is itself an
 *               `if`/`else` rebinding a DIFFERENT local per inner arm, so the
 *               merge lands at the outer level with three reachable states.
 */
class MergeLocalsShapes extends StatefulSmartContract {
  a: bigint;
  b: bigint;
  c: bigint;

  constructor(a: bigint, b: bigint, c: bigint) {
    super(a, b, c);
    this.a = a;
    this.b = b;
    this.c = c;
  }

  public bothArms(x: bigint, flag: bigint) {
    let na: bigint = this.a;
    let nb: bigint = this.b;
    if (flag > 0n) {
      na = x + 1n;
      nb = x + 2n;
    } else {
      na = x + 3n;
      nb = x + 4n;
    }
    this.addOutput(1000n, na, nb, this.c);
  }

  public three(x: bigint, flag: bigint) {
    let na: bigint = this.a;
    let nb: bigint = this.b;
    let nc: bigint = this.c;
    if (flag > 0n) {
      na = x + 1n;
      nb = x + 2n;
      nc = x + 3n;
    } else {
      na = x + 4n;
      nb = x + 5n;
      nc = x + 6n;
    }
    this.addOutput(1000n, na, nb, nc);
  }

  public nested(x: bigint, outer: bigint, inner: bigint) {
    let na: bigint = this.a;
    let nb: bigint = this.b;
    if (outer > 0n) {
      if (inner > 0n) {
        na = x + 1n;
      } else {
        nb = x + 2n;
      }
    }
    this.addOutput(1000n, na, nb, this.c);
  }
}
