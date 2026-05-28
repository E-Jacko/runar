import RunarVerification.ANF.Syntax
import RunarVerification.ANF.Typed

/-!
# ANF Builtin Signature Table

A list-based mirror of the `BUILTIN_FUNCTIONS` map in
`packages/runar-compiler/src/passes/03-typecheck.ts` (125 entries).

The list form is used instead of a match-expression so that downstream
tasks can iterate over the table (e.g. for fidelity checks in Task 9)
and the `builtinSig` function (a O(n) lookup) is easily derivable from
it via `List.find?`.

## Type-mapping conventions

The TS table uses string type-names; the mapping to `ANFType` is:

  'bigint'          → .bigint
  'boolean'         → .bool
  'ByteString'      → .byteString
  'Sha256'          → .sha256
  'Ripemd160'       → .ripemd160
  'PubKey'          → .pubKey
  'Sig'             → .sig
  'Addr'            → .addr
  'SigHashPreimage' → .sigHashPreimage
  'Point'           → .point
  'P256Point'       → .p256Point
  'P384Point'       → .p384Point
  'RabinPubKey'     → .rabinPubKey
  'RabinSig'        → .rabinSig

Two TS return types do not have `ANFType` constructors:

* `'void'` — used by `assert`, `exit`, `requireOutputP2PKH`. These
  builtins are never the source of a typed binding in the compiler's ANF
  (they are statement-level, not expression-level). We render `void`
  as `.bool` — the same convention used in `Typed.lean` — so the table
  remains total and downstream typing rules can assign a uniform type to
  these nodes when they do appear as bindings.
* `'Sig[]'` / `'PubKey[]'` — used only by `checkMultiSig`. No array
  type is modelled in the closed `ANFType` sum. `checkMultiSig` is
  omitted from this table (124 out of 125 TS entries are present); the
  one absent entry is documented by the `checkMultiSig_omitted` comment.
-/

namespace RunarVerification.ANF.TypeCheck

open RunarVerification.ANF (ANFType)

/-- Per-builtin (paramTypes, returnType). Row-for-row mirror of
`packages/runar-compiler/src/passes/03-typecheck.ts` `BUILTIN_FUNCTIONS`
(125 entries; 124 represented here — see module-level note for the one
omitted entry). -/
def builtinTable : List (String × (List ANFType × ANFType)) :=
  [ -- Hashes
    ("sha256",                  ([.byteString],                                                               .sha256)),
    ("ripemd160",               ([.byteString],                                                               .ripemd160)),
    ("hash160",                 ([.byteString],                                                               .ripemd160)),
    ("hash256",                 ([.byteString],                                                               .sha256)),
    -- Signature / preimage
    ("checkSig",                ([.sig, .pubKey],                                                             .bool)),
    -- "checkMultiSig" omitted: params are Sig[]/PubKey[] — no array ANFType
    ("assert",                  ([.bool],                                                                     .bool)),
    -- Byte-string primitives
    ("len",                     ([.byteString],                                                               .bigint)),
    ("cat",                     ([.byteString, .byteString],                                                  .byteString)),
    ("substr",                  ([.byteString, .bigint, .bigint],                                             .byteString)),
    ("num2bin",                 ([.bigint, .bigint],                                                          .byteString)),
    ("bin2num",                 ([.byteString],                                                               .bigint)),
    ("checkPreimage",           ([.sigHashPreimage],                                                          .bool)),
    -- Rabin / WOTS+ / SLH-DSA verifiers
    ("verifyRabinSig",          ([.byteString, .rabinSig, .byteString, .rabinPubKey],                        .bool)),
    ("verifyWOTS",              ([.byteString, .byteString, .byteString],                                     .bool)),
    ("verifySLHDSA_SHA2_128s",  ([.byteString, .byteString, .byteString],                                     .bool)),
    ("verifySLHDSA_SHA2_128f",  ([.byteString, .byteString, .byteString],                                     .bool)),
    ("verifySLHDSA_SHA2_192s",  ([.byteString, .byteString, .byteString],                                     .bool)),
    ("verifySLHDSA_SHA2_192f",  ([.byteString, .byteString, .byteString],                                     .bool)),
    ("verifySLHDSA_SHA2_256s",  ([.byteString, .byteString, .byteString],                                     .bool)),
    ("verifySLHDSA_SHA2_256f",  ([.byteString, .byteString, .byteString],                                     .bool)),
    -- Partial-hash primitives
    ("sha256Compress",          ([.byteString, .byteString],                                                  .byteString)),
    ("sha256Finalize",          ([.byteString, .byteString, .bigint],                                         .byteString)),
    ("blake3Compress",          ([.byteString, .byteString],                                                  .byteString)),
    ("blake3Hash",              ([.byteString],                                                               .byteString)),
    -- Math
    ("abs",                     ([.bigint],                                                                   .bigint)),
    ("min",                     ([.bigint, .bigint],                                                          .bigint)),
    ("max",                     ([.bigint, .bigint],                                                          .bigint)),
    ("within",                  ([.bigint, .bigint, .bigint],                                                 .bool)),
    ("safediv",                 ([.bigint, .bigint],                                                          .bigint)),
    ("safemod",                 ([.bigint, .bigint],                                                          .bigint)),
    ("clamp",                   ([.bigint, .bigint, .bigint],                                                 .bigint)),
    ("sign",                    ([.bigint],                                                                   .bigint)),
    ("pow",                     ([.bigint, .bigint],                                                          .bigint)),
    ("mulDiv",                  ([.bigint, .bigint, .bigint],                                                 .bigint)),
    ("percentOf",               ([.bigint, .bigint],                                                          .bigint)),
    ("sqrt",                    ([.bigint],                                                                   .bigint)),
    ("gcd",                     ([.bigint, .bigint],                                                          .bigint)),
    ("divmod",                  ([.bigint, .bigint],                                                          .bigint)),
    ("log2",                    ([.bigint],                                                                   .bigint)),
    ("bool",                    ([.bigint],                                                                   .bool)),
    -- Byte-string slicing helpers
    ("split",                   ([.byteString, .bigint],                                                      .byteString)),
    ("reverseBytes",            ([.byteString],                                                               .byteString)),
    ("left",                    ([.byteString, .bigint],                                                      .byteString)),
    ("right",                   ([.byteString, .bigint],                                                      .byteString)),
    ("int2str",                 ([.bigint, .bigint],                                                          .byteString)),
    ("toByteString",            ([.byteString],                                                               .byteString)),
    ("exit",                    ([.bool],                                                                     .bool)),
    ("pack",                    ([.bigint],                                                                   .byteString)),
    ("unpack",                  ([.byteString],                                                               .bigint)),
    -- secp256k1 EC
    ("ecAdd",                   ([.point, .point],                                                            .point)),
    ("ecMul",                   ([.point, .bigint],                                                           .point)),
    ("ecMulGen",                ([.bigint],                                                                   .point)),
    ("ecNegate",                ([.point],                                                                    .point)),
    ("ecOnCurve",               ([.point],                                                                    .bool)),
    ("ecModReduce",             ([.bigint, .bigint],                                                          .bigint)),
    ("ecEncodeCompressed",      ([.point],                                                                    .byteString)),
    ("ecMakePoint",             ([.bigint, .bigint],                                                          .point)),
    ("ecPointX",                ([.point],                                                                    .bigint)),
    ("ecPointY",                ([.point],                                                                    .bigint)),
    -- NIST P-256
    ("p256Add",                 ([.p256Point, .p256Point],                                                    .p256Point)),
    ("p256Mul",                 ([.p256Point, .bigint],                                                       .p256Point)),
    ("p256MulGen",              ([.bigint],                                                                   .p256Point)),
    ("p256Negate",              ([.p256Point],                                                                .p256Point)),
    ("p256OnCurve",             ([.p256Point],                                                                .bool)),
    ("p256EncodeCompressed",    ([.p256Point],                                                                .byteString)),
    ("verifyECDSA_P256",        ([.byteString, .byteString, .byteString],                                     .bool)),
    -- NIST P-384
    ("p384Add",                 ([.p384Point, .p384Point],                                                    .p384Point)),
    ("p384Mul",                 ([.p384Point, .bigint],                                                       .p384Point)),
    ("p384MulGen",              ([.bigint],                                                                   .p384Point)),
    ("p384Negate",              ([.p384Point],                                                                .p384Point)),
    ("p384OnCurve",             ([.p384Point],                                                                .bool)),
    ("p384EncodeCompressed",    ([.p384Point],                                                                .byteString)),
    ("verifyECDSA_P384",        ([.byteString, .byteString, .byteString],                                     .bool)),
    -- BabyBear field arithmetic
    ("bbFieldAdd",              ([.bigint, .bigint],                                                          .bigint)),
    ("bbFieldSub",              ([.bigint, .bigint],                                                          .bigint)),
    ("bbFieldMul",              ([.bigint, .bigint],                                                          .bigint)),
    ("bbFieldInv",              ([.bigint],                                                                   .bigint)),
    -- BabyBear quartic extension field
    ("bbExt4Mul0",              ([.bigint, .bigint, .bigint, .bigint, .bigint, .bigint, .bigint, .bigint],    .bigint)),
    ("bbExt4Mul1",              ([.bigint, .bigint, .bigint, .bigint, .bigint, .bigint, .bigint, .bigint],    .bigint)),
    ("bbExt4Mul2",              ([.bigint, .bigint, .bigint, .bigint, .bigint, .bigint, .bigint, .bigint],    .bigint)),
    ("bbExt4Mul3",              ([.bigint, .bigint, .bigint, .bigint, .bigint, .bigint, .bigint, .bigint],    .bigint)),
    ("bbExt4Inv0",              ([.bigint, .bigint, .bigint, .bigint],                                        .bigint)),
    ("bbExt4Inv1",              ([.bigint, .bigint, .bigint, .bigint],                                        .bigint)),
    ("bbExt4Inv2",              ([.bigint, .bigint, .bigint, .bigint],                                        .bigint)),
    ("bbExt4Inv3",              ([.bigint, .bigint, .bigint, .bigint],                                        .bigint)),
    -- KoalaBear field arithmetic
    ("kbFieldAdd",              ([.bigint, .bigint],                                                          .bigint)),
    ("kbFieldSub",              ([.bigint, .bigint],                                                          .bigint)),
    ("kbFieldMul",              ([.bigint, .bigint],                                                          .bigint)),
    ("kbFieldInv",              ([.bigint],                                                                   .bigint)),
    -- KoalaBear quartic extension field
    ("kbExt4Mul0",              ([.bigint, .bigint, .bigint, .bigint, .bigint, .bigint, .bigint, .bigint],    .bigint)),
    ("kbExt4Mul1",              ([.bigint, .bigint, .bigint, .bigint, .bigint, .bigint, .bigint, .bigint],    .bigint)),
    ("kbExt4Mul2",              ([.bigint, .bigint, .bigint, .bigint, .bigint, .bigint, .bigint, .bigint],    .bigint)),
    ("kbExt4Mul3",              ([.bigint, .bigint, .bigint, .bigint, .bigint, .bigint, .bigint, .bigint],    .bigint)),
    ("kbExt4Inv0",              ([.bigint, .bigint, .bigint, .bigint],                                        .bigint)),
    ("kbExt4Inv1",              ([.bigint, .bigint, .bigint, .bigint],                                        .bigint)),
    ("kbExt4Inv2",              ([.bigint, .bigint, .bigint, .bigint],                                        .bigint)),
    ("kbExt4Inv3",              ([.bigint, .bigint, .bigint, .bigint],                                        .bigint)),
    -- BN254 field arithmetic
    ("bn254FieldAdd",           ([.bigint, .bigint],                                                          .bigint)),
    ("bn254FieldSub",           ([.bigint, .bigint],                                                          .bigint)),
    ("bn254FieldMul",           ([.bigint, .bigint],                                                          .bigint)),
    ("bn254FieldInv",           ([.bigint],                                                                   .bigint)),
    ("bn254FieldNeg",           ([.bigint],                                                                   .bigint)),
    -- BN254 G1 curve operations
    ("bn254G1Add",              ([.point, .point],                                                            .point)),
    ("bn254G1ScalarMul",        ([.point, .bigint],                                                           .point)),
    ("bn254G1Negate",           ([.point],                                                                    .point)),
    ("bn254G1OnCurve",          ([.point],                                                                    .bool)),
    -- Merkle proof verification
    ("merkleRootSha256",        ([.byteString, .byteString, .bigint, .bigint],                                .byteString)),
    ("merkleRootHash256",       ([.byteString, .byteString, .bigint, .bigint],                                .byteString)),
    -- Preimage extractors
    ("extractVersion",          ([.sigHashPreimage],                                                          .bigint)),
    ("extractHashPrevouts",     ([.sigHashPreimage],                                                          .sha256)),
    ("extractHashSequence",     ([.sigHashPreimage],                                                          .sha256)),
    ("extractOutpoint",         ([.sigHashPreimage],                                                          .byteString)),
    ("extractInputIndex",       ([.sigHashPreimage],                                                          .bigint)),
    ("extractScriptCode",       ([.sigHashPreimage],                                                          .byteString)),
    ("extractAmount",           ([.sigHashPreimage],                                                          .bigint)),
    ("extractSequence",         ([.sigHashPreimage],                                                          .bigint)),
    ("extractOutputHash",       ([.sigHashPreimage],                                                          .sha256)),
    ("extractOutputs",          ([.sigHashPreimage],                                                          .sha256)),
    ("extractLocktime",         ([.sigHashPreimage],                                                          .bigint)),
    ("extractSigHashType",      ([.sigHashPreimage],                                                          .bigint)),
    ("buildChangeOutput",       ([.byteString, .bigint],                                                      .byteString)),
    -- Intent sub-covenant intrinsics
    ("extractPrevOutputScript", ([.bigint, .byteString],                                                      .byteString)),
    ("requireOutputP2PKH",      ([.bigint, .byteString, .bigint],                                             .bool)),
    ("currentBlockHeight",      ([],                                                                          .bigint))
  ]

/-- Look up a builtin's (paramTypes, returnType) from the table. -/
def builtinSig (name : String) : Option (List ANFType × ANFType) :=
  (builtinTable.find? (·.1 == name)).map (·.2)

end RunarVerification.ANF.TypeCheck

-- Smoke tests (elaborated by `lake build`)
example : RunarVerification.ANF.TypeCheck.builtinSig "sha256" = some ([.byteString], .sha256) := by native_decide
example : RunarVerification.ANF.TypeCheck.builtinSig "ecMul" = some ([.point, .bigint], .point) := by native_decide
example : RunarVerification.ANF.TypeCheck.builtinSig "within" = some ([.bigint, .bigint, .bigint], .bool) := by native_decide
example : RunarVerification.ANF.TypeCheck.builtinSig "not_a_builtin" = none := by native_decide
