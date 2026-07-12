/**
 * Rúnar Program Fuzzer — generates random valid Rúnar contract source strings
 * for property-based testing (CSmith-inspired).
 *
 * Uses fast-check Arbitrary combinators to produce well-typed, syntactically
 * valid Rúnar contracts.
 */

import fc from 'fast-check';
import type {
  GeneratedContract,
  GeneratedProperty,
  GeneratedMethod,
  GeneratedParam,
  Expr,
  Stmt,
  ForStmt,
  RuinarType,
} from './contract-ir.js';

// ---------------------------------------------------------------------------
// Primitive types available in Rúnar
// ---------------------------------------------------------------------------

const PROPERTY_TYPES = ['bigint', 'boolean', 'ByteString', 'PubKey', 'Sig'] as const;
type PropertyType = (typeof PROPERTY_TYPES)[number];

// ---------------------------------------------------------------------------
// Name generators
// ---------------------------------------------------------------------------

const arbPropertyName: fc.Arbitrary<string> = fc
  .integer({ min: 0, max: 99 })
  .map((n) => `prop${n}`);

const arbParamName: fc.Arbitrary<string> = fc
  .integer({ min: 0, max: 99 })
  .map((n) => `param${n}`);

const arbLocalName: fc.Arbitrary<string> = fc
  .integer({ min: 0, max: 99 })
  .map((n) => `local${n}`);

const arbMethodName: fc.Arbitrary<string> = fc
  .integer({ min: 0, max: 9 })
  .map((n) => `method${n}`);

const arbContractName: fc.Arbitrary<string> = fc
  .integer({ min: 0, max: 99 })
  .map((n) => `TestContract${n}`);

const arbPropertyType: fc.Arbitrary<PropertyType> = fc.constantFrom(...PROPERTY_TYPES);

// ---------------------------------------------------------------------------
// Expression generators
// ---------------------------------------------------------------------------

interface PropertyDef {
  name: string;
  type: PropertyType;
}

interface ParamDef {
  name: string;
  type: PropertyType;
}

function arbBigintLiteral(): fc.Arbitrary<string> {
  return fc.bigInt({ min: -1000n, max: 1000n }).map((n) => `${n}n`);
}

function arbBoolLiteral(): fc.Arbitrary<string> {
  return fc.boolean().map((b) => String(b));
}

/** Generate a random ByteString literal expression. */
export function arbByteStringLiteral(): fc.Arbitrary<string> {
  return fc
    .array(fc.integer({ min: 0, max: 255 }), { minLength: 0, maxLength: 8 })
    .map(
      (bytes) =>
        `toByteString('${bytes.map((b) => b.toString(16).padStart(2, '0')).join('')}')`,
    );
}

/**
 * A non-zero divisor literal for `/` and `%`. Always a fixed literal (never
 * a variable) so the resulting expression is well-defined regardless of the
 * random witness value drawn for the left-hand side at spend time — the
 * execution oracle (`runDifferentialExecution`, driven by
 * `arbArithmeticContract` / `arbStatelessContract`) synthesizes fresh
 * bigint witnesses per spend and cannot itself guarantee a variable operand
 * is non-zero.
 */
function arbNonZeroDivisorLiteral(): fc.Arbitrary<string> {
  return fc.integer({ min: 1, max: 20 }).chain((n) =>
    fc.constantFrom(`${n}n`, `${-n}n`),
  );
}

/**
 * Generate a random arithmetic expression using available bigint variables.
 */
function arbArithExpr(bigintVars: string[], depth: number): fc.Arbitrary<string> {
  if (depth <= 0 || bigintVars.length === 0) {
    return fc.oneof(
      arbBigintLiteral(),
      bigintVars.length > 0
        ? fc.constantFrom(...bigintVars)
        : arbBigintLiteral(),
    );
  }

  const leaf = arbArithExpr(bigintVars, 0);
  const binOps = ['+', '-', '*'] as const;

  return fc.oneof(
    leaf,
    fc
      .tuple(
        arbArithExpr(bigintVars, depth - 1),
        fc.constantFrom(...binOps),
        arbArithExpr(bigintVars, depth - 1),
      )
      .map(([l, op, r]) => `(${l} ${op} ${r})`),
    // Division / modulo — RHS is always a non-zero literal (see
    // arbNonZeroDivisorLiteral) so `/`/`%` reach the execution oracle with a
    // well-defined result instead of a div-by-zero reject on both engines.
    fc
      .tuple(
        arbArithExpr(bigintVars, depth - 1),
        fc.constantFrom('/' as const, '%' as const),
        arbNonZeroDivisorLiteral(),
      )
      .map(([l, op, r]) => `(${l} ${op} ${r})`),
  );
}

/**
 * Generate a random boolean expression using available variables.
 */
function arbBoolExpr(
  bigintVars: string[],
  boolVars: string[],
  depth: number,
): fc.Arbitrary<string> {
  if (depth <= 0) {
    return fc.oneof(
      arbBoolLiteral(),
      boolVars.length > 0 ? fc.constantFrom(...boolVars) : arbBoolLiteral(),
    );
  }

  const comparisons = ['===', '!==', '<', '<=', '>', '>='] as const;
  const logicalOps = ['&&', '||'] as const;

  const comparisonExpr =
    bigintVars.length > 0
      ? fc
          .tuple(
            arbArithExpr(bigintVars, depth - 1),
            fc.constantFrom(...comparisons),
            arbArithExpr(bigintVars, depth - 1),
          )
          .map(([l, op, r]) => `(${l} ${op} ${r})`)
      : arbBoolLiteral();

  return fc.oneof(
    comparisonExpr,
    fc
      .tuple(
        arbBoolExpr(bigintVars, boolVars, depth - 1),
        fc.constantFrom(...logicalOps),
        arbBoolExpr(bigintVars, boolVars, depth - 1),
      )
      .map(([l, op, r]) => `(${l} ${op} ${r})`),
    arbBoolExpr(bigintVars, boolVars, depth - 1).map((e) => `!(${e})`),
  );
}

// ---------------------------------------------------------------------------
// Statement generators
// ---------------------------------------------------------------------------

function arbAssertStatement(
  bigintVars: string[],
  boolVars: string[],
): fc.Arbitrary<string> {
  return arbBoolExpr(bigintVars, boolVars, 2).map(
    (cond) => `    assert(${cond});`,
  );
}

function arbVarDeclStatement(
  bigintVars: string[],
): fc.Arbitrary<{ stmt: string; name: string; type: 'bigint' }> {
  return fc.tuple(arbLocalName, arbArithExpr(bigintVars, 2)).map(([name, expr]) => ({
    stmt: `    let ${name}: bigint = ${expr};`,
    name,
    type: 'bigint' as const,
  }));
}

function arbIfStatement(
  bigintVars: string[],
  boolVars: string[],
): fc.Arbitrary<string> {
  return fc
    .tuple(
      arbBoolExpr(bigintVars, boolVars, 1),
      arbAssertStatement(bigintVars, boolVars),
    )
    .map(
      ([cond, body]) =>
        `    if (${cond}) {\n  ${body}\n    }`,
    );
}

// ---------------------------------------------------------------------------
// Method body generator
// ---------------------------------------------------------------------------

function arbMethodBody(
  properties: PropertyDef[],
  params: ParamDef[],
): fc.Arbitrary<string> {
  // Collect available variable names by type.
  const bigintVars = [
    ...properties.filter((p) => p.type === 'bigint').map((p) => `this.${p.name}`),
    ...params.filter((p) => p.type === 'bigint').map((p) => p.name),
  ];
  const boolVars = [
    ...properties.filter((p) => p.type === 'boolean').map((p) => `this.${p.name}`),
    ...params.filter((p) => p.type === 'boolean').map((p) => p.name),
  ];

  return fc
    .tuple(
      // 0-2 variable declarations
      fc.array(arbVarDeclStatement(bigintVars), { minLength: 0, maxLength: 2 }),
      // 0-1 if statements
      fc.array(arbIfStatement(bigintVars, boolVars), { minLength: 0, maxLength: 1 }),
      // 1-2 assert statements (method must end with assert)
      fc.array(arbAssertStatement(bigintVars, boolVars), {
        minLength: 1,
        maxLength: 2,
      }),
    )
    .map(([decls, ifs, asserts]) => {
      const allBigintVars = [
        ...bigintVars,
        ...decls.map((d) => d.name),
      ];
      // Build body with all available vars for the final asserts.
      const lines: string[] = [];
      for (const d of decls) {
        lines.push(d.stmt);
      }
      for (const ifStmt of ifs) {
        lines.push(ifStmt);
      }
      for (const a of asserts) {
        lines.push(a);
      }
      void allBigintVars; // used above transitively
      return lines.join('\n');
    });
}

// ---------------------------------------------------------------------------
// Contract generator
// ---------------------------------------------------------------------------

function arbMethod(
  properties: PropertyDef[],
): fc.Arbitrary<string> {
  return fc
    .tuple(
      arbMethodName,
      // 0-3 parameters (bigint or boolean only for simplicity)
      fc.array(
        fc.tuple(arbParamName, fc.constantFrom('bigint' as const, 'boolean' as const)),
        { minLength: 0, maxLength: 3 },
      ),
    )
    .chain(([name, paramDefs]) => {
      // Deduplicate parameter names.
      const seen = new Set<string>();
      const uniqueParams: ParamDef[] = [];
      for (const [pName, pType] of paramDefs) {
        const uniqueName = seen.has(pName) ? `${pName}_` : pName;
        seen.add(uniqueName);
        uniqueParams.push({ name: uniqueName, type: pType });
      }

      const paramStr = uniqueParams
        .map((p) => `${p.name}: ${p.type}`)
        .join(', ');

      return arbMethodBody(properties, uniqueParams).map(
        (body) =>
          `  public ${name}(${paramStr}) {\n${body}\n  }`,
      );
    });
}

function arbPropertyDefs(): fc.Arbitrary<PropertyDef[]> {
  return fc
    .array(fc.tuple(arbPropertyName, arbPropertyType), {
      minLength: 1,
      maxLength: 3,
    })
    .map((defs) => {
      // Deduplicate property names.
      const seen = new Set<string>();
      const result: PropertyDef[] = [];
      for (const [name, type] of defs) {
        const uniqueName = seen.has(name) ? `${name}_` : name;
        seen.add(uniqueName);
        result.push({ name: uniqueName, type });
      }
      return result;
    });
}

function arbConstructor(properties: PropertyDef[]): string {
  const params = properties.map((p) => `${p.name}: ${p.type}`).join(', ');
  const superArgs = properties.map((p) => p.name).join(', ');
  const assignments = properties
    .map((p) => `    this.${p.name} = ${p.name};`)
    .join('\n');
  return `  constructor(${params}) {\n    super(${superArgs});\n${assignments}\n  }`;
}

function generateContractSource(
  contractName: string,
  properties: PropertyDef[],
  methods: string[],
): string {
  const propDecls = properties
    .map((p) => `  readonly ${p.name}: ${p.type};`)
    .join('\n');

  const ctor = arbConstructor(properties);

  const imports = [
    `import { SmartContract, assert } from 'runar-lang';`,
  ];

  // Add type imports if needed.
  const usedTypes = new Set(properties.map((p) => p.type));
  const typeImports: string[] = [];
  if (usedTypes.has('ByteString')) typeImports.push('ByteString', 'toByteString');
  if (usedTypes.has('PubKey')) typeImports.push('PubKey');
  if (usedTypes.has('Sig')) typeImports.push('Sig');
  if (typeImports.length > 0) {
    imports.push(
      `import { ${typeImports.join(', ')} } from 'runar-lang';`,
    );
  }

  return `${imports.join('\n')}

export class ${contractName} extends SmartContract {
${propDecls}

${ctor}

${methods.join('\n\n')}
}
`;
}

// ---------------------------------------------------------------------------
// Public arbitraries
// ---------------------------------------------------------------------------

/**
 * Generate a random valid Rúnar contract source string.
 */
export const arbContract: fc.Arbitrary<string> = fc
  .tuple(arbContractName, arbPropertyDefs())
  .chain(([name, props]) =>
    fc
      .tuple(
        fc.constant(name),
        fc.constant(props),
        fc.array(arbMethod(props), { minLength: 1, maxLength: 3 }),
      )
      .map(([contractName, properties, methods]) =>
        generateContractSource(contractName, properties, methods),
      ),
  );

/**
 * Generate contracts with no properties (stateless).
 * Methods use only their parameters.
 */
export const arbStatelessContract: fc.Arbitrary<string> = fc
  .tuple(
    arbContractName,
    fc.array(
      fc
        .tuple(
          arbMethodName,
          fc.array(
            fc.tuple(arbParamName, fc.constant('bigint' as PropertyType)),
            { minLength: 1, maxLength: 3 },
          ),
        )
        .chain(([name, paramDefs]) => {
          const seen = new Set<string>();
          const uniqueParams: ParamDef[] = [];
          for (const [pName, pType] of paramDefs) {
            const uniqueName = seen.has(pName) ? `${pName}_` : pName;
            seen.add(uniqueName);
            uniqueParams.push({ name: uniqueName, type: pType });
          }
          const bigintVars = uniqueParams.map((p) => p.name);
          const paramStr = uniqueParams
            .map((p) => `${p.name}: ${p.type}`)
            .join(', ');
          return arbAssertStatement(bigintVars, []).map(
            (body) =>
              `  public ${name}(${paramStr}) {\n${body}\n  }`,
          );
        }),
      { minLength: 1, maxLength: 2 },
    ),
  )
  .map(([contractName, methods]) => {
    return `import { SmartContract, assert } from 'runar-lang';

export class ${contractName} extends SmartContract {
  constructor() { super(); }

${methods.join('\n\n')}
}
`;
  });

/**
 * Generate contracts focused on arithmetic operations.
 */
export const arbArithmeticContract: fc.Arbitrary<string> = fc
  .tuple(
    arbContractName,
    // 1-3 bigint properties
    fc.array(arbPropertyName, { minLength: 1, maxLength: 3 }).map((names) => {
      const seen = new Set<string>();
      return names.map((n) => {
        const unique = seen.has(n) ? `${n}_` : n;
        seen.add(unique);
        return { name: unique, type: 'bigint' as PropertyType };
      });
    }),
  )
  .chain(([contractName, properties]) =>
    fc
      .array(
        fc
          .tuple(
            arbMethodName,
            fc.array(
              fc.tuple(arbParamName, fc.constant('bigint' as PropertyType)),
              { minLength: 1, maxLength: 3 },
            ),
          )
          .chain(([name, paramDefs]) => {
            const seen = new Set<string>();
            const uniqueParams: ParamDef[] = [];
            for (const [pName, pType] of paramDefs) {
              const uniqueName = seen.has(pName) ? `${pName}_` : pName;
              seen.add(uniqueName);
              uniqueParams.push({ name: uniqueName, type: pType });
            }
            const bigintVars = [
              ...properties.map((p) => `this.${p.name}`),
              ...uniqueParams.map((p) => p.name),
            ];
            const paramStr = uniqueParams
              .map((p) => `${p.name}: ${p.type}`)
              .join(', ');
            return fc
              .tuple(
                arbArithExpr(bigintVars, 3),
                arbArithExpr(bigintVars, 3),
              )
              .map(
                ([lhs, rhs]) =>
                  `  public ${name}(${paramStr}) {\n    assert(${lhs} === ${rhs});\n  }`,
              );
          }),
        { minLength: 1, maxLength: 3 },
      )
      .map((methods) =>
        generateContractSource(contractName, properties, methods),
      ),
  );

/**
 * Generate contracts focused on cryptographic operations.
 */
export const arbCryptoContract: fc.Arbitrary<string> = fc
  .tuple(
    arbContractName,
    fc.array(arbPropertyName, { minLength: 1, maxLength: 2 }).map((names) => {
      const seen = new Set<string>();
      return names.map((n) => {
        const unique = seen.has(n) ? `${n}_` : n;
        seen.add(unique);
        return { name: unique, type: 'PubKey' as PropertyType };
      });
    }),
  )
  .chain(([contractName, properties]) =>
    fc
      .array(
        arbMethodName.map(
          (name) =>
            `  public ${name}(sig: Sig, msg: ByteString) {\n` +
            `    assert(checkSig(sig, this.${properties[0]!.name}));\n` +
            `    assert(sha256(msg) !== toByteString('${'00'.repeat(32)}'));\n` +
            `  }`,
        ),
        { minLength: 1, maxLength: 2 },
      )
      .map((methods) => {
        const propDecls = properties
          .map((p) => `  readonly ${p.name}: ${p.type};`)
          .join('\n');
        const ctorParams = properties.map((p) => `${p.name}: ${p.type}`).join(', ');
        const ctorBody = properties
          .map((p) => `    this.${p.name} = ${p.name};`)
          .join('\n');

        return `import { SmartContract, assert, checkSig, sha256 } from 'runar-lang';
import { PubKey, Sig, ByteString, toByteString } from 'runar-lang';

export class ${contractName} extends SmartContract {
${propDecls}

  constructor(${ctorParams}) {
    super(${properties.map((p) => p.name).join(', ')});
${ctorBody}
  }

${methods.join('\n\n')}
}
`;
      }),
  );

// ===========================================================================
// IR-based generators (language-neutral)
// ===========================================================================

/**
 * Configuration for the IR-based contract generator.
 */
export interface GeneratorConfig {
  maxProperties: number;
  maxExprDepth: number;
  maxMethods: number;
  maxStatements: number;
  maxParams: number;
}

const DEFAULT_CONFIG: GeneratorConfig = {
  maxProperties: 3,
  maxExprDepth: 3,
  maxMethods: 3,
  maxStatements: 4,
  maxParams: 3,
};

// ---------------------------------------------------------------------------
// IR type generator
// ---------------------------------------------------------------------------

export const arbRuinarType: fc.Arbitrary<RuinarType> = fc.oneof(
  { weight: 5, arbitrary: fc.constant('bigint' as RuinarType) },
  { weight: 3, arbitrary: fc.constant('boolean' as RuinarType) },
  { weight: 1, arbitrary: fc.constant('ByteString' as RuinarType) },
  { weight: 1, arbitrary: fc.constant('PubKey' as RuinarType) },
);

// ---------------------------------------------------------------------------
// IR expression generators
// ---------------------------------------------------------------------------

function arbBigintLiteralIR(): fc.Arbitrary<Expr> {
  return fc.bigInt({ min: -100n, max: 100n }).map(
    (v): Expr => ({ kind: 'bigint_literal', value: v }),
  );
}

function arbBoolLiteralIR(): fc.Arbitrary<Expr> {
  return fc.boolean().map(
    (v): Expr => ({ kind: 'bool_literal', value: v }),
  );
}

export function arbByteStringLiteralIR(): fc.Arbitrary<Expr> {
  return fc
    .array(fc.integer({ min: 0, max: 255 }), { minLength: 0, maxLength: 4 })
    .map((bytes): Expr => ({
      kind: 'bytestring_literal',
      hex: bytes.map((b) => b.toString(16).padStart(2, '0')).join(''),
    }));
}

/**
 * A non-zero divisor literal for `/` and `%` (IR form). See
 * `arbNonZeroDivisorLiteral` above — same rationale: `arbGeneratedContract`
 * feeds `execute-differential.ts`'s witness-driven execution oracle, so the
 * divisor must be fixed at generation time, not left to a runtime witness.
 */
function arbNonZeroDivisorLiteralIR(): fc.Arbitrary<Expr> {
  return fc.integer({ min: 1, max: 20 }).chain((n) =>
    fc.constantFrom<Expr>(
      { kind: 'bigint_literal', value: BigInt(n) },
      { kind: 'bigint_literal', value: BigInt(-n) },
    ),
  );
}

/** Generate a bigint-typed expression using available vars. */
function arbBigintExprIR(
  bigintVars: string[],
  depth: number,
): fc.Arbitrary<Expr> {
  if (depth <= 0) {
    const options: fc.Arbitrary<Expr>[] = [arbBigintLiteralIR()];
    if (bigintVars.length > 0) {
      options.push(fc.constantFrom(...bigintVars).map(
        (name): Expr => name.startsWith('this.')
          ? { kind: 'property_ref', name: name.slice(5) }
          : { kind: 'var_ref', name },
      ));
    }
    return fc.oneof(...options);
  }

  const leaf = arbBigintExprIR(bigintVars, 0);
  const ops: Array<'+' | '-' | '*'> = ['+', '-', '*'];

  return fc.oneof(
    leaf,
    // Binary arithmetic
    fc.tuple(
      arbBigintExprIR(bigintVars, depth - 1),
      fc.constantFrom(...ops),
      arbBigintExprIR(bigintVars, depth - 1),
    ).map(([left, op, right]): Expr => ({ kind: 'binary', op, left, right })),
    // Division / modulo — RHS restricted to a non-zero literal (see
    // arbNonZeroDivisorLiteralIR) so OP_DIV/OP_MOD reach the execution
    // oracle with a well-defined result on every synthesized witness.
    fc.tuple(
      arbBigintExprIR(bigintVars, depth - 1),
      fc.constantFrom('/' as const, '%' as const),
      arbNonZeroDivisorLiteralIR(),
    ).map(([left, op, right]): Expr => ({ kind: 'binary', op, left, right })),
    // Math builtins
    fc.tuple(
      fc.constantFrom('abs'),
      arbBigintExprIR(bigintVars, depth - 1),
    ).map(([fn, arg]): Expr => ({ kind: 'call', fn, args: [arg] })),
    fc.tuple(
      fc.constantFrom('min', 'max'),
      arbBigintExprIR(bigintVars, depth - 1),
      arbBigintExprIR(bigintVars, depth - 1),
    ).map(([fn, a, b]): Expr => ({ kind: 'call', fn, args: [a, b] })),
  );
}

/** Generate a boolean-typed expression. */
function arbBoolExprIR(
  bigintVars: string[],
  boolVars: string[],
  depth: number,
): fc.Arbitrary<Expr> {
  if (depth <= 0) {
    const options: fc.Arbitrary<Expr>[] = [arbBoolLiteralIR()];
    if (boolVars.length > 0) {
      options.push(fc.constantFrom(...boolVars).map(
        (name): Expr => name.startsWith('this.')
          ? { kind: 'property_ref', name: name.slice(5) }
          : { kind: 'var_ref', name },
      ));
    }
    return fc.oneof(...options);
  }

  const comparisons: Array<'===' | '!==' | '<' | '>' | '<=' | '>='> =
    ['===', '!==', '<', '>', '<=', '>='];

  return fc.oneof(
    // Comparison
    bigintVars.length > 0
      ? fc.tuple(
          arbBigintExprIR(bigintVars, depth - 1),
          fc.constantFrom(...comparisons),
          arbBigintExprIR(bigintVars, depth - 1),
        ).map(([left, op, right]): Expr => ({ kind: 'binary', op, left, right }))
      : arbBoolLiteralIR(),
    // Logical
    fc.tuple(
      arbBoolExprIR(bigintVars, boolVars, depth - 1),
      fc.constantFrom('&&' as const, '||' as const),
      arbBoolExprIR(bigintVars, boolVars, depth - 1),
    ).map(([left, op, right]): Expr => ({ kind: 'binary', op, left, right })),
    // Negation
    arbBoolExprIR(bigintVars, boolVars, depth - 1).map(
      (operand): Expr => ({ kind: 'unary', op: '!', operand }),
    ),
  );
}

// ---------------------------------------------------------------------------
// IR statement generators
// ---------------------------------------------------------------------------

function arbAssertStmtIR(
  bigintVars: string[],
  boolVars: string[],
): fc.Arbitrary<Stmt> {
  return arbBoolExprIR(bigintVars, boolVars, 2).map(
    (condition): Stmt => ({ kind: 'assert', condition }),
  );
}

function arbVarDeclStmtIR(
  bigintVars: string[],
): fc.Arbitrary<{ stmt: Stmt; name: string; type: RuinarType }> {
  return fc.tuple(
    fc.integer({ min: 0, max: 99 }).map((n) => `local${n}`),
    arbBigintExprIR(bigintVars, 2),
  ).map(([name, value]) => ({
    stmt: { kind: 'var_decl' as const, name, type: 'bigint' as const, value, mutable: false },
    name,
    type: 'bigint' as RuinarType,
  }));
}

function arbIfStmtIR(
  bigintVars: string[],
  boolVars: string[],
): fc.Arbitrary<Stmt> {
  return fc.tuple(
    arbBoolExprIR(bigintVars, boolVars, 1),
    arbAssertStmtIR(bigintVars, boolVars),
    fc.option(arbAssertStmtIR(bigintVars, boolVars)),
  ).map(([condition, thenStmt, elseStmt]): Stmt => ({
    kind: 'if',
    condition,
    then: [thenStmt],
    else_: elseStmt ? [elseStmt] : undefined,
  }));
}

// ---------------------------------------------------------------------------
// IR method and contract generators
// ---------------------------------------------------------------------------

function arbMethodIR(
  properties: GeneratedProperty[],
  config: GeneratorConfig,
): fc.Arbitrary<GeneratedMethod> {
  return fc.tuple(
    fc.integer({ min: 0, max: 9 }).map((n) => `method${n}`),
    fc.array(
      fc.tuple(
        fc.integer({ min: 0, max: 99 }).map((n) => `param${n}`),
        fc.constantFrom('bigint' as RuinarType, 'boolean' as RuinarType),
      ),
      { minLength: 0, maxLength: config.maxParams },
    ),
  ).chain(([name, paramDefs]) => {
    // Deduplicate
    const seen = new Set<string>();
    const params: GeneratedParam[] = [];
    for (const [pName, pType] of paramDefs) {
      const unique = seen.has(pName) ? `${pName}X` : pName;
      seen.add(unique);
      params.push({ name: unique, type: pType });
    }

    const bigintVars = [
      ...properties.filter((p) => p.type === 'bigint').map((p) => `this.${p.name}`),
      ...params.filter((p) => p.type === 'bigint').map((p) => p.name),
    ];
    const boolVars = [
      ...properties.filter((p) => p.type === 'boolean').map((p) => `this.${p.name}`),
      ...params.filter((p) => p.type === 'boolean').map((p) => p.name),
    ];

    return fc.tuple(
      fc.array(arbVarDeclStmtIR(bigintVars), { minLength: 0, maxLength: 2 }),
      fc.array(arbIfStmtIR(bigintVars, boolVars), { minLength: 0, maxLength: 1 }),
      fc.array(arbAssertStmtIR(bigintVars, boolVars), { minLength: 1, maxLength: 2 }),
    ).map(([decls, ifs, asserts]): GeneratedMethod => {
      const body: Stmt[] = [
        ...decls.map((d) => d.stmt),
        ...ifs,
        ...asserts,
      ];

      return {
        name,
        visibility: 'public',
        params,
        body,
        mutatesState: false,
      };
    });
  });
}

function arbStatefulMethodIR(
  properties: GeneratedProperty[],
  config: GeneratorConfig,
): fc.Arbitrary<GeneratedMethod> {
  const mutableProps = properties.filter((p) => !p.readonly);

  return fc.tuple(
    fc.integer({ min: 0, max: 9 }).map((n) => `method${n}`),
    fc.array(
      fc.tuple(
        fc.integer({ min: 0, max: 99 }).map((n) => `param${n}`),
        fc.constant('bigint' as RuinarType),
      ),
      { minLength: 0, maxLength: config.maxParams },
    ),
  ).chain(([name, paramDefs]) => {
    const seen = new Set<string>();
    const params: GeneratedParam[] = [];
    for (const [pName, pType] of paramDefs) {
      const unique = seen.has(pName) ? `${pName}X` : pName;
      seen.add(unique);
      params.push({ name: unique, type: pType });
    }

    const bigintVars = [
      ...properties.filter((p) => p.type === 'bigint').map((p) => `this.${p.name}`),
      ...params.filter((p) => p.type === 'bigint').map((p) => p.name),
    ];
    const boolVars = properties.filter((p) => p.type === 'boolean').map((p) => `this.${p.name}`);

    return fc.tuple(
      // State mutations
      fc.array(
        fc.tuple(
          fc.constantFrom(...mutableProps.filter((p) => p.type === 'bigint').map((p) => p.name)),
          arbBigintExprIR(bigintVars, 1),
        ).map(([target, value]): Stmt => ({
          kind: 'assign',
          target,
          value,
          isProperty: true,
        })),
        { minLength: 1, maxLength: Math.min(2, mutableProps.length) },
      ),
      fc.array(arbAssertStmtIR(bigintVars, boolVars), { minLength: 0, maxLength: 1 }),
    ).map(([mutations, asserts]): GeneratedMethod => ({
      name,
      visibility: 'public',
      params,
      body: [...asserts, ...mutations],
      mutatesState: true,
    }));
  });
}

/**
 * Generate a random stateless GeneratedContract IR.
 */
export const arbGeneratedContract: fc.Arbitrary<GeneratedContract> = fc
  .tuple(
    fc.integer({ min: 0, max: 99 }).map((n) => `FuzzContract${n}`),
    fc.array(
      fc.tuple(
        fc.integer({ min: 0, max: 99 }).map((n) => `prop${n}`),
        fc.constantFrom('bigint' as RuinarType, 'boolean' as RuinarType),
      ),
      { minLength: 1, maxLength: DEFAULT_CONFIG.maxProperties },
    ),
  )
  .chain(([name, propDefs]) => {
    const seen = new Set<string>();
    const properties: GeneratedProperty[] = [];
    for (const [pName, pType] of propDefs) {
      const unique = seen.has(pName) ? `${pName}X` : pName;
      seen.add(unique);
      properties.push({ name: unique, type: pType, readonly: true });
    }

    return fc
      .array(arbMethodIR(properties, DEFAULT_CONFIG), {
        minLength: 1,
        maxLength: DEFAULT_CONFIG.maxMethods,
      })
      .map((methods): GeneratedContract => ({
        name,
        parentClass: 'SmartContract',
        properties,
        methods,
      }));
  });

/**
 * Generate a random stateful GeneratedContract IR.
 */
export const arbGeneratedStatefulContract: fc.Arbitrary<GeneratedContract> = fc
  .tuple(
    fc.integer({ min: 0, max: 99 }).map((n) => `FuzzStateful${n}`),
    // At least one mutable bigint property
    fc.array(
      fc.tuple(
        fc.integer({ min: 0, max: 99 }).map((n) => `prop${n}`),
        fc.constant('bigint' as RuinarType),
        fc.boolean(), // readonly?
      ),
      { minLength: 1, maxLength: DEFAULT_CONFIG.maxProperties },
    ),
  )
  .chain(([name, propDefs]) => {
    const seen = new Set<string>();
    const properties: GeneratedProperty[] = [];
    let hasMutable = false;
    for (const [pName, pType, isReadonly] of propDefs) {
      const unique = seen.has(pName) ? `${pName}X` : pName;
      seen.add(unique);
      properties.push({ name: unique, type: pType, readonly: isReadonly });
      if (!isReadonly) hasMutable = true;
    }

    // Ensure at least one mutable property
    if (!hasMutable && properties.length > 0) {
      properties[0]!.readonly = false;
    }

    return fc
      .array(arbStatefulMethodIR(properties, DEFAULT_CONFIG), {
        minLength: 1,
        maxLength: DEFAULT_CONFIG.maxMethods,
      })
      .map((methods): GeneratedContract => ({
        name,
        parentClass: 'StatefulSmartContract',
        properties,
        methods,
      }));
  });

// ===========================================================================
// Tri-modal execution-oracle generator (issue #124)
//
// A dedicated arbitrary for the tri-modal source-vs-script oracle
// (`runTriModalExecution`). It is DELIBERATELY separate from
// `arbGeneratedContract` (which feeds the native cross-tier `--ir` path and
// must render byte-identically across all 7 tiers). This generator adds the
// three shapes that historically hid silent miscompiles and only became
// correctly compilable after #121 (loop start/step) + #130 (param shadow):
//
//   1. `for` loops with a NON-ZERO start counting up AND countdown loops.
//   2. `substr` / `cat` / `len` byte-ops over ByteString PARAMETERS.
//   3. post-loop parameter reads (a param referenced after a loop body).
//
// Every generated case is rendered to TypeScript ONLY (via `renderTypeScript`)
// and carries its own concrete constructor + method inputs, so fast-check
// PROPERTY mode shrinks both the contract structure and the failing inputs to
// a minimal repro. Cases are constructed to always be valid, in-range Rúnar
// (fixed-length ByteStrings + statically-safe substr bounds + additive,
// magnitude-bounded loop bodies) so the ONLY way the three engines disagree is
// a real compiler bug — never a harness artifact.
// ===========================================================================

/** Concrete witness/constructor value for an execution-oracle case. */
export type ExecArg = bigint | boolean | Uint8Array;

/** A fully-concrete tri-modal execution-oracle case (contract + inputs). */
export interface ExecCase {
  contract: GeneratedContract; // exactly one public method
  method: string;
  constructorArgs: Record<string, ExecArg>;
  args: ExecArg[]; // positional, in method-parameter order
}

/** Fixed ByteString length for all generated params/props — lets the byte-op
 *  generator compute statically-safe `substr` bounds. */
const EXEC_BYTES_LEN = 4;
/** |bigint inputs| bound — small enough that additive loop accumulation and a
 *  single multiply stay far inside Bitcoin script-number range. */
const EXEC_INT_MAG = 8n;

const EXEC_CMP_OPS = ['===', '!==', '<', '>', '<=', '>='] as const;

/** Reference an available bigint var (`local`, param, or `this.prop`). */
function bigintVarRef(name: string): Expr {
  return name.startsWith('this.')
    ? { kind: 'property_ref', name: name.slice(5) }
    : { kind: 'var_ref', name };
}

/** A small bigint atom: literal in [-4,4] or an available bigint var. */
function arbBigintAtom(bigintVars: string[]): fc.Arbitrary<Expr> {
  const options: fc.Arbitrary<Expr>[] = [
    fc.integer({ min: -4, max: 4 }).map((v): Expr => ({ kind: 'bigint_literal', value: BigInt(v) })),
  ];
  if (bigintVars.length > 0) {
    options.push(fc.constantFrom(...bigintVars).map(bigintVarRef));
  }
  return fc.oneof(...options);
}

/** Additive-only bigint expr (bounded magnitude) — safe inside loop bodies. */
function arbAdditiveExpr(bigintVars: string[], depth: number): fc.Arbitrary<Expr> {
  if (depth <= 0) return arbBigintAtom(bigintVars);
  return fc.oneof(
    arbBigintAtom(bigintVars),
    fc
      .tuple(
        arbAdditiveExpr(bigintVars, depth - 1),
        fc.constantFrom('+' as const, '-' as const),
        arbBigintAtom(bigintVars),
      )
      .map(([left, op, right]): Expr => ({ kind: 'binary', op, left, right })),
  );
}

/** Bounded bigint expr allowing one multiply — used only OUTSIDE loop bodies. */
function arbBoundedBigintExpr(bigintVars: string[], depth: number): fc.Arbitrary<Expr> {
  if (depth <= 0) return arbBigintAtom(bigintVars);
  return fc.oneof(
    arbBigintAtom(bigintVars),
    fc
      .tuple(
        arbAdditiveExpr(bigintVars, depth - 1),
        fc.constantFrom('+' as const, '-' as const, '*' as const),
        arbBigintAtom(bigintVars),
      )
      .map(([left, op, right]): Expr => ({ kind: 'binary', op, left, right })),
  );
}

/** A ByteString var with a statically-known MINIMUM byte length. */
interface BytesVar {
  ref: Expr;
  minLen: number;
}

/**
 * A ByteString expression built from the available ByteString vars, tracking a
 * conservative minimum length so `substr` bounds are always in range on both
 * the interpreter and the script engines (OP_SPLIT rejects out-of-range).
 */
function arbBytesExpr(
  bytesVars: BytesVar[],
  depth: number,
): fc.Arbitrary<{ expr: Expr; minLen: number }> {
  const atom = fc.constantFrom(...bytesVars).map((v) => ({ expr: v.ref, minLen: v.minLen }));
  if (depth <= 0) return atom;
  return fc.oneof(
    atom,
    // cat(a, b) — always valid; min length adds.
    fc
      .tuple(arbBytesExpr(bytesVars, depth - 1), arbBytesExpr(bytesVars, depth - 1))
      .map(([a, b]) => ({
        expr: { kind: 'call', fn: 'cat', args: [a.expr, b.expr] } as Expr,
        minLen: a.minLen + b.minLen,
      })),
    // substr(x, start, len) — bounds chosen inside [0, minLen(x)].
    arbBytesExpr(bytesVars, depth - 1).chain((base) =>
      fc.integer({ min: 0, max: base.minLen }).chain((start) =>
        fc.integer({ min: 0, max: base.minLen - start }).map((len) => ({
          expr: {
            kind: 'call',
            fn: 'substr',
            args: [
              base.expr,
              { kind: 'bigint_literal', value: BigInt(start) },
              { kind: 'bigint_literal', value: BigInt(len) },
            ],
          } as Expr,
          minLen: len,
        })),
      ),
    ),
  );
}

/** A bounded `for` loop (non-zero start counting up OR a countdown), body
 *  accumulating additively into `accVar`. */
function arbForLoop(accVar: string, bigintVars: string[]): fc.Arbitrary<ForStmt> {
  const iterVar = 'k';
  const upShape = fc
    .record({
      start: fc.integer({ min: 0, max: 4 }),
      count: fc.integer({ min: 1, max: 6 }),
      op: fc.constantFrom('<' as const, '<=' as const),
    })
    .map(({ start, count, op }) => ({
      start,
      bound: op === '<' ? start + count : start + count - 1,
      op,
      step: 1 as const,
    }));
  const downShape = fc
    .record({
      start: fc.integer({ min: 1, max: 8 }),
      countRaw: fc.integer({ min: 1, max: 6 }),
      op: fc.constantFrom('>' as const, '>=' as const),
    })
    .map(({ start, countRaw, op }) => {
      const count = Math.min(countRaw, start); // keep 1 <= count <= start
      return {
        start,
        bound: op === '>' ? start - count : start - count + 1,
        op,
        step: -1 as const,
      };
    });
  return fc.oneof(upShape, downShape).chain((shape) => {
    const loopVars = [...bigintVars, iterVar];
    return fc
      .array(
        fc
          .tuple(fc.constantFrom('+' as const, '-' as const), arbAdditiveExpr(loopVars, 1))
          .map(([op, term]): Stmt => ({
            kind: 'assign',
            target: accVar,
            value: { kind: 'binary', op, left: { kind: 'var_ref', name: accVar }, right: term },
            isProperty: false,
          })),
        { minLength: 1, maxLength: 2 },
      )
      .map((body): ForStmt => ({
        kind: 'for',
        iterVar,
        start: BigInt(shape.start),
        bound: BigInt(shape.bound),
        op: shape.op,
        step: shape.step,
        body,
      }));
  });
}

/**
 * A boolean clause that GUARANTEES a read of `param` — placed in the terminal
 * assert AFTER the loop, so every case with a loop exercises a post-loop
 * parameter read.
 */
function arbParamClause(
  param: GeneratedParam,
  bigintVars: string[],
  bytesVars: BytesVar[],
): fc.Arbitrary<Expr> {
  if (param.type === 'boolean') {
    return fc.oneof(
      fc.constant<Expr>({ kind: 'var_ref', name: param.name }),
      fc.constant<Expr>({ kind: 'unary', op: '!', operand: { kind: 'var_ref', name: param.name } }),
    );
  }
  if (param.type === 'ByteString') {
    const pv: BytesVar = { ref: { kind: 'var_ref', name: param.name }, minLen: EXEC_BYTES_LEN };
    // len(<expr using param>) <cmp> <literal in [0, 2*BYTES_LEN]>
    return fc
      .tuple(
        arbBytesExpr([pv, ...bytesVars], 2),
        fc.constantFrom(...EXEC_CMP_OPS),
        fc.integer({ min: 0, max: 2 * EXEC_BYTES_LEN }),
      )
      .map(([b, op, n]): Expr => ({
        kind: 'binary',
        op,
        left: { kind: 'call', fn: 'len', args: [b.expr] },
        right: { kind: 'bigint_literal', value: BigInt(n) },
      }));
  }
  // bigint param: (param <cmp> <bounded bigint expr>)
  return fc
    .tuple(fc.constantFrom(...EXEC_CMP_OPS), arbBoundedBigintExpr(bigintVars, 2))
    .map(([op, rhs]): Expr => ({
      kind: 'binary',
      op,
      left: { kind: 'var_ref', name: param.name },
      right: rhs,
    }));
}

/** An extra boolean clause over the accumulator / byte lengths (no guarantee
 *  of a param read — that is the param clause's job). */
function arbExtraClause(bigintVars: string[], bytesVars: BytesVar[]): fc.Arbitrary<Expr> {
  const numeric = fc
    .tuple(
      arbBoundedBigintExpr(bigintVars, 2),
      fc.constantFrom(...EXEC_CMP_OPS),
      arbBoundedBigintExpr(bigintVars, 2),
    )
    .map(([left, op, right]): Expr => ({ kind: 'binary', op, left, right }));
  if (bytesVars.length === 0) return numeric;
  const bytesEq = fc
    .tuple(arbBytesExpr(bytesVars, 2), arbBytesExpr(bytesVars, 2), fc.constantFrom('===' as const, '!==' as const))
    .map(([a, b, op]): Expr => ({ kind: 'binary', op, left: a.expr, right: b.expr }));
  return fc.oneof(numeric, bytesEq);
}

/** Generate the body of the single exec-oracle method for the given props/params. */
function arbExecMethodBody(
  props: GeneratedProperty[],
  params: GeneratedParam[],
): fc.Arbitrary<Stmt[]> {
  const bigintPropParamVars = [
    ...props.filter((p) => p.type === 'bigint').map((p) => `this.${p.name}`),
    ...params.filter((p) => p.type === 'bigint').map((p) => p.name),
  ];
  const bytesBase: BytesVar[] = [
    ...props
      .filter((p) => p.type === 'ByteString')
      .map((p): BytesVar => ({ ref: { kind: 'property_ref', name: p.name }, minLen: EXEC_BYTES_LEN })),
    ...params
      .filter((p) => p.type === 'ByteString')
      .map((p): BytesVar => ({ ref: { kind: 'var_ref', name: p.name }, minLen: EXEC_BYTES_LEN })),
  ];

  return fc
    .record({
      accInit: arbAdditiveExpr(bigintPropParamVars, 1),
      includeLoop: fc.boolean(),
      loopBuilder: arbForLoop('acc', bigintPropParamVars),
      numByteDecls: bytesBase.length > 0 ? fc.integer({ min: 0, max: 2 }) : fc.constant(0),
      byteExprs: fc.array(arbBytesExpr(bytesBase.length > 0 ? bytesBase : [{ ref: { kind: 'bigint_literal', value: 0n }, minLen: 0 }], 2), {
        minLength: 0,
        maxLength: 2,
      }),
      paramIdx: fc.integer({ min: 0, max: Math.max(0, params.length - 1) }),
      useExtra: fc.boolean(),
      logicalOp: fc.constantFrom('&&' as const, '||' as const),
      extra: arbExtraClause(['acc', ...bigintPropParamVars], bytesBase),
    })
    .chain((cfg) => {
      const body: Stmt[] = [];
      // Accumulator local (mutable so the loop can update it).
      body.push({ kind: 'var_decl', name: 'acc', type: 'bigint', value: cfg.accInit, mutable: true });
      const bigintVars = ['acc', ...bigintPropParamVars];

      if (cfg.includeLoop) body.push(cfg.loopBuilder);

      // Optional byte-op locals (only meaningful when ByteString vars exist).
      const bytesVars = [...bytesBase];
      if (bytesBase.length > 0) {
        const n = Math.min(cfg.numByteDecls, cfg.byteExprs.length);
        for (let i = 0; i < n; i++) {
          const name = `b${i}`;
          const be = cfg.byteExprs[i]!;
          body.push({ kind: 'var_decl', name, type: 'ByteString', value: be.expr, mutable: false });
          bytesVars.push({ ref: { kind: 'var_ref', name }, minLen: be.minLen });
        }
      }

      // Terminal assert: a guaranteed param read, optionally &&/|| an extra clause.
      const param = params[Math.min(cfg.paramIdx, params.length - 1)]!;
      return arbParamClause(param, bigintVars, bytesVars).map((clause): Stmt[] => {
        const condition: Expr = cfg.useExtra
          ? { kind: 'binary', op: cfg.logicalOp, left: clause, right: cfg.extra }
          : clause;
        return [...body, { kind: 'assert', condition }];
      });
    });
}

/** A random value for a constructor prop / method param of the given type. */
function arbExecValue(type: RuinarType): fc.Arbitrary<ExecArg> {
  if (type === 'boolean') return fc.boolean();
  if (type === 'ByteString') {
    return fc.uint8Array({ minLength: EXEC_BYTES_LEN, maxLength: EXEC_BYTES_LEN });
  }
  // bigint (default)
  return fc.bigInt({ min: -EXEC_INT_MAG, max: EXEC_INT_MAG });
}

const EXEC_PROP_TYPES = ['bigint', 'ByteString'] as const;
const EXEC_PARAM_TYPES = ['bigint', 'boolean', 'ByteString'] as const;

/** Generate the structural shell (contract + its single method). */
const arbExecStructure: fc.Arbitrary<{ contract: GeneratedContract; method: GeneratedMethod }> = fc
  .record({
    name: fc.integer({ min: 0, max: 9999 }).map((n) => `ExecFuzz${n}`),
    propDefs: fc.array(
      fc.tuple(fc.integer({ min: 0, max: 9 }), fc.constantFrom(...EXEC_PROP_TYPES)),
      { minLength: 0, maxLength: 2 },
    ),
    methodName: fc.integer({ min: 0, max: 9 }).map((n) => `run${n}`),
    paramDefs: fc.array(
      fc.tuple(fc.integer({ min: 0, max: 9 }), fc.constantFrom(...EXEC_PARAM_TYPES)),
      { minLength: 1, maxLength: 3 },
    ),
  })
  .chain((s) => {
    // De-dup property names.
    const propSeen = new Set<string>();
    const properties: GeneratedProperty[] = [];
    for (const [n, type] of s.propDefs) {
      let name = `prop${n}`;
      while (propSeen.has(name)) name += 'X';
      propSeen.add(name);
      properties.push({ name, type, readonly: true });
    }
    // De-dup parameter names.
    const paramSeen = new Set<string>();
    const params: GeneratedParam[] = [];
    for (const [n, type] of s.paramDefs) {
      let name = `param${n}`;
      while (paramSeen.has(name)) name += 'X';
      paramSeen.add(name);
      params.push({ name, type });
    }
    return arbExecMethodBody(properties, params).map((body) => {
      const method: GeneratedMethod = {
        name: s.methodName,
        visibility: 'public',
        params,
        body,
        mutatesState: false,
      };
      const contract: GeneratedContract = {
        name: s.name,
        parentClass: 'SmartContract',
        properties,
        methods: [method],
      };
      return { contract, method };
    });
  });

/**
 * A fully-concrete tri-modal execution-oracle case: a stateless contract with
 * loops + byte-ops + post-loop param reads, plus concrete constructor + method
 * inputs. fast-check property mode shrinks both the structure and the inputs to
 * a minimal repro on any tri-modal disagreement.
 */
export const arbExecCase: fc.Arbitrary<ExecCase> = arbExecStructure.chain(({ contract, method }) => {
  const ctorEntries = contract.properties.map(
    (p) => [p.name, arbExecValue(p.type)] as const,
  );
  const ctorArb: fc.Arbitrary<Record<string, ExecArg>> =
    ctorEntries.length === 0
      ? fc.constant({})
      : fc.record(Object.fromEntries(ctorEntries) as Record<string, fc.Arbitrary<ExecArg>>);
  const argArbs = method.params.map((p) => arbExecValue(p.type));
  const argsArb: fc.Arbitrary<ExecArg[]> =
    argArbs.length === 0 ? fc.constant([]) : fc.tuple(...argArbs);
  return fc.tuple(ctorArb, argsArb).map(
    ([constructorArgs, args]): ExecCase => ({
      contract,
      method: method.name,
      constructorArgs,
      args,
    }),
  );
});
