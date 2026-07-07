/**
 * Language-neutral intermediate representation for generated Rúnar contracts.
 *
 * The fuzzer generates contracts at this level, then renderers convert them
 * to source code in each target language (TypeScript, Go, Rust, Python,
 * Zig, Ruby, Solidity, Move).
 */

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export type RuinarType =
  | 'bigint'
  | 'boolean'
  | 'ByteString'
  | 'PubKey'
  | 'Sig'
  | 'Addr'
  | 'Sha256'
  | 'Ripemd160';

// ---------------------------------------------------------------------------
// Expressions
// ---------------------------------------------------------------------------

export type Expr =
  | BigintLiteral
  | BoolLiteral
  | ByteStringLiteral
  | VarRef
  | PropertyRef
  | BinaryExpr
  | UnaryExpr
  | CallExpr
  | TernaryExpr;

export interface BigintLiteral {
  kind: 'bigint_literal';
  value: bigint;
}

export interface BoolLiteral {
  kind: 'bool_literal';
  value: boolean;
}

export interface ByteStringLiteral {
  kind: 'bytestring_literal';
  hex: string; // e.g., 'aabbcc'
}

export interface VarRef {
  kind: 'var_ref';
  name: string;
}

export interface PropertyRef {
  kind: 'property_ref';
  name: string; // camelCase — renderers convert to snake_case for Python/Rust/Ruby
}

export type BinaryOp =
  | '+' | '-' | '*' | '/' | '%'
  | '===' | '!==' | '<' | '>' | '<=' | '>='
  | '&&' | '||';

export interface BinaryExpr {
  kind: 'binary';
  op: BinaryOp;
  left: Expr;
  right: Expr;
}

export interface UnaryExpr {
  kind: 'unary';
  op: '!' | '-';
  operand: Expr;
}

/** Built-in function call (hash160, sha256, abs, min, max, etc.) */
export interface CallExpr {
  kind: 'call';
  fn: string; // camelCase name (e.g., 'hash160', 'checkSig', 'safediv')
  args: Expr[];
}

export interface TernaryExpr {
  kind: 'ternary';
  condition: Expr;
  consequent: Expr;
  alternate: Expr;
}

// ---------------------------------------------------------------------------
// Statements
// ---------------------------------------------------------------------------

export type Stmt =
  | VarDeclStmt
  | AssertStmt
  | AssignStmt
  | IfStmt
  | ForStmt
  | ExprStmt;

export interface VarDeclStmt {
  kind: 'var_decl';
  name: string;
  type: RuinarType;
  value: Expr;
  mutable: boolean;
}

export interface AssertStmt {
  kind: 'assert';
  condition: Expr;
}

export interface AssignStmt {
  kind: 'assign';
  target: string; // property name (camelCase)
  value: Expr;
  isProperty: boolean; // true = this.propName, false = local var
}

export interface IfStmt {
  kind: 'if';
  condition: Expr;
  then: Stmt[];
  else_?: Stmt[];
}

/**
 * Bounded `for` loop with a compile-time-constant iteration count. Models the
 * shapes the Rúnar compiler unrolls (issue #121): a NON-ZERO start counting up
 * (`step: 1`, `op: '<' | '<='`) or a countdown (`step: -1`, `op: '>' | '>='`).
 * `start` and `bound` are integer literals; the loop variable (`iterVar`,
 * `bigint`) is available inside `body` and goes out of scope after it.
 */
export interface ForStmt {
  kind: 'for';
  iterVar: string;
  start: bigint;
  bound: bigint;
  op: '<' | '<=' | '>' | '>=';
  step: 1 | -1;
  body: Stmt[];
}

export interface ExprStmt {
  kind: 'expr';
  expr: Expr;
}

// ---------------------------------------------------------------------------
// Contract structure
// ---------------------------------------------------------------------------

export interface GeneratedProperty {
  name: string; // camelCase
  type: RuinarType;
  readonly: boolean;
  initializer?: Expr; // only literal values
}

export interface GeneratedParam {
  name: string; // camelCase
  type: RuinarType;
}

export interface GeneratedMethod {
  name: string; // camelCase
  visibility: 'public' | 'private';
  params: GeneratedParam[];
  body: Stmt[];
  mutatesState: boolean; // true if any AssignStmt targets a property
}

export interface GeneratedContract {
  name: string; // PascalCase
  parentClass: 'SmartContract' | 'StatefulSmartContract';
  properties: GeneratedProperty[];
  methods: GeneratedMethod[];
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/** Convert camelCase to snake_case. */
export function toSnakeCase(name: string): string {
  return name.replace(/([A-Z])/g, '_$1').toLowerCase().replace(/^_/, '');
}

/** Convert camelCase to PascalCase. */
export function toPascalCase(name: string): string {
  return name.charAt(0).toUpperCase() + name.slice(1);
}

/** Get all imports needed by a contract's expressions. */
export function collectUsedFunctions(contract: GeneratedContract): Set<string> {
  const fns = new Set<string>();

  function walkExpr(expr: Expr): void {
    switch (expr.kind) {
      case 'call':
        fns.add(expr.fn);
        expr.args.forEach(walkExpr);
        break;
      case 'binary':
        walkExpr(expr.left);
        walkExpr(expr.right);
        break;
      case 'unary':
        walkExpr(expr.operand);
        break;
      case 'ternary':
        walkExpr(expr.condition);
        walkExpr(expr.consequent);
        walkExpr(expr.alternate);
        break;
    }
  }

  function walkStmt(stmt: Stmt): void {
    switch (stmt.kind) {
      case 'var_decl':
        walkExpr(stmt.value);
        break;
      case 'assert':
        walkExpr(stmt.condition);
        break;
      case 'assign':
        walkExpr(stmt.value);
        break;
      case 'if':
        walkExpr(stmt.condition);
        stmt.then.forEach(walkStmt);
        stmt.else_?.forEach(walkStmt);
        break;
      case 'for':
        stmt.body.forEach(walkStmt);
        break;
      case 'expr':
        walkExpr(stmt.expr);
        break;
    }
  }

  for (const method of contract.methods) {
    method.body.forEach(walkStmt);
  }

  return fns;
}

/** Get all types used in properties and parameters. */
export function collectUsedTypes(contract: GeneratedContract): Set<RuinarType> {
  const types = new Set<RuinarType>();
  for (const prop of contract.properties) {
    types.add(prop.type);
  }
  for (const method of contract.methods) {
    for (const param of method.params) {
      types.add(param.type);
    }
  }
  return types;
}
