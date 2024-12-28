import { describe, expect, test } from "vitest";
import {
  ASTNode,
  parsePackage,
  term,
  stripAST,
  identifier2str,
  strip,
  identifier2,
  parseLineComment,
  identifier,
  parenthesis,
  abstraction,
  type,
  definition,
  parseFile,
  resync,
  pi,
  Def,
  adt,
  caseStatement,
  caseBranch,
  IntLit,
  Ann,
  application,
  ifStatement,
  integerLiteral,
  letStatement,
  listLiteral,
  self,
  stringLiteral,
  Ref,
  block,
  ParseError,
} from "./ast";
import {
  bind,
  char,
  many,
  parseErrorDiagnostic,
  Stream,
  Result,
  Parser,
  any13,
  either,
  lazy,
  lspc,
  pure,
  spc,
  str,
  any3,
  map,
  many1,
} from "./parser";
import { TypecheckError } from "./typecheck";
import { foldTreeCtx, printDiagnostic } from "./inspect";

export const ts = (s: string): Stream => ({
  src: s,
  idx: 0,
});

export const result = <T>(x: Result<T>) => {
  if (x._ == "parseerror") {
    const msg = parseErrorDiagnostic(x);
    throw msg;
  } else {
    return x.value;
  }
};

export type IntPlus = {
  _: "iplus";
  lhs: Expression;
  rhs: Expression;
};

export const IntPlus = (lhs: Expression, rhs: Expression): IntPlus => ({
  _: "iplus",
  lhs: lhs,
  rhs: rhs,
});

export type IntMul = {
  _: "imul";
  lhs: Expression;
  rhs: Expression;
};

export const IntMul = (lhs: Expression, rhs: Expression): IntMul => ({
  _: "imul",
  lhs: lhs,
  rhs: rhs,
});

type Expression = IntLit | IntPlus | IntMul;

// export const reference: Parser<Expression> = map(identifier, (result: string) =>
//   Ref(result)
// );
const opParser = either(char("+"), char("*"));

const expression =
  (min: number) =>
  (s: Stream): Result<Expression> => {
    // An expression consists of an integer literal, optionally followed by
    // operators and literals.
    // The job of this function is to parse the expression tree while
    // maintaining correct precedence.
    // It is an implementation of the standard Pratt parsing algorithm.

    // Handle parentheses.
    let paren = char("(")(s);
    if (paren._ != "parseerror") {
      const ex = expression(0)(paren.stream);
      if (ex._ == "parseerror") {
        return ex;
      }
      let closeparen = char(")")(ex.stream);
      if (closeparen._ == "parseerror") {
        return closeparen;
      }
      return {
        _: "outputvalue",
        value: ex.value,
        stream: closeparen.stream,
      };
    }

    let acc: Result<Expression> = integerLiteral(s);
    if (acc._ == "parseerror") {
      return acc;
    }

    // Now parse many `op int op int op int ...`
    while (true) {
      // Peek the next operator, if there is one.
      const op = opParser(acc.stream);
      if (op._ == "parseerror") {
        break;
      }
      // Check the binding power of the operator we just peeked. If the binding
      // power of the current expression (acc) is higher, then we don't parse
      // the operator and instead we terminate this sub-expression. This allows
      // the operator to be inserted into the upper level of the tree.
      if (op.value == "+" && min < 2) {
        // Continue parsing, setting the binding power appropriately.
        const rhs = expression(2)(op.stream);
        if (rhs._ == "parseerror") {
          return rhs;
        }
        acc = {
          _: "outputvalue",
          value: IntPlus(acc.value, rhs.value),
          stream: rhs.stream,
        };
      } else if (op.value == "*" && min < 4) {
        const rhs = expression(4)(op.stream);
        if (rhs._ == "parseerror") {
          return rhs;
        }
        acc = {
          _: "outputvalue",
          value: IntMul(acc.value, rhs.value),
          stream: rhs.stream,
        };
      } else {
        break;
      }
    }

    return acc;
  };

// serialise outputs the term tree in the same syntax as the typescript
// implementation. This is useful for quickly generating code for a term to be
// used in tests.
export function serialise(t: Expression, d: number = 0): string {
  switch (t._) {
    // case "ref":
    //   return `Ref("${t.name}")`;
    case "int":
      return `IntLit(${t.num})`;
    // case "err":
    //   return `ParseError(${t.msg})`;
    case "iplus":
      return `IntPlus(${serialise(t.lhs)}, ${serialise(t.rhs)})`;
    case "imul":
      return `IntMul(${serialise(t.lhs)}, ${serialise(t.rhs)})`;
  }
}

const st = (s: string): string => serialise(result(expression(0)(ts(s))));

describe("math", () => {
  test("should parse integer addition binary operator", () =>
    expect(st("1+2")).toBe(`IntPlus(IntLit(1), IntLit(2))`));

  test("should parse integer addition with left associativity", () =>
    // 1+2+3 === (1+2)+3
    expect(st("1+2+3")).toBe(
      `IntPlus(IntPlus(IntLit(1), IntLit(2)), IntLit(3))`
    ));

  test("should parse integer multiplication binary operator", () =>
    expect(st("1*2")).toBe(`IntMul(IntLit(1), IntLit(2))`));

  test("should parse integer multiplication with left associativity", () =>
    // 1*2*3 === (1*2)*3
    expect(st("1*2*3")).toBe(
      `IntMul(IntMul(IntLit(1), IntLit(2)), IntLit(3))`
    ));

  test("should parse integer multiplication with higher associativity than addition", () =>
    // 1+2*3 === 1+(2*3)
    expect(st("1+2*3")).toBe(
      `IntPlus(IntLit(1), IntMul(IntLit(2), IntLit(3)))`
    ));

  test("should parse integer multiplication with higher associativity than addition 2", () =>
    // 1*2+3 === (1*2)+3
    expect(st("1*2+3")).toBe(
      `IntPlus(IntMul(IntLit(1), IntLit(2)), IntLit(3))`
    ));

  test("should parse parenthesis with the highest precedence", () =>
    expect(st("1*(2+3)")).toBe(
      `IntMul(IntLit(1), IntPlus(IntLit(2), IntLit(3)))`
    ));
});
