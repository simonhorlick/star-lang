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

export type IntNeg = {
  _: "ineg";
  exp: Expression;
};

export const IntNeg = (exp: Expression): IntNeg => ({
  _: "ineg",
  exp: exp,
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

// Function composition operator `f . g`.
export type Comp = {
  _: "comp";
  lhs: Expression;
  rhs: Expression;
};

export const Comp = (lhs: Expression, rhs: Expression): Comp => ({
  _: "comp",
  lhs: lhs,
  rhs: rhs,
});

type Expression = IntLit | IntPlus | IntMul | IntNeg | Comp;

// export const reference: Parser<Expression> = map(identifier, (result: string) =>
//   Ref(result)
// );
const opParser = any3(char("+"), char("*"), char("."));

const getBindingPower = (op: string): [number, number] => {
  if (op == "+") {
    return [1, 2];
  } else if (op == "*") {
    return [3, 4];
  } else if (op == ".") {
    return [6, 5];
  } else {
    throw new Error("unknown operator");
  }
};

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

    let neg = char("-")(s);
    if (neg._ != "parseerror") {
      const ex = expression(0)(neg.stream);
      if (ex._ == "parseerror") {
        return ex;
      }
      return {
        _: "outputvalue",
        value: IntNeg(ex.value),
        stream: ex.stream,
      };
    }

    let acc: Result<Expression> = integerLiteral(s);
    if (acc._ == "parseerror") {
      return acc;
    }

    // Now parse many `op a op b op c ...`
    while (true) {
      // Peek the next operator, if there is one.
      const op = opParser(acc.stream);
      if (op._ == "parseerror") {
        break;
      }
      const [leftBindingPower, rightBindingPower] = getBindingPower(op.value);

      // Consider the following expression `1 + 2 * 3`. The parse tree is built
      // from left-to-right starting with `1`. The next operator is `+` which
      // has a left binding power of 1 so we continue parsing the `2*3` with a
      // minimum binding power of 1.
      //
      //     +
      //    / \
      //   1   ?
      //
      // There are two possibilities to construct the parse tree. The first is
      // that the `2*3` is added in the place of the question mark. The second
      // is that the `2` is added in the place of the question mark and the `*3`
      // is added at the root of the tree, corresponding to the following
      // expressions:
      //
      //     +
      //    / \
      //   1   *                corresponding to 1+(2*3)
      //      / \
      //     2   3
      //
      //       *
      //      / \
      //     +   3              corresponding to (1+2)*3
      //    / \
      //   1   2
      //
      // Because the minimum binding power is 1, when we reach the `*` we know
      // that we can add it at this point in the tree. If the binding power
      // would be less, we would have to add the 2 and recurse back up to add
      // the rest of the expression.

      if (op.value == "+" && min < leftBindingPower) {
        // Continue parsing, setting the binding power appropriately.
        const rhs = expression(rightBindingPower)(op.stream);
        if (rhs._ == "parseerror") {
          return rhs;
        }
        acc = {
          _: "outputvalue",
          value: IntPlus(acc.value, rhs.value),
          stream: rhs.stream,
        };
      } else if (op.value == "*" && min < leftBindingPower) {
        const rhs = expression(rightBindingPower)(op.stream);
        if (rhs._ == "parseerror") {
          return rhs;
        }
        acc = {
          _: "outputvalue",
          value: IntMul(acc.value, rhs.value),
          stream: rhs.stream,
        };
      } else if (op.value == "." && min < leftBindingPower) {
        const rhs = expression(rightBindingPower)(op.stream);
        if (rhs._ == "parseerror") {
          return rhs;
        }
        acc = {
          _: "outputvalue",
          value: Comp(acc.value, rhs.value),
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
    case "ineg":
      return `IntNeg(${serialise(t.exp)})`;
    case "iplus":
      return `IntPlus(${serialise(t.lhs)}, ${serialise(t.rhs)})`;
    case "imul":
      return `IntMul(${serialise(t.lhs)}, ${serialise(t.rhs)})`;
    case "comp":
      return `Comp(${serialise(t.lhs)}, ${serialise(t.rhs)})`;
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

  test("should parse unary negation", () =>
    expect(st("-1")).toBe(`IntNeg(IntLit(1))`));

  test("should parse function composition with right associativity", () =>
    // f . g . h === f . (g . h)
    expect(st("1.2.3")).toBe(`Comp(IntLit(1), Comp(IntLit(2), IntLit(3)))`));
});
