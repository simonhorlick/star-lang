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
  any4,
  any5,
  any6,
  any7,
  any8,
  any,
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
  _: "add";
  lhs: Expression;
  rhs: Expression;
};

export const IntPlus = (lhs: Expression, rhs: Expression): IntPlus => ({
  _: "add",
  lhs: lhs,
  rhs: rhs,
});

export type IntSub = {
  _: "sub";
  lhs: Expression;
  rhs: Expression;
};

export const IntSub = (lhs: Expression, rhs: Expression): IntSub => ({
  _: "sub",
  lhs: lhs,
  rhs: rhs,
});

export const IntNeg = (exp: Expression): IntNeg => ({
  _: "neg",
  exp: exp,
});

export type IntMul = {
  _: "mul";
  lhs: Expression;
  rhs: Expression;
};

export const IntMul = (lhs: Expression, rhs: Expression): IntMul => ({
  _: "mul",
  lhs: lhs,
  rhs: rhs,
});

export type IntDiv = {
  _: "div";
  lhs: Expression;
  rhs: Expression;
};

export const IntDiv = (lhs: Expression, rhs: Expression): IntDiv => ({
  _: "div",
  lhs: lhs,
  rhs: rhs,
});

export type Idx = {
  _: "idx";
  arr: Expression;
  idx: Expression;
};

export const Idx = (arr: Expression, idx: Expression): Idx => ({
  _: "idx",
  arr: arr,
  idx: idx,
});

export type Gt = {
  _: "gt";
  lhs: Expression;
  rhs: Expression;
};

export const Gt = (lhs: Expression, rhs: Expression): Gt => ({
  _: "gt",
  lhs: lhs,
  rhs: rhs,
});

export type Lt = {
  _: "lt";
  lhs: Expression;
  rhs: Expression;
};

export const Lt = (lhs: Expression, rhs: Expression): Lt => ({
  _: "lt",
  lhs: lhs,
  rhs: rhs,
});

export type Gte = {
  _: "gte";
  lhs: Expression;
  rhs: Expression;
};

export const Gte = (lhs: Expression, rhs: Expression): Gte => ({
  _: "gte",
  lhs: lhs,
  rhs: rhs,
});

export type Lte = {
  _: "lte";
  lhs: Expression;
  rhs: Expression;
};

export const Lte = (lhs: Expression, rhs: Expression): Lte => ({
  _: "lte",
  lhs: lhs,
  rhs: rhs,
});

export type App = {
  _: "app";
  lhs: Expression;
  rhs: Expression;
};

export const App = (lhs: Expression, rhs: Expression): App => ({
  _: "app",
  lhs: lhs,
  rhs: rhs,
});

export type IntNeg = {
  _: "neg";
  exp: Expression;
};

// List concatenation operator.
export type Cat = {
  _: "cat";
  lhs: Expression;
  rhs: Expression;
};

export const Cat = (lhs: Expression, rhs: Expression): Cat => ({
  _: "cat",
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

// Π is the type of functions.
export type Pi = {
  _: "pi";
  from: Expression;
  body: Expression;
  name: string; // name of the binder
};

export const Pi = (name: string, from: Expression, to: Expression): Pi => ({
  _: "pi",
  from: from,
  body: to,
  name: name,
});

// Π is the type of functions.
export type Ann = {
  _: "ann";
  term: Expression;
  type: Expression;
};

export const Ann = (term: Expression, type: Expression): Ann => ({
  _: "ann",
  term: term,
  type: type,
});

type Expression =
  | IntLit
  | IntPlus
  | IntSub
  | IntMul
  | IntDiv
  | IntNeg
  | Comp
  | App
  | Ref
  | Pi
  | Ann
  | Idx
  | Cat
  | Gt
  | Lt
  | Gte
  | Lte;

export const reference: Parser<Expression> = map(identifier, (result: string) =>
  Ref(result)
);

const opParser = spc(
  any(
    str("++"),
    str("->"),
    str(">="),
    str("<="),
    char(">"),
    char("<"),
    char("+"),
    char("-"),
    char("*"),
    char("/"),
    char("."),
    char("("),
    char(":"),
    char("[")
  )
);

const getBindingPower = (op: string): [number, number] => {
  if (op == "+" || op == "-") {
    return [1, 2];
  } else if (op == "*" || op == "/") {
    return [3, 4];
  } else if (op == "(") {
    return [5, 6];
  } else if (op == ".") {
    return [8, 7];
  } else if (op == "->") {
    return [10, 9];
  } else if (op == ":") {
    return [11, 12];
  } else if (op == "[") {
    return [13, 14];
  } else if (op == "++") {
    return [15, 16];
  } else if (op == ">" || op == "<" || op == ">=" || op == "<=") {
    return [17, 18];
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

    let acc: Result<Expression> = either(integerLiteral, reference)(s);
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
      } else if (op.value == "-" && min < leftBindingPower) {
        const rhs = expression(rightBindingPower)(op.stream);
        if (rhs._ == "parseerror") {
          return rhs;
        }
        acc = {
          _: "outputvalue",
          value: IntSub(acc.value, rhs.value),
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
      } else if (op.value == "/" && min < leftBindingPower) {
        const rhs = expression(rightBindingPower)(op.stream);
        if (rhs._ == "parseerror") {
          return rhs;
        }
        acc = {
          _: "outputvalue",
          value: IntDiv(acc.value, rhs.value),
          stream: rhs.stream,
        };
      } else if (op.value == ">" && min < leftBindingPower) {
        const rhs = expression(rightBindingPower)(op.stream);
        if (rhs._ == "parseerror") {
          return rhs;
        }
        acc = {
          _: "outputvalue",
          value: Gt(acc.value, rhs.value),
          stream: rhs.stream,
        };
      } else if (op.value == "<" && min < leftBindingPower) {
        const rhs = expression(rightBindingPower)(op.stream);
        if (rhs._ == "parseerror") {
          return rhs;
        }
        acc = {
          _: "outputvalue",
          value: Lt(acc.value, rhs.value),
          stream: rhs.stream,
        };
      } else if (op.value == ">=" && min < leftBindingPower) {
        const rhs = expression(rightBindingPower)(op.stream);
        if (rhs._ == "parseerror") {
          return rhs;
        }
        acc = {
          _: "outputvalue",
          value: Gte(acc.value, rhs.value),
          stream: rhs.stream,
        };
      } else if (op.value == "<=" && min < leftBindingPower) {
        const rhs = expression(rightBindingPower)(op.stream);
        if (rhs._ == "parseerror") {
          return rhs;
        }
        acc = {
          _: "outputvalue",
          value: Lte(acc.value, rhs.value),
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
      } else if (op.value == "(" && min < leftBindingPower) {
        // Function application `f(x)` is parsed as an infix `(` followed by a
        // closing `)`.
        const rhs = expression(rightBindingPower)(op.stream);
        if (rhs._ == "parseerror") {
          return rhs;
        }
        let closeparen = char(")")(rhs.stream);
        if (closeparen._ == "parseerror") {
          return closeparen;
        }
        acc = {
          _: "outputvalue",
          value: App(acc.value, rhs.value),
          stream: closeparen.stream,
        };
      } else if (op.value == "[" && min < leftBindingPower) {
        // List indexing operator `a[i]` is parsed as an infix `[` followed by
        // a closing `]`.
        const rhs = expression(rightBindingPower)(op.stream);
        if (rhs._ == "parseerror") {
          return rhs;
        }
        let closeparen = char("]")(rhs.stream);
        if (closeparen._ == "parseerror") {
          return closeparen;
        }
        acc = {
          _: "outputvalue",
          value: Idx(acc.value, rhs.value),
          stream: closeparen.stream,
        };
      } else if (op.value == "->" && min < leftBindingPower) {
        const rhs = expression(rightBindingPower)(op.stream);
        if (rhs._ == "parseerror") {
          return rhs;
        }
        acc = {
          _: "outputvalue",
          value: Pi("", acc.value, rhs.value),
          stream: rhs.stream,
        };
      } else if (op.value == "++" && min < leftBindingPower) {
        const rhs = expression(rightBindingPower)(op.stream);
        if (rhs._ == "parseerror") {
          return rhs;
        }
        acc = {
          _: "outputvalue",
          value: Cat(acc.value, rhs.value),
          stream: rhs.stream,
        };
      } else if (op.value == ":" && min < leftBindingPower) {
        const rhs = expression(rightBindingPower)(op.stream);
        if (rhs._ == "parseerror") {
          return rhs;
        }
        acc = {
          _: "outputvalue",
          value: Ann(acc.value, rhs.value),
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
    case "ref":
      return `Ref("${t.name}")`;
    case "int":
      return `IntLit(${t.num})`;
    // case "err":
    //   return `ParseError(${t.msg})`;
    case "neg":
      return `IntNeg(${serialise(t.exp)})`;
    case "add":
      return `IntPlus(${serialise(t.lhs)}, ${serialise(t.rhs)})`;
    case "sub":
      return `IntSub(${serialise(t.lhs)}, ${serialise(t.rhs)})`;
    case "mul":
      return `IntMul(${serialise(t.lhs)}, ${serialise(t.rhs)})`;
    case "div":
      return `IntDiv(${serialise(t.lhs)}, ${serialise(t.rhs)})`;
    case "comp":
      return `Comp(${serialise(t.lhs)}, ${serialise(t.rhs)})`;
    case "app":
      return `App(${serialise(t.lhs)}, ${serialise(t.rhs)})`;
    case "pi":
      return `Pi("${t.name}", ${serialise(t.from)}, ${serialise(t.body)})`;
    case "ann":
      return `Ann(${serialise(t.term)}, ${serialise(t.type)})`;
    case "idx":
      return `Idx(${serialise(t.arr)}, ${serialise(t.idx)})`;
    case "cat":
      return `Cat(${serialise(t.lhs)}, ${serialise(t.rhs)})`;
    case "gt":
      return `Gt(${serialise(t.lhs)}, ${serialise(t.rhs)})`;
    case "lt":
      return `Lt(${serialise(t.lhs)}, ${serialise(t.rhs)})`;
    case "gte":
      return `Gte(${serialise(t.lhs)}, ${serialise(t.rhs)})`;
    case "lte":
      return `Lte(${serialise(t.lhs)}, ${serialise(t.rhs)})`;
    default:
      throw new Error(`unhandled node`);
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

  test("should parse integer subtraction binary operator", () =>
    expect(st("1-2")).toBe(`IntSub(IntLit(1), IntLit(2))`));

  test("should parse integer subtraction with left associativity", () =>
    // 1-2-3 === (1-2)-3
    expect(st("1-2-3")).toBe(
      `IntSub(IntSub(IntLit(1), IntLit(2)), IntLit(3))`
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

  test("should parse integer division binary operator", () =>
    expect(st("1/2")).toBe(`IntDiv(IntLit(1), IntLit(2))`));

  test("should parse multiple parenthesis", () =>
    expect(st("((1))")).toBe(`IntLit(1)`));

  test("should parse unary negation", () =>
    expect(st("-1")).toBe(`IntNeg(IntLit(1))`));

  test("should parse function composition with right associativity", () =>
    // f . g . h === f . (g . h)
    expect(st("f . g . h")).toBe(`Comp(Ref("f"), Comp(Ref("g"), Ref("h")))`));

  test("should parse function application", () =>
    expect(st("f(x)")).toBe(`App(Ref("f"), Ref("x"))`));

  test("should parse function application with multiple arguments", () =>
    // f(x)(y) === (f(x))(y)
    expect(st("f(x)(y)")).toBe(`App(App(Ref("f"), Ref("x")), Ref("y"))`));

  test("should parse arrow operator with right associativity", () =>
    // a -> b -> c === a -> (b -> c)
    expect(st("a->b->c")).toBe(`Pi("", Ref("a"), Pi("", Ref("b"), Ref("c")))`));

  test("should parse type annotation", () =>
    // a:A:B === (a:A):B
    expect(st("a:A:B")).toBe(`Ann(Ann(Ref("a"), Ref("A")), Ref("B"))`));

  test("should parse type annotation with high precedence", () =>
    // a:Int + b:Int === (a:Int) + (b:Int)
    expect(st("a:Int+b:Int")).toBe(
      `IntPlus(Ann(Ref("a"), Ref("Int")), Ann(Ref("b"), Ref("Int")))`
    ));

  test("should parse list indexing operator", () =>
    expect(st("a[i]")).toBe(`Idx(Ref("a"), Ref("i"))`));

  test("should parse list concatenation operator with left associativity", () =>
    expect(st("as++bs++cs")).toBe(`Cat(Cat(Ref("as"), Ref("bs")), Ref("cs"))`));

  test("should parse greater-than binary operator", () =>
    expect(st("a>b")).toBe(`Gt(Ref("a"), Ref("b"))`));

  test("should parse greater-than-or-equal binary operator", () =>
    expect(st("a>=b")).toBe(`Gte(Ref("a"), Ref("b"))`));

  test("should parse less-than binary operator", () =>
    expect(st("a<b")).toBe(`Lt(Ref("a"), Ref("b"))`));

  test("should parse less-than-or-equal binary operator", () =>
    expect(st("a<=b")).toBe(`Lte(Ref("a"), Ref("b"))`));

  test("should parse less-than and greater-than with the same precedence", () =>
    // a<b>c === (a<b)>c
    expect(st("a<b>c")).toBe(`Gt(Lt(Ref("a"), Ref("b")), Ref("c"))`));
});
