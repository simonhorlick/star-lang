import { describe, expect, test } from "@jest/globals";

import {
  char,
  either,
  str,
  many,
  optional,
  line,
  Result,
  Stream,
  bind,
  pure,
  seq,
  many1,
  indexToLineCol,
} from "./parser";
import {
  parsePackage,
  parseLineComment,
  identifier,
  parenthesis,
  abstraction,
  term,
  application,
  definition,
  reference,
  type,
  arrow,
} from "./ast";
import { Abs, App, Pi, Def, Ref } from "./ast";

const success = <T>(x: Result<T>) => x.type == "outputvalue";

const ts = (s: string): Stream => ({
  src: `parsed${s}`,
  idx: 6,
});

const result = <T>(x: Result<T>) => {
  if (x.type == "parseerror") {
    const loc = indexToLineCol(x.stream.src, x.stream.idx);
    return `parsing failed at line ${loc.line} col ${loc.col}: ${x.error}`;
  } else {
    return x.value;
  }
};

const resultC = <T>(x: Result<T>) => {
  if (x.type == "parseerror") {
    return x.error;
  } else {
    if (x.stream.idx != x.stream.src.length) {
      return "stream not consumed";
    }
    return x.value;
  }
};

describe("parser", () => {
  const parseA = char("A");
  const parseB = char("B");
  const parseAorB = either(parseA, parseB);

  const parseAandB = seq(parseA, parseB);

  const parseAB = str("AB");

  const parseManyA = many(char("a"));

  const parseOptionalB = optional(char("b"));

  const parseAoptionalB = bind(char("a"), (a) =>
    bind(parseOptionalB, (b) => bind(char("a"), (a2) => pure([a, b, a2])))
  );

  const parserTests = [
    {
      expected: true,
      actual: success(parseAB(ts("ABALONE"))),
    },
    {
      expected: true,
      actual: success(parseAorB(ts("Applesauce and orange juice"))),
    },
    { expected: true, actual: success(parseAorB(ts("Buckets of rain"))) },
    { expected: false, actual: success(parseAorB(ts("Canada oh Canada"))) },
    { expected: false, actual: success(parseAandB(ts("Argyle sweaters"))) },
    {
      expected: false,
      actual: success(parseAandB(ts("Beer battered bananas"))),
    },
    { expected: true, actual: success(parseAandB(ts("ABBA"))) },
    {
      expected: "one two three",
      actual: result(line(ts("one two three\nfour five six"))),
    },
    {
      expected: { _: "pkg", name: "abc" },
      actual: result(parsePackage(ts(`package abc`))),
    },
    {
      expected: ["a", "a", "a"],
      actual: result(parseManyA(ts("aaabbb"))),
    },
    {
      expected: [],
      actual: result(many(char("a"))(ts(""))),
    },
    {
      expected: false,
      actual: success(many1(char("a"))(ts(""))),
    },
    {
      expected: "b",
      actual: result(parseOptionalB(ts("b"))),
    },
    {
      expected: null,
      actual: result(parseOptionalB(ts(""))),
    },
    {
      expected: ["a", null, "a"],
      actual: result(parseAoptionalB(ts("aa"))),
    },
    {
      expected: ["a", "b", "a"],
      actual: result(parseAoptionalB(ts("aba"))),
    },
    {
      expected: [
        { _: "com", text: " comment" },
        { _: "com", text: " comment 2" },
      ],
      actual: result(many(parseLineComment)(ts("// comment\n// comment 2"))),
    },
    // comment at EOF
    {
      expected: { _: "com", text: " comment" },
      actual: result(parseLineComment(ts("// comment"))),
    },
    {
      expected: "aaabbb",
      actual: result(identifier(ts("aaabbb"))),
    },
    {
      expected: "Abc",
      actual: result(identifier(ts("Abc"))),
    },
    {
      expected: false,
      actual: success(identifier(ts("0abc"))),
    },
    {
      expected: "abc0",
      actual: result(identifier(ts("abc0"))),
    },
    {
      expected: "a_b",
      actual: result(identifier(ts("a_b"))),
    },
    {
      expected: true,
      actual: success(parenthesis(char("a"))(ts("(a)"))),
    },
    {
      expected: Abs("x", Ref("t"), Ref("X")),
      actual: result(abstraction(() => term)(ts("λx:X.t"))),
    },
    {
      expected: App(Ref("f"), Ref("x")),
      actual: result(application(() => term)(ts("f(x)"))),
    },
    // want to parse `f(x)(y)` as the following tree:
    //
    //      ap
    //     /  \
    //    ap   y
    //   /  \
    //  f    x
    //
    {
      expected: App(App(Ref("f"), Ref("x")), Ref("y")),
      actual: result(application(() => term)(ts("f(x)(y)"))),
    },
    {
      expected: App(App(Ref("b"), Ref("v")), Ref("w")),
      actual: result(application(() => term)(ts("(b(v))(w)"))),
    },
    {
      expected: Abs("t", Abs("f", Ref("t"), Ref("Bool")), Ref("Bool")),
      actual: result(term(ts("λt:Bool. λf:Bool. t"))),
    },
    {
      expected: App(Ref("x"), App(Ref("y"), Ref("z"))),
      actual: result(term(ts("x (y (z))"))),
    },
    {
      expected: Abs(
        "z",
        Abs(
          "x",
          Abs("y", App(Ref("x"), App(Ref("y"), Ref("z"))), Ref("Y")),
          Ref("X")
        ),
        Ref("Z")
      ),
      actual: result(term(ts("λz:Z. λx:X. λy:Y. x (y (z))"))),
    },
    {
      expected: Def("id", Abs("x", Ref("x"), Ref("X")), Ref("X")),
      actual: result(definition(ts("func id:X = λx:X. x"))),
    },
    {
      expected: Ref("ex2"),
      actual: result(reference(ts("ex2"))),
    },
    {
      expected: Ref("Bool"),
      actual: result(type(ts("Bool"))),
    },
    {
      expected: Ref("Bool"),
      actual: result(type(ts("(Bool)"))),
    },
    {
      expected: Pi(Ref("A"), Ref("B")),
      actual: result(arrow(() => type)(ts("A->B"))),
    },
    {
      expected: Pi(Ref("A"), Pi(Ref("B"), Ref("C"))),
      actual: result(type(ts("A->B->C"))),
    },
    {
      expected: Pi(Ref("B"), Ref("C")),
      actual: result(type(ts("B->C"))),
    },
    {
      expected: Pi(Ref("A"), Pi(Ref("B"), Ref("C"))),
      actual: result(arrow(() => type)(ts("A->(B->C)"))),
    },
    {
      expected: Pi(Pi(Ref("A"), Ref("B")), Ref("C")),
      actual: resultC(arrow(() => type)(ts("(A->B)->C"))),
    },

    {
      expected: Pi(Pi(Ref("A"), Ref("B")), Pi(Ref("C"), Ref("D"))),
      actual: result(arrow(() => type)(ts("(A->B)->(C->D)"))),
    },
  ];

  for (let t of parserTests) {
    test("", () => expect(t.actual).toStrictEqual(t.expected));
  }
});

describe("util", () => {
  const file = `abcdefghijklmnopqrstuvwxyz\nabcdefghijklmnopqrstuvwxyz\nabcdefghijklmnopqrstuvwxyz\n`;

  test("1", () =>
    expect(indexToLineCol(file, 0)).toStrictEqual({ line: 0, col: 0 }));
  test("2", () =>
    expect(indexToLineCol(file, 5)).toStrictEqual({ line: 0, col: 5 }));
  test("3", () =>
    expect(indexToLineCol(file, 27)).toStrictEqual({ line: 1, col: 0 }));
  test("4", () =>
    expect(indexToLineCol(file, 30)).toStrictEqual({ line: 1, col: 3 }));
});
