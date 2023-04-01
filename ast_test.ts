import { describe, expect, test } from "@jest/globals";
import {
  Abs,
  abstraction,
  App,
  application,
  arrow,
  Def,
  definition,
  identifier,
  parenthesis,
  parseLineComment,
  parsePackage,
  Pi,
  Ref,
  reference,
  term,
  type,
} from "./ast";
import { strip, stripAST } from "./check";
import { char, many, parseErrorDiagnostic, Result } from "./parser";
import { result, ts } from "./parser_test";

const success = <T>(x: Result<T>) => x.type == "outputvalue";

const resultC = <T>(x: Result<T>) => {
  if (x.type == "parseerror") {
    throw x.error;
  } else {
    if (x.stream.idx != x.stream.src.length) {
      throw "stream not consumed";
    }
    return x.value;
  }
};

describe("ast", () => {
  test("should parse lambda body greedily", () => {
    const src = `λn n(λp Nat)`;
    const t = term({ src, idx: 0 });
    if (t.type == "parseerror") {
      throw parseErrorDiagnostic(t);
    }
    // Expect the parser to consume the input.
    expect(t.stream.idx).toBe(src.length);
  });

  test("should parse package", () =>
    expect(stripAST(result(parsePackage(ts(`package abc`))))).toStrictEqual({
      _: "pkg",
      name: "abc",
    }));

  test("should parse multi-line comments", () =>
    expect(
      result(many(parseLineComment)(ts("// comment\n// comment 2")))
    ).toStrictEqual([
      { _: "orig2", start: 6, end: 17, child: { _: "com", text: " comment" } },
      {
        _: "orig2",
        start: 17,
        end: 29,
        child: { _: "com", text: " comment 2" },
      },
    ]));

  test("should parse comment at EOF", () =>
    expect(result(parseLineComment(ts("// comment")))).toStrictEqual({
      _: "orig2",
      start: 6,
      end: 16,
      child: {
        _: "com",
        text: " comment",
      },
    }));

  test("should parse identifier", () =>
    expect(result(identifier(ts("aaabbb")))).toStrictEqual("aaabbb"));

  test("should parse identifier", () =>
    expect(result(identifier(ts("Abc")))).toStrictEqual("Abc"));

  test("should parse identifier", () =>
    expect(success(identifier(ts("0abc")))).toStrictEqual(false));

  test("should parse identifier", () =>
    expect(result(identifier(ts("abc0")))).toStrictEqual("abc0"));

  test("should parse identifier", () =>
    expect(result(identifier(ts("a_b")))).toStrictEqual("a_b"));

  test("should parse parenthesis", () =>
    expect(success(parenthesis(char("a"))(ts("(a)")))).toStrictEqual(true));

  test("should parse lambda abstraction", () =>
    expect(strip(result(abstraction(() => term)(ts("λx t"))))).toStrictEqual(
      Abs("x", Ref("t"))
    ));

  test("should parse function application", () =>
    expect(strip(result(application(() => term)(ts("f(x)"))))).toStrictEqual(
      App(Ref("f"), Ref("x"))
    ));

  // want to parse `f(x)(y)` as the following tree:
  //
  //      ap
  //     /  \
  //    ap   y
  //   /  \
  //  f    x
  //
  test("should parse function application with multiple arguments", () =>
    expect(strip(result(application(() => term)(ts("f(x)(y)"))))).toStrictEqual(
      App(App(Ref("f"), Ref("x")), Ref("y"))
    ));

  test("should parse function application with additional parens", () =>
    expect(
      strip(result(application(() => term)(ts("(b(v))(w)"))))
    ).toStrictEqual(App(App(Ref("b"), Ref("v")), Ref("w"))));

  test("should parse true", () =>
    expect(strip(result(term(ts("λt λf t"))))).toStrictEqual(
      Abs("t", Abs("f", Ref("t")))
    ));

  test("should parse bracketed application", () =>
    expect(strip(result(term(ts("x (y (z))"))))).toStrictEqual(
      App(Ref("x"), App(Ref("y"), Ref("z")))
    ));

  test("should parse term", () =>
    expect(strip(result(term(ts("λz λx λy x (y (z))"))))).toStrictEqual(
      Abs("z", Abs("x", Abs("y", App(Ref("x"), App(Ref("y"), Ref("z"))))))
    ));

  test("should parse definition", () =>
    expect(stripAST(result(definition(ts("func id:X = λx x"))))).toStrictEqual(
      Def("id", Abs("x", Ref("x")), Ref("X"))
    ));

  test("should parse reference", () =>
    expect(strip(result(reference(ts("ex2"))))).toStrictEqual(Ref("ex2")));

  test("should parse reference", () =>
    expect(strip(result(type(ts("Bool"))))).toStrictEqual(Ref("Bool")));

  test("should parse reference", () =>
    expect(strip(result(type(ts("(Bool)"))))).toStrictEqual(Ref("Bool")));

  test("should parse arrow", () =>
    expect(strip(result(arrow(() => type)(ts("A->B"))))).toStrictEqual(
      Pi("", Ref("A"), Ref("B"))
    ));

  test("should parse arrow with correct precedence", () =>
    expect(strip(result(type(ts("A->B->C"))))).toStrictEqual(
      Pi("", Ref("A"), Pi("", Ref("B"), Ref("C")))
    ));

  test("should parse arrow type", () =>
    expect(strip(result(type(ts("B->C"))))).toStrictEqual(
      Pi("", Ref("B"), Ref("C"))
    ));

  test("should parse arrow with bracketing", () =>
    expect(strip(result(arrow(() => type)(ts("A->(B->C)"))))).toStrictEqual(
      Pi("", Ref("A"), Pi("", Ref("B"), Ref("C")))
    ));

  test("should parse arrow with bracketing", () =>
    expect(strip(resultC(arrow(() => type)(ts("(A->B)->C"))))).toStrictEqual(
      Pi("", Pi("", Ref("A"), Ref("B")), Ref("C"))
    ));

  test("should parse arrow with bracketing", () =>
    expect(
      strip(result(arrow(() => type)(ts("(A->B)->(C->D)"))))
    ).toStrictEqual(
      Pi("", Pi("", Ref("A"), Ref("B")), Pi("", Ref("C"), Ref("D")))
    ));
});
