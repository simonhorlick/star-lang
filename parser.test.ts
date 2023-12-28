import { describe, expect, test } from "vitest";

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
  num,
  parseErrorDiagnostic,
  skip,
  Parser,
  takeUntil,
} from "./parser";

const success = <T>(x: Result<T>) => x._ == "outputvalue";

export const ts = (s: string): Stream => ({
  src: `parsed${s}`,
  idx: 6,
});

export const result = <T>(x: Result<T>) => {
  if (x._ == "parseerror") {
    const msg = parseErrorDiagnostic(x);
    throw msg;
  } else {
    return x.value;
  }
};

describe("parser", () => {
  const parseA = char("A");
  const parseB = char("B");
  const parseAorB = either(parseA, parseB);

  const parseAthenB = seq(parseA, parseB);

  const parseAB = str("AB");

  const parseManyA = many(char("a"));

  const parseOptionalB = optional(char("b"));

  const parseAoptionalB = bind(char("a"), (a) =>
    bind(parseOptionalB, (b) => bind(char("a"), (a2) => pure([a, b, a2])))
  );

  test("should parse AB", () =>
    expect(success(parseAB(ts("ABALONE")))).toStrictEqual(true));

  test("should parse A", () =>
    expect(success(parseAorB(ts("Applesauce and orange juice")))).toStrictEqual(
      true
    ));

  test("should parse B", () =>
    expect(success(parseAorB(ts("Buckets of rain")))).toStrictEqual(true));

  test("should not parse C", () =>
    expect(success(parseAorB(ts("Canada oh Canada")))).toStrictEqual(false));

  test("should not parse AB", () =>
    expect(success(parseAthenB(ts("Argyle sweaters")))).toStrictEqual(false));

  test("should not parse AB", () =>
    expect(success(parseAthenB(ts("Beer battered bananas")))).toStrictEqual(
      false
    ));

  test("should parse AB", () =>
    expect(success(parseAthenB(ts("ABBA")))).toStrictEqual(true));

  test("should parse one line", () =>
    expect(result(line(ts("one two three\nfour five six")))).toStrictEqual(
      "one two three"
    ));

  test("should parse many as", () =>
    expect(result(parseManyA(ts("aaabbb")))).toStrictEqual(["a", "a", "a"]));

  test("should skip letter a", () =>
    expect(
      result(bind(skip(char("a")), (_) => char("b"))(ts("aaaaab")))
    ).toStrictEqual("b"));

  test("should parse many without input successfully as an empty list", () =>
    expect(result(many(char("a"))(ts("")))).toStrictEqual([]));

  test("should fail many1 on empty input", () =>
    expect(success(many1(char("a"))(ts("")))).toStrictEqual(false));

  test("should parse optional b", () =>
    expect(result(parseOptionalB(ts("b")))).toStrictEqual("b"));

  test("should parse optional b successfully if not present", () =>
    expect(result(parseOptionalB(ts("")))).toStrictEqual(null));

  test("should parse ab+a without b present", () =>
    expect(result(parseAoptionalB(ts("aa")))).toStrictEqual(["a", null, "a"]));

  test("should parse ab+a with b present", () =>
    expect(result(parseAoptionalB(ts("aba")))).toStrictEqual(["a", "b", "a"]));

  test("should parse 12345", () =>
    expect(result(num(ts("12345")))).toStrictEqual(12345));

  const untila = takeUntil(char("a"));

  test("should parse until the given parser is true", () =>
    expect(result(untila(ts("12345abcd")))).toStrictEqual("12345"));
});

describe("csv", () => {
  // a string that starts with two double quotes and ends with two double quotes.
  // e.g. ""hello""
  const quoted: Parser<string> = bind(str(`""`), (_) =>
    bind(takeUntil(str(`""`)), (name) => bind(str(`""`), (_) => pure(name)))
  );
  const plain: Parser<string> = takeUntil(either(char(`,`), char(`"`)));

  test("plain", () =>
    expect(result(plain(ts(`Event,`)))).toStrictEqual("Event"));
  test("plain2", () => expect(result(plain(ts(`,,"`)))).toStrictEqual(""));
  test("quoted", () =>
    expect(result(quoted(ts(`""aaaaa""`)))).toStrictEqual("aaaaa"));
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
