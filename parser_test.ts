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

const success = <T>(x: Result<T>) => x.type == "outputvalue";

export const ts = (s: string): Stream => ({
  src: `parsed${s}`,
  idx: 6,
});

export const result = <T>(x: Result<T>) => {
  if (x.type == "parseerror") {
    const loc = indexToLineCol(x.stream.src, x.stream.idx);
    throw `parsing failed at line ${loc.line} col ${loc.col}: ${x.error}`;
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
