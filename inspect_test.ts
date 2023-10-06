import { describe, expect, test } from "@jest/globals";

var util = require("util");

import { ADT, ASTNode, Context, Def, parseFile, Term, Type } from "./ast";
import { stripAST, TypecheckError } from "./check";
import { indexToLineCol, printLine } from "./parser";
import { desugar, processADTs } from "./process";
import {
  complete,
  CompletionInfo,
  hover,
  HoverInfo,
  hoverMessage,
  inspect,
  inspectASTNodes,
  Range,
} from "./inspect";
import { pretty, printCtx } from "./pretty";
import { build, BuildResult } from "./build";

export const printDiagnostic = (src: string, err: TypecheckError) => {
  const lc = indexToLineCol(src, err.start);
  const ec = indexToLineCol(src, err.end);
  const line = printLine(src, lc.line);
  return (
    `at line ${lc.line} col ${lc.col}: ${err.msg}\n` +
    `  ${line}\n` +
    `  ${" ".repeat(lc.col)}^`
  );
};

export const printMultilineDiagnostic = (
  src: string,
  err: TypecheckError
): string => {
  const lc = indexToLineCol(src, err.start);
  const ec = indexToLineCol(src, err.end);

  let msg = `at line ${lc.line} col ${lc.col}: ${err.msg}\n`;
  for (let i = lc.line; i <= ec.line; i++) {
    const line = printLine(src, i);
    msg += `${line}\n`;
    if (i == lc.line) {
      msg += `${" ".repeat(lc.col)}^`;
      if (ec.line > lc.line) {
        msg += `${"-".repeat(line.length - lc.col - 1)}\n`;
      } else {
        msg += `${"-".repeat(ec.col - lc.col - 1)}\n`;
      }
    } else if (i == ec.line) {
      msg += `${"-".repeat(ec.col)}^\n`;
    } else {
      msg += `${"-".repeat(line.length)}\n`;
    }
  }

  return msg;
};

const ensureBuild = (src: string): BuildResult => {
  const result = build(src, false);
  if (result._ != "buildresult") throw "build failed";
  return result;
};

describe("inspect", () => {
  test("should not display anything when hovering comments", () => {
    const result = ensureBuild(`// comment`);
    const expected = new Map<Range, HoverInfo>([
      [{ start: 0, end: 10 }, { msg: "" }],
    ]);
    expect(hover("", result.file, result.defs)).toEqual(expected);
  });

  test("should display the type when hovering a function definition", () => {
    // hovering over `not` should return `Bool->Bool`
    // hovering over `b` (the parameter and the case variable) should return `Bool`
    // hovering over `false` should give a Ref back to the type definition
    // hovering over `true` same as above
    // hovering over `Bool` in the type annotation should Ref back to the type definition
    const src = `
    type Bool = false | true
    func not:Bool->Bool = λb
      case b of
        false -> true
        true -> false
    `;
    const result = ensureBuild(src);
    const expected = new Map<Range, HoverInfo>([
      // the argument b
      [{ start: 57, end: 58 }, { msg: "id(Bool)" }],
      // the b in case b
      [{ start: 70, end: 71 }, { msg: "var(Bool)" }],
      // the true in `false -> true`
      [{ start: 92, end: 96 }, { msg: "ref(Bool)" }],
      // the false in `true -> false`
      [{ start: 113, end: 118 }, { msg: "ref(Bool)" }],
      // the Bool in the type signature
      [{ start: 43, end: 47 }, { msg: "ref(★)" }],
      // the other Bool in the type signature
      [{ start: 49, end: 53 }, { msg: "ref(★)" }],
    ]);
    expect(hover(src, result.file, result.defs)).toEqual(expected);

    expect(hoverMessage(src, result.file, result.defs, 70)).toEqual({
      range: { start: 70, end: 71 },
      msg: "var(Bool)",
    });
  });

  test("should return a list of available completions for partial def", () => {
    const src = `
    type Nat = zero | succ(x Nat)
    func prev:Nat->Nat = λn
      case n of
        zero -> zero
        succ -> `;
    const result = build(src, false);
    expect(result.defs.size).toBe(4);
  });

  test("should return a list of available completions", () => {
    const src = `
    type Nat = zero | succ(x Nat)
    func prev:Nat->Nat = λn
      case n of
        zero -> zero
        succ -> n
    func f:Nat = zero`;
    const result = build(src, false);

    for (let err of result.checkerErrors) {
      console.error(printDiagnostic(src, err));
    }

    console.log(
      "finding completions at location: " +
        printDiagnostic(src, TypecheckError("", 116, 117))
    );

    // in the succ branch of the case
    expect(complete(src, result.file, result.defs, 116)).toStrictEqual([
      {
        kind: 1,
        label: "n",
        sortText: "0",
      },
      {
        kind: 1,
        label: "n.x",
        sortText: "0",
      },
    ]);
  });
});
