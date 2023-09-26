import { describe, expect, test } from "@jest/globals";

var util = require("util");

import { ADT, ASTNode, Context, Def, parseFile, Term, Type } from "./ast";
import { stripAST, TypecheckError } from "./check";
import { indexToLineCol, printLine } from "./parser";
import { desugar, processADTs } from "./process";
import { inspect, inspectASTNodes } from "./inspect";
import { pretty, printCtx } from "./pretty";
import { build, BuildResult } from "./build";
import { File } from "./ast";

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

type HoverInfo = {
  msg: string;
};

type Range = { start: number; end: number };

const hover = (
  src: string,
  f: File,
  defs: Map<string, Def>
): Map<Range, HoverInfo> => {
  let hoverInfo = new Map<Range, HoverInfo>();

  for (const node of f.content) {
    if (node._ == "def") {
      const def = node;
      const spans = inspect(def, defs);
      for (const [k, v] of spans) {
        switch (v.term._) {
          case "lam":
            break;
          default:
            hoverInfo.set(
              { start: k.start, end: k.end },
              { msg: `${v.term._}(${pretty(v.type)})` }
            );
        }
        // const msg = `${k.start}-${k.end} is a ${v.term._} with type ${pretty(
        //   v.type
        // )}; ctx at this location is ${printCtx(v.ctx)}`;
        // console.debug(
        //   printDiagnostic(src, TypecheckError(msg, k.start, k.end))
        // );
        // console.log(
        //   `[{ start: ${k.start}, end: ${k.end} }, { msg: "${`${
        //     v.term._
        //   }(${pretty(v.type)})`}" }],`
        // );
      }
    } else {
      const spans = inspectASTNodes(node);
      for (const [k, v] of spans) {
        hoverInfo.set({ start: k.start, end: k.end }, { msg: "" });

        // const msg = `${k.start}-${k.end} is a ${v.term._}`;
        // console.debug(
        //   printDiagnostic(src, TypecheckError(msg, k.start, k.end))
        // );
      }
    }
  }

  return hoverInfo;
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
  });
});
