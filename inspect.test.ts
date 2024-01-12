import { describe, expect, test } from "vitest";

import { TypecheckError } from "./typecheck";
import {
  complete,
  hover,
  HoverInfo,
  hoverMessage,
  printDiagnostic,
  printMultilineDiagnostic,
  Range,
} from "./inspect";
import { build, BuildResult } from "./build";

const ensureBuild = (src: string): BuildResult => {
  const result = build(src, false);
  if (result.checkerErrors.length) throw "build failed";
  return result;
};

const debugPrintTokens = (src: string, br: BuildResult) => {
  const hoverInfo = hover(src, br.file, br.defs, undefined);
  for (const [k, v] of hoverInfo) {
    console.debug(
      printMultilineDiagnostic(src, TypecheckError(v.msg, k.start, k.end))
    );
  }
};

describe("inspect", () => {
  test("should not display anything when hovering comments", () => {
    const result = ensureBuild(`// comment`);
    const expected = new Map<Range, HoverInfo>([
      [{ start: 0, end: 10 }, { msg: "" }],
    ]);
    expect(hover("", result.file, result.defs, 5)).toEqual(expected);
  });

  //FIXME
  // test("should display the type when hovering a function definition", () => {
  //   // hovering over `not` should return `Bool->Bool`
  //   // hovering over `b` (the parameter and the case variable) should return `Bool`
  //   // hovering over `false` should give a Ref back to the type definition
  //   // hovering over `true` same as above
  //   // hovering over `Bool` in the type annotation should Ref back to the type definition
  //   const src = `
  //   type Bool = false | true
  //   func not:Bool->Bool = λb
  //     case b of
  //     | false -> true
  //     | true -> false
  //   `;
  //   const result = ensureBuild(src);
  //   const expected = new Map<Range, HoverInfo>([
  //     // the argument b
  //     [{ start: 57, end: 58 }, { msg: "id(Bool)" }],
  //     // the b in case b
  //     [{ start: 70, end: 71 }, { msg: "var(Bool)" }],
  //     // the true in `false -> true`
  //     [{ start: 91, end: 96 }, { msg: "ref(Bool)" }],
  //     // the false in `true -> false`
  //     [{ start: 112, end: 118 }, { msg: "ref(Bool)" }],
  //     // the Bool in the type signature
  //     [{ start: 43, end: 47 }, { msg: "ref(★)" }],
  //     // the other Bool in the type signature
  //     [{ start: 49, end: 53 }, { msg: "ref(★)" }],
  //   ]);
  //   const actual = hover(src, result.file, result.defs, undefined);
  //   expect(actual).toEqual(expected);

  //   expect(hoverMessage(src, result.file, result.defs, 70)).toEqual({
  //     range: { start: 70, end: 71 },
  //     msg: "var(Bool)",
  //   });
  // });

  // // TODO: Implement this.
  // test("should display the type when hovering a function definition Nat", () => {
  //   const srcWithToken = `
  // type Nat = zero | succ(x Nat)
  // func f$HERE$:Nat = zero`;
  //   const src = srcWithToken.replace("$HERE$", "");
  //   const tokenLocation = srcWithToken.indexOf("$HERE$");

  //   const result = ensureBuild(src);

  //   debugPrintTokens(src, result);
  //   // the type of f
  //   expect(hoverMessage(src, result.file, result.defs, tokenLocation)).toEqual({
  //     range: { start: 70, end: 71 },
  //     msg: "Nat",
  //   });
  // });

  // FIXME:
  // test("should return a list of available completions for partial def", () => {
  //   const src = `
  //   type Nat = zero | succ(x Nat)
  //   func prev:Nat->Nat = λn
  //     case n of
  //     | zero -> zero
  //     | succ -> x`;
  //   const result = build(src, false);
  //   expect(result.defs.size).toBe(3);
  // });

  // FIXME:
  // test("should return a list of available completions", () => {
  //   const srcWithToken = `
  //   type Nat = zero | succ(x Nat)
  //   func prev:Nat->Nat = λn
  //     case n of
  //     | zero -> zero
  //     | succ -> $HERE$
  //   func f:Nat = zero`;
  //   const src = srcWithToken.replace("$HERE$", "");
  //   const tokenLocation = srcWithToken.indexOf("$HERE$");
  //   const result = build(src, false);

  //   for (let err of result.checkerErrors) {
  //     console.error(printDiagnostic(src, err));
  //   }

  //   console.log(
  //     "finding completions at location: " +
  //       printDiagnostic(
  //         src,
  //         TypecheckError("", tokenLocation, tokenLocation + 1)
  //       )
  //   );

  //   // in the succ branch of the case
  //   expect(
  //     complete(src, result.file, result.defs, tokenLocation)
  //   ).toStrictEqual([
  //     {
  //       kind: 1,
  //       label: "n",
  //       sortText: "0",
  //     },
  //     {
  //       kind: 1,
  //       label: "n.x",
  //       sortText: "0",
  //     },
  //   ]);
  // });
});
