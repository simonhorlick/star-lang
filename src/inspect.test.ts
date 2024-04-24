import { describe, expect, test } from "vitest";

import { equate, TypecheckError } from "./typecheck";
import {
  complete,
  hover,
  HoverInfo,
  hoverMessage,
  inferType,
  map,
  printDiagnostic,
  printMultilineDiagnostic,
  Range,
} from "./inspect";
import { build, BuildResult } from "./build";
import { Abs, Ann, App, Hole, Pi, Ref, serialise, Star, Var } from "./ast";
import { pretty } from "./pretty";
import { reduce } from "./equal";

const ensureBuild = (src: string): BuildResult => {
  const result = build(src, false);
  if (result.checkerErrors.length) {
    throw "build failed";
  }
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
  test("should be able to map identity over an AST", () => {
    // meaningless expression with a lot of different AST node types.
    const t = Ann(
      Abs("b", App(Var("b", 0), Ref("true"))),
      Pi("P", Star(), Hole(0))
    );
    const actual = map((x) => x, t);
    expect(pretty(actual)).toBe(pretty(t));
  });

  test("should not display anything when hovering comments", () => {
    const result = ensureBuild(`// comment`);
    const expected = new Map<Range, HoverInfo>([
      [{ start: 0, end: 10 }, { msg: " comment" }],
    ]);
    expect(hover("", result.file, result.defs, 5)).toEqual(expected);
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
      | false -> true
      | true -> false
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
    const actual = hover(src, result.file, result.defs, undefined);
    expect(actual).toEqual(expected);
  });

  test("should desugar the definitions", () => {
    const src = `
    type Bool = false | true
    func not:Bool->Bool = λb
      case b of
      | false -> true
      | true -> false
    `;
    const result = ensureBuild(src);
    expect(pretty(result.defs.get("not")!.term)).toBe(
      `λb b(λP Bool)(true)(false)`
    );
  });

  test("should give diagnostic that case isn't fully specified", () => {
    const src = `
    type Bool = true | false
    func not:Bool->Bool = λb case b of
      | false -> true
    `;
    const result = build(src, false);
    expect(result.checkerErrors[0].msg).toBe(
      "case statement doesn't handle all cases"
    );
  });

  test("should provide suggestions that fit the expected type", () => {
    const srcWithToken = `
    type Bool = true | false
    func not:Bool->Bool = λb case b of
      | true -> $HERE$
      | false -> true
    `;
    const src = srcWithToken.replace("$HERE$", "");
    const tokenLocation = srcWithToken.indexOf("$HERE$");
    const result = build(src, false);

    // The space under the cursor should have type == Bool.
    const typ = inferType(src, result.file, result.defs, tokenLocation);
    const equ = equate([], result.defs, typ!, Ref("Bool"), Ref("unused"));
    expect(equ.eq).toBeTruthy();
  });

  test("should provide suggestions for if condition", () => {
    const srcWithToken = `
    type Bool = true | false
    func not:Bool->Bool = λb if $HERE$ then todo else todo
    `;

    const src = srcWithToken.replace("$HERE$", "");
    const tokenLocation = srcWithToken.indexOf("$HERE$");
    const result = build(src, false);

    // The space under the cursor should have type == Bool.
    const typ = inferType(src, result.file, result.defs, tokenLocation);
    expect(pretty(typ)).toBe("Bool");
  });

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

  test("should return a list of available completions", () => {
    const srcWithToken = `
    type Nat = zero | succ(x Nat)
    func prev:Nat->Nat = λn
      case n of
      | zero -> zero
      | succ -> $HERE$
    func f:Nat = zero`;
    const src = srcWithToken.replace("$HERE$", "");
    const tokenLocation = srcWithToken.indexOf("$HERE$");
    const result = build(src, false);

    for (let err of result.checkerErrors) {
      console.error(printDiagnostic(src, err));
    }

    console.log(
      "finding completions at location: " +
        printDiagnostic(
          src,
          TypecheckError("", tokenLocation, tokenLocation + 1)
        )
    );

    // in the succ branch of the case
    const typ = inferType(src, result.file, result.defs, tokenLocation);
    const completion = complete(
      src,
      result.file,
      result.defs,
      tokenLocation,
      typ
    );
    const completionLabels = completion.map((c) => c.label);
    expect(completionLabels).toContain("n");
    expect(completionLabels).toContain("n.x");
  });

  test("should display type of function on hover", () => {
    const srcWithToken = `
    type Nat = zero | succ(x Nat)
    func f:Nat = su$HERE$cc(zero)`;
    const src = srcWithToken.replace("$HERE$", "");
    const tokenLocation = srcWithToken.indexOf("$HERE$");
    const result = build(src, false);
    expect(hoverMessage(src, result.file, result.defs, tokenLocation)).toEqual({
      range: { start: 52, end: 56 },
      msg: "ref((Πx:Nat Nat))",
    });
  });

  test("should display type of case branch argument on hover", () => {
    const srcWithToken = `
    type Nat = zero | succ(x Nat)
    func add:Nat->Nat->Nat = λn λm case n of
      | zero -> m
      | succ -> succ(add(n$HERE$.x)(m))`;
    const src = srcWithToken.replace("$HERE$", "");
    const tokenLocation = srcWithToken.indexOf("$HERE$");
    const result = build(src, false);
    expect(
      hoverMessage(src, result.file, result.defs, tokenLocation)?.msg
    ).toEqual("var(Nat)");
  });
});
