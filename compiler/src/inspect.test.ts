import { describe, expect, test } from "vitest";

import { equate, TypecheckError } from "./typecheck";
import {
  complete,
  definitionLocation,
  hover,
  hoverMessage,
  inferType,
  printDiagnostic,
  printMultilineDiagnostic,
} from "./inspect";
import { build, BuildResult } from "./build";
import { Ref } from "./pratt";
import { pretty } from "./pretty";

const ensureBuild = (src: string): BuildResult => {
  const result = build(src, false);
  if (result.checkerErrors.length) {
    throw "build failed";
  }
  return result;
};

// const debugPrintTokens = (src: string, br: BuildResult) => {
//   const hoverInfo = hover(src, br.file, br.defs, undefined);
//   for (const hi of hoverInfo) {
//     console.debug(
//       printMultilineDiagnostic(src, TypecheckError(hi.msg, hi.start, hi.end))
//     );
//   }
// };

describe("inspect", () => {
  test("should not display anything when hovering comments", () => {
    const result = ensureBuild(`// comment`);
    const expected = [{ start: 0, end: 10, msg: " comment" }];
    expect(hover("", result.defs, result.nondefs, 5)).toEqual(expected);
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
      | false => true
      | true => false
    `;
    const result = ensureBuild(src);
    const expected = [
      // the argument b
      { start: 57, end: 58, msg: "id(Bool)" },
      // the b in case b
      { start: 70, end: 71, msg: "var(Bool)" },
      // the Bool in the type signature
      { start: 49, end: 53, msg: "ref(★)" },
      // the true in `false => true`
      { start: 92, end: 96, msg: "ref(Bool)" },
      // the false in `true => false`
      { start: 113, end: 118, msg: "ref(Bool)" },
      // the other Bool in the type signature
      { start: 43, end: 47, msg: "ref(★)" },
    ];
    const actual = hover(src, result.defs, result.nondefs, undefined);
    console.log(JSON.stringify(actual, null, 2));
    expect(actual).toEqual(expected);
  });

  test("should desugar the definitions", () => {
    const src = `
    type Bool = false | true
    func not:Bool->Bool = λb
      case b of
      | false => true
      | true => false
    `;
    const result = ensureBuild(src);
    expect(pretty(result.defs.get("not")!.term)).toBe(
      `λb b(λ Bool,true,false)`
    );
  });

  // test("should give diagnostic that case isn't fully specified", () => {
  //   const src = `
  //   type Bool = true | false
  //   func not:Bool->Bool = λb case b of
  //     | false => true
  //   `;
  //   const result = build(src, false);
  //   expect(result.checkerErrors[0].msg).toBe(
  //     "case statement doesn't handle all cases"
  //   );
  // });

  test("should provide suggestions that fit the expected type", () => {
    const srcWithToken = `
    type Bool = true | false
    func not:Bool->Bool = λb case b of
      | true => $HERE$
      | false => true
    `;
    const src = srcWithToken.replace("$HERE$", "");
    const tokenLocation = srcWithToken.indexOf("$HERE$");
    const result = build(src, false);

    // The space under the cursor should have type == Bool.
    const typ = inferType(src, result.defs, tokenLocation);
    expect(typ).toBeDefined();
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
    const typ = inferType(src, result.defs, tokenLocation);
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
  //   expect(hoverMessage(src, result.defs, result.nondefs, tokenLocation)).toEqual({
  //     range: { start: 70, end: 71 },
  //     msg: "Nat",
  //   });
  // });

  test("should return a list of available completions", () => {
    const srcWithToken = `
    type Nat = zero | succ(x Nat)
    func prev:Nat->Nat = λn
      case n of
      | zero => zero
      | succ => $HERE$
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
    const typ = inferType(src, result.defs, tokenLocation);
    const completion = complete(src, result.defs, tokenLocation, typ);
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
    expect(
      hoverMessage(src, result.defs, result.nondefs, tokenLocation)
    ).toEqual({
      range: { start: 52, end: 56 },
      msg: "ref((Πx:Nat Nat))",
    });
  });

  test("should output hover information for case branch argument", () => {
    const srcWithToken = `
    type Nat = zero | succ(x Nat)
    func add:Nat->Nat->Nat = λn λm case n of
      | zero => m
      | succ => succ(add(n$HERE$.x,m))`;
    const src = srcWithToken.replace("$HERE$", "");
    const offset = srcWithToken.indexOf("$HERE$");
    const result = build(src, false);

    const hoverInfo = hover(src, result.defs, result.nondefs, undefined)
      // Add token for clarity in test output.
      .map((i) => ({
        ...i,
        token: src.slice(i.start, i.end),
      }))
      .sort((a, b) => a.start - b.start);

    expect(hoverInfo).toEqual([
      {
        start: 30,
        end: 33,
        msg: "ref(★)",
        token: "Nat",
      },
      {
        start: 48,
        end: 51,
        msg: "ref(★)",
        token: "Nat",
      },
      {
        start: 53,
        end: 56,
        msg: "ref(★)",
        token: "Nat",
      },
      {
        start: 58,
        end: 61,
        msg: "ref(★)",
        token: "Nat",
      },
      {
        start: 65,
        end: 66,
        msg: "id(Nat)",
        token: "n",
      },
      {
        start: 68,
        end: 69,
        msg: "id(Nat)",
        token: "m",
      },
      {
        start: 75,
        end: 76,
        msg: "var(Nat)",
        token: "n",
      },
      {
        start: 96,
        end: 97,
        msg: "var(Nat)",
        token: "m",
      },
      {
        start: 114,
        end: 118,
        msg: "ref((Πx:Nat Nat))",
        token: "succ",
      },
      {
        start: 119,
        end: 122,
        msg: "ref(Nat→Nat→Nat)",
        token: "add",
      },
      {
        start: 123,
        end: 126,
        msg: "var(Nat)",
        token: "n.x",
      },
      {
        start: 127,
        end: 128,
        msg: "var(Nat)",
        token: "m",
      },
    ]);
  });

  test("should display type of case branch argument on hover", () => {
    const srcWithToken = `
    type Nat = zero | succ(x Nat)
    func add:Nat->Nat->Nat = λn λm case n of
      | zero => m
      | succ => succ(add(n$HERE$.x,m))`;
    const src = srcWithToken.replace("$HERE$", "");
    const tokenLocation = srcWithToken.indexOf("$HERE$");
    const result = build(src, false);

    const hm = hoverMessage(src, result.defs, result.nondefs, tokenLocation);

    expect(hm?.msg).toEqual("var(Nat)");
  });

  test("should provide source location of func reference", () => {
    const srcWithToken = `
    type Nat = zero | succ(x Nat)
    func add:Nat->Nat->Nat = λn λm case n of
      | zero => m
      | succ => succ(a$1$dd(n.x,m))`;
    const src = srcWithToken.replace("$1$", "");
    const tokenLocation = srcWithToken.indexOf("$1$");
    const result = build(src, false);

    const actual = definitionLocation(src, result.defs, tokenLocation);

    expect(actual).toEqual([
      {
        start: 39, // beginning of `func add...
        end: 130,
      },
    ]);
  });

  test("should cons lists successfully", () => {
    const src = `// Package list contains an implementation of cons lists.
package list

// TODO: Add imports
type Nat = zero | succ(x Nat)
func add:Nat->Nat->Nat = λn λm case n of
  | zero => m
  | succ => succ(add(n.x,m))

type List(A *) = nil | cons(head A, tail List(A))

type Bool = true | false

func head:List(Nat)->Nat = λxs
  case xs of
  | nil => 0
  | cons => xs.head

func empty:List(Nat)->Bool = λxs case xs of
  | nil => true
  | cons => false

func sum:List(Nat)->Nat = λxs case xs of
  | nil => 0
  | cons => add(xs.head, sum(xs.tail))

func numbers:List(Nat) = [1,2,3]

func main:Nat = sum(numbers)`;

    const result = build(src, false);
    expect(result.checkerErrors).toEqual([]);
  });
});
