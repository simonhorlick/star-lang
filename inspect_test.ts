import { describe, test } from "@jest/globals";

var util = require("util");

import { ADT, Def, parseFile } from "./ast";
import { typecheck, TypecheckError } from "./check";
import { indexToLineCol, printLine } from "./parser";
import { desugar, processADTs } from "./process";
import { inspect, typecheckErrorDiagnostic } from "./inspect";
import { pretty, printCtx } from "./pretty";
import { build } from "./build";

describe("inspect", () => {
  const src = `
// Package nat contains an implementation of Church numerals.
package nat

type Bool = false | true

type Nat = zero | succ(x Nat)

//func isZero(n Nat): Bool = (case n of
func isZero:Nat->Bool = λn (case n of
  zero -> true
  succ -> false):Bool

//func add(n, m Nat): Nat = (case n of
// func add:Nat->Nat->Nat = λn λm (case n of
//   zero -> m
//   succ -> succ(add(n.x)(m))):Nat

func add:Nat->Nat->Nat = λn λm n(λP Nat)(m)(λn.x succ(add(n.x)(m)))

func main:Nat = add(succ(succ(zero)))(succ(zero)) // 2+1=3  
`;

  test("should return type information for main", () => {
    const checked = build(src);
    const def = checked.find((def) => def.name == "add")!;
    const spans = inspect(def.term, def.typ, checked);
    for (const [k, v] of spans) {
      const msg = `${k.start}-${k.end} is a ${v.term._} with type ${pretty(
        v.type
      )}; ctx at this location is ${printCtx(v.ctx)}`;
      console.log(
        typecheckErrorDiagnostic(src, TypecheckError(msg, k.start, k.end))
      );
    }
  });
});
