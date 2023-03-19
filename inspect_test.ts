import { describe, test } from "@jest/globals";

var util = require("util");

import { ADT, Def, parseFile } from "./ast";
import { typecheck, TypecheckError } from "./check";
import { indexToLineCol, printLine } from "./parser";
import { desugar, processADTs } from "./process";
import { inspect, typecheckErrorDiagnostic } from "./inspect";
import { pretty, printCtx } from "./pretty";

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
func add:Nat->Nat->Nat = λn λm (case n of
  zero -> m
  succ -> succ(add(n.x)(m))):Nat

func main:Nat = add(succ(succ(zero)))(succ(zero)) // 2+1=3  
`;

  const t = parseFile({ src, idx: 0 });

  if (t.type != "outputvalue") {
    throw "";
  }

  // generate syntax nodes for ADTs, etc
  const f = processADTs(t.value);

  // desugar definitions
  const adts = t.value.content.filter((c) => c._ == "adt") as ADT[];
  const defs = (f.content.filter((c) => c._ == "def") as Def[]).map((def) =>
    desugar(def, adts)
  );

  let checks = true;
  let checked: Def[] = [];
  for (const def of defs) {
    // typecheck
    console.log(`\n# checking definition ${def.name}`);
    const result = typecheck(defs, adts, [], def.term, def.typ, 0, src.length);
    if (result._ == "typecheckerror") {
      console.error(typecheckErrorDiagnostic(src, result));
      checks = false;
    } else {
      checked.push(Def(def.name, result.term, result.type));
    }
  }

  if (!checks) {
    throw "failed check";
  }

  const main = checked.find((def) => def.name == "true")!;

  test("should return type information for main", () => {
    // func main:Bool = not(true)
    console.log(`inspect ${main.name}:`);
    const spans = inspect(main.term, main.typ, checked);
    for (const [k, v] of spans) {
      const msg = `${k.start}-${k.end} is a ${v.term._} with type ${pretty(
        v.type
      )}; ctx at this location is ${printCtx(v.ctx)}`;
      console.log(
        typecheckErrorDiagnostic(src, TypecheckError(msg, k.start, k.end))
      );
    }
    throw "fail";
  });
});
