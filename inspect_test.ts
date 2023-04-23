import { describe, test } from "@jest/globals";

var util = require("util");

import { ADT, ASTNode, Context, Def, parseFile, Term, Type } from "./ast";
import { typecheck, TypecheckError } from "./check";
import { indexToLineCol, printLine } from "./parser";
import { desugar, processADTs } from "./process";
import { inspect, inspectASTNodes, typecheckErrorDiagnostic } from "./inspect";
import { pretty, printCtx } from "./pretty";
import { build } from "./build";

describe("inspect", () => {
  const src = `
  // Package nat contains an implementation of Church numerals.
  package nat
  
  type Bool = false | true
  
  // Nat is a natural number.
  type Nat = zero | succ(x Nat)
   
  func isZero:Nat->Bool = λn (case n of
    zero -> true
    succ -> false):Bool
  
  func add:Nat->Nat->Nat = λn λm n(λa Nat)(m)(λn.x succ(add(n.x)(m)))
  
  // main 
  func main:Nat = add(succ(succ(zero)))(succ(zero)) // 2+1=3  
`;

  test("should return type information for main", () => {
    const result = build(src);
    if (result._ != "buildresult") throw "build failed";
    const defs = result.defs;
    const f = result.file;

    for (const node of f.content) {
      if (node._ == "def") {
        const def = node;
        const spans = inspect(def, defs);
        for (const [k, v] of spans) {
          const msg = `${k.start}-${k.end} is a ${v.term._} with type ${pretty(
            v.type
          )}; ctx at this location is ${printCtx(v.ctx)}`;
          console.log(
            typecheckErrorDiagnostic(src, TypecheckError(msg, k.start, k.end))
          );
        }
      } else {
        const spans = inspectASTNodes(node);
        for (const [k, v] of spans) {
          const msg = `${k.start}-${k.end} is a ${v.term._}`;
          console.log(
            typecheckErrorDiagnostic(src, TypecheckError(msg, k.start, k.end))
          );
        }
      }
    }
  });
});
