#!/usr/bin/env ./node_modules/.bin/ts-node-script

var _ = require("lodash");

function GetTypecheckTestSuite() {
  // TODO: define Int, succ, zero

  // What are we testing here?
  // - given a term:
  // - does the function body evaluate to the annotated return type?
  //      func id:X = λx:X. x ✅
  //      func id:Y = λx:X. x ❌ (λx:X.x does not evaluate to type Y)
  // - do all applications apply to arguments of the same type?
  //      λn:Int. succ(n) ✅
  //      λn:Int→Int. succ(n) ❌ (succ expects Int, got Int→Int)
  // note that Int→Int is shorthand for Πx:Int. Int.
  // - λf:B→C. λg:A→B. λx:A. f(g(x))
  // - are there any undefined references in a top level definition?
  //      func id:X = λx:X. doesntexist(x) ❌ (reference doesntexist not found)
  // does a lambda abstraction have the correct type?
  // i.e. given t2:T2; then λx:T1. t2 has type  T1→T2 (or Πx:T1.T2)

  // TODO: For each of these come up with some example test cases.
  // TODO: Add Kinds
  // TODO: Add polymorphism (T-TAbs)

  // x:T ∈ Γ
  // ------- T-Var
  // Γ ⊢ x:T

  //    Γ,x:T1 ⊢ t2:T2
  // ------------------- T-Abs
  // Γ ⊢ λx:T1. t2:T1→T2

  // Γ ⊢ t1:T11→T12    Γ ⊢ t2:T11
  // ---------------------------- T-App
  //        Γ ⊢ t1(t2):T12

  //   Γ,X ⊢ t2:T2
  // --------------- T-TAbs
  // Γ ⊢ ΛX.t2:∀X.T2

  //     Γ ⊢ t1:∀X.T12
  // --------------------- T-TApp
  // Γ ⊢ t1(T2):[X/T2]T12

  // Γ ⊢ t:[t/x]T
  // ------------ selfGen
  //  Γ ⊢ t:ιx.T

  //  Γ ⊢ t:ιx.T
  // ------------ selfInst
  // Γ ⊢ t:[t/x]T

  const typecheckTests = [
    {
      expected: null,
      actual: null,
    },
  ];

  return {
    name: "typecheck",
    tests: typecheckTests,
  };
}

function RunAllTests() {
  let suites = [GetTypecheckTestSuite()];

  let passed = 0;
  let total = 0;
  for (const s of suites) {
    for (let i = 0; i < s.tests.length; i++) {
      const t = s.tests[i];
      if (!_.isEqual(t.expected, t.actual)) {
        let expected = JSON.stringify(t.expected);
        let actual = JSON.stringify(t.actual);

        // If the output is long place them on their own lines.
        if (expected.length > 60) {
          expected = `\n${expected}`;
          actual = `\n${actual}`;
        }

        console.log(
          `failed: ${s.name} test ${i} expected ${expected}; got ${actual}`
        );
      } else {
        passed++;
      }
    }
    total += s.tests.length;
  }

  console.log(`passed ${passed}/${total}`);
}

RunAllTests();
