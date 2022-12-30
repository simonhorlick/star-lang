import { describe, expect, test } from "@jest/globals";
import { Context } from "./ast";
import { Check, GetType } from "./check";
import { Abs, App, Arrow, Ref, Var } from "./evaluation";

// What are we testing here?
// - given a term:
// - we want to reject programs that would otherwise fail to evaluate (no matching rules)
//   - λa:A. λab:A->B. ab(a) ✅
//   - λb:A. λab:A->B. ab(b) ❌ T-App: ab has type A->B, but applied to argument of type B.
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

//
// Typing Rules
//

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

describe("typechecker", () => {
  test("T-App rejects argument of wrong type from context", () => {
    // Γ ⊢ a:A
    // Γ ⊢ ab:A->B
    const ctx: Context = [
      { name: "a", typ: Ref("A") },
      { name: "ab", typ: Arrow(Ref("A"), Ref("B")) },
    ];
    const program = Abs(
      "a",
      Abs("ab", App(Var("ab", 0), Var("a", 1)), Arrow(Ref("A"), Ref("B"))),
      Ref("A")
    );

    expect(Check(ctx, program)).toBe(true);
  });

  test("T-App rejects argument of wrong type from binders", () => {
    const ctx: Context = [];

    // λa:A. λab:A->B. ab(a)
    const program = Abs(
      "a",
      Abs("ab", App(Var("ab", 0), Var("a", 1)), Arrow(Ref("A"), Ref("B"))),
      Ref("A")
    );

    expect(Check(ctx, program)).toBe(true);
  });

  test("T-Abs", () => {
    const ctx: Context = [];

    // typeof(λa:A. a) is A->A
    const program = Abs("a", Var("a", 0), Ref("A"));

    expect(GetType(ctx, program)).toBe(Arrow(Ref("A"), Ref("A")));
  });
});
