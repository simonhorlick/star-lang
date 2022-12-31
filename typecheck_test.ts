import { describe, expect, test } from "@jest/globals";
import { Context } from "./ast";
import { Check, GetType } from "./check";
import { Abs, Ann, App, Arrow, Ref, Var } from "./evaluation";

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
  test("should calculate type of lambda body (id)", () => {
    // The type of λa:A. a is A->A.
    const program = Abs("a", Var("a", 0), Ref("A"));
    expect(GetType([], program)).toStrictEqual(Arrow(Ref("A"), Ref("A")));
  });

  test("should calculate type of lambda body using variable from context", () => {
    // The type of λa:A. b is A->B.
    const ctx: Context = [{ name: "b", typ: Ref("B") }];
    const program = Abs("a", Var("b", 1), Ref("A"));
    expect(GetType(ctx, program)).toStrictEqual(Arrow(Ref("A"), Ref("B")));
  });

  test("should accept well-typed application", () => {
    // λa:A. λf:A->B. f(a)
    const program = Abs(
      "a",
      Abs("f", App(Var("f", 0), Var("a", 1)), Arrow(Ref("A"), Ref("B"))),
      Ref("A")
    );

    expect(Check([], program)).toStrictEqual([]);
  });

  test("bound variable must exist", () => {
    const ctx: Context = [];
    const program = Abs("a", Var("b", 1), Ref("A"));
    expect(Check(ctx, program)).toStrictEqual([
      { msg: "undefined variable b" },
    ]);
  });

  test("app requires lhs to be an arrow", () => {
    const ctx: Context = [
      { name: "b", typ: Ref("B") },
      { name: "a", typ: Ref("A") },
    ];
    const program = App(Var("a", 0), Var("b", 1));
    expect(Check(ctx, program)).toStrictEqual([{ msg: "expected arrow type" }]);
  });

  test("should ensure annotated type matches calculated type", () => {
    // (λa:A. a):A->A
    const program = Ann(
      Abs("a", Var("a", 0), Ref("A")),
      Arrow(Ref("A"), Ref("A"))
    );
    expect(Check([], program)).toStrictEqual([]);
  });

  test("should fail if annotated type doesn't match", () => {
    // (λa:A. a):X
    const program = Ann(Abs("a", Var("a", 0), Ref("A")), Ref("X"));
    expect(Check([], program)).toStrictEqual([{ msg: "expected X; got A→A" }]);
  });
});
