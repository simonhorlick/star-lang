import { describe, expect, test } from "@jest/globals";
import { Context } from "./ast";
import { GetKind, GetType } from "./check";
import {
  Abs,
  All,
  Ann,
  App,
  Arrow,
  Ref,
  Star,
  TAbs,
  TApp,
  typeShift,
  Var,
} from "./evaluation";
import { prettyT } from "./pretty";

//
// Typing Rules
//

// x:T ∈ Γ
// ------- T-Var
// Γ ⊢ x:T

//   Γ ⊢ T1::★   Γ,x:T1 ⊢ t2:T2
// ---------------------------- T-Abs
//     Γ ⊢ (λx:T1. t2):T1→T2

// Γ ⊢ t1:T11→T12    Γ ⊢ t2:T11
// ---------------------------- T-App
//        Γ ⊢ t1(t2):T12

//       Γ,X::K1 ⊢ t2:T2
// -------------------------- T-TAbs
// Γ ⊢ (ΛX::K1. t2):∀X::K1.T2

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
    const program = Abs("a", Var("a", 0), Var("A", 0));
    expect(
      GetType([{ type: "tbind", name: "A", kind: Star() }], program)
    ).toStrictEqual(Arrow(Var("A", 0), Var("A", 0)));
  });

  test("should calculate type of lambda body using variable from context", () => {
    // The type of λa:A. b is A->B.
    const ctx: Context = [
      { type: "tbind", name: "A", kind: Star() },
      { type: "bind", name: "b", typ: Ref("B") },
    ];
    const program = Abs("a", Var("b", 1), Var("A", 1));
    expect(GetType(ctx, program)).toStrictEqual(Arrow(Var("A", 1), Ref("B")));
  });

  test("should accept well-typed application", () => {
    // Γ=[B::★,A::★]  λa:A. λf:A->B. f(a)
    const program = Abs(
      "a",
      Abs("f", App(Var("f", 0), Var("a", 1)), Arrow(Var("A", 1), Var("B", 2))),
      Var("A", 0)
    );

    const result = GetType(
      [
        { type: "tbind", name: "B", kind: Star() },
        { type: "tbind", name: "A", kind: Star() },
      ],
      program
    );
    if (result._ == "typecheckerror") {
      throw new Error(result.msg);
    }
    expect(prettyT(result)).toBe("0→0→1→1");
  });

  test("bound variable must exist", () => {
    const ctx: Context = [{ type: "tbind", name: "A", kind: Star() }];
    const program = Abs("a", Var("b", 2), Var("A", 0));
    expect(GetType(ctx, program)).toStrictEqual({
      _: "typecheckerror",
      msg: "undefined variable b",
    });
  });

  test("type shift increments free variables", () => {
    // Both X and Y are free type variables.
    const type = Arrow(Var("X", 0), Var("Y", 1));
    expect(typeShift(1, type)).toStrictEqual(Arrow(Var("X", 1), Var("Y", 2)));
  });

  test("type shift doesn't change bound variables", () => {
    const type = All("X", Var("X", 0), Star());
    expect(typeShift(1, type)).toStrictEqual(type);
  });

  test("doubleNat is well-typed", () => {
    // Γ=[Nat::★]  λf:Nat→Nat. λx:Nat. f(f(x))
    const program = Abs(
      "f",
      Abs("x", App(Var("f", 1), App(Var("f", 1), Var("x", 0))), Var("Nat", 1)),
      Arrow(Var("Nat", 0), Var("Nat", 0))
    );
    const result = GetType(
      [{ type: "tbind", name: "Nat", kind: Star() }],
      program
    );
    if (result._ == "typecheckerror") {
      throw new Error(result.msg);
    }
  });

  test("app requires lhs to be an arrow", () => {
    const ctx: Context = [
      { type: "bind", name: "b", typ: Ref("B") },
      { type: "bind", name: "a", typ: Ref("A") },
    ];
    const program = App(Var("a", 0), Var("b", 1));
    expect(GetType(ctx, program)).toStrictEqual({
      _: "typecheckerror",
      msg: "expected arrow type",
    });
  });

  test("should ensure annotated type matches calculated type", () => {
    // Γ=[A::★]  (λa:A. a):A->A
    const program = Ann(
      Abs("a", Var("a", 0), Var("A", 0)),
      Arrow(Var("A", 0), Var("A", 0))
    );
    const result = GetType(
      [{ type: "tbind", name: "A", kind: Star() }],
      program
    );
    if (result._ == "typecheckerror") {
      throw new Error(result.msg);
    }
  });

  test("should fail if annotated type doesn't match", () => {
    // (λa:A. a):X
    const program = Ann(Abs("a", Var("a", 0), Var("A", 0)), Ref("X"));
    expect(
      GetType([{ type: "tbind", name: "A", kind: Star() }], program)
    ).toStrictEqual({
      _: "typecheckerror",
      msg: "expected X; got 0→0",
    });
  });

  test("pi types have kind ★", () => {
    // double(x Nat) Nat = 2*x
    // double has type Nat->Nat which has kind ★
    expect(
      GetKind(
        [{ type: "tbind", name: "Nat", kind: Star() }],
        Arrow(Var("Nat", 0), Var("Nat", 0))
      )
    ).toStrictEqual(Star());
  });

  test("should pass polymorphic identity function abs", () => {
    // id = ΛX::★. λx:X. x
    const program = TAbs("X", Abs("x", Var("x", 0), Var("X", 0)), Star());
    const result = GetType([], program);
    if (result._ == "typecheckerror") {
      throw new Error();
    }
  });

  test("should pass polymorphic identity function applied to a type", () => {
    // (ΛX::★. λx:X. x)(Int)
    // λx:Int. x
    const program = TApp(
      TAbs("X", Abs("x", Var("x", 0), Var("X", 1)), Star()),
      Var("Int", 0)
    );
    const result = GetType(
      [{ type: "tbind", name: "Int", kind: Star() }],
      program
    );
    if (result._ == "typecheckerror") {
      throw new Error();
    }
  });

  test("should disallow type operators with the wrong kind", () => {
    // ΛX::★. X→X has kind ★=>★
    // MakePair = ΛA::★. ΛB::★. A→B→Pair(A,B) has kind ★=>★=>★
    // Pair(Nat) has kind ★=>★ (it's partially applied)
    // Pair(Pair) does not belong to any kind
  });
});
