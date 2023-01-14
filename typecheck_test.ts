import { describe, expect, test } from "@jest/globals";
import { Context, Type } from "./ast";
import {
  GetKind,
  GetType,
  reduceOnce,
  simplifyty,
  typeEq,
  typeShift,
  tytermSubst,
} from "./check";
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
  TTAbs,
  TTApp,
  Var,
} from "./ast";
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

  // ΛT::★. λf:T→T. λx:T. f(f(x))
  const double = TAbs(
    "T",
    Abs(
      "f",
      Abs("x", App(Var("f", 1), App(Var("f", 1), Var("x", 0))), Var("T", 1)),
      Arrow(Var("T", 0), Var("T", 0))
    ),
    Star()
  );

  test("polymorphic double function is well-typed", () => {
    const result = GetType([], double);
    if (result._ == "typecheckerror") {
      throw new Error(result.msg);
    }
    console.log(prettyT(result, false));
    expect(result).toStrictEqual(
      All(
        "T",
        Arrow(Arrow(Var("T", 0), Var("T", 0)), Arrow(Var("T", 0), Var("T", 0))),
        Star()
      )
    );
  });

  test("instantiating double with Nat gives doubleNat", () => {
    const doubleNat = TApp(double, Ref("Nat"));
    const result = GetType(
      [{ type: "tbind", name: "Nat", kind: Star() }],
      doubleNat
    );
    if (result._ == "typecheckerror") {
      throw new Error(result.msg);
    }
    expect(result).toStrictEqual(
      Arrow(Arrow(Ref("Nat"), Ref("Nat")), Arrow(Ref("Nat"), Ref("Nat")))
    );
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

  test("should evaluate polymorphic identity function app", () => {
    // In system F the polymorphic id function is
    // Λα:★. λx:α. x
    // with type
    // ∀α:★. α→α

    // (ΛX::★. λx:X. x)(Y)
    // λx:Y. x
    const program = TApp(
      TAbs("X", Abs("x", Var("x", 0), Var("X", 1)), Star()),
      Ref("Y")
    );

    const actual = reduceOnce([], program);
    const expected = Abs("x", Var("x", 0), Ref("Y"));
    expect(actual).toStrictEqual(expected);
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
    // λX::★. X→X has kind ★=>★
    // MakePair = ΛA::★. ΛB::★. A→B→Pair(A,B) has kind ★=>★=>★
    // Pair(Nat) has kind ★=>★ (it's partially applied)
    // Pair(Pair) does not belong to any kind
  });

  // pair = ΛA::★. ΛB::★. λa:A. λb:B.
  // fst = λp:Pair(A,B).

  test("[X/Nat](λx:X.x)", () => {
    // [X/Nat](λx:X.x)
    // λx:Nat.x
    let term = Abs("x", Var("x", 0), Var("X", 1));
    let actual = tytermSubst(Var("Nat", 5), 0, term);
    let expected = Abs("x", Var("x", 0), Var("Nat", 6));
    expect(actual).toStrictEqual(expected);
  });
});

describe("type operators", () => {
  // The identity type operator λX.X: when applied to any type it gives back
  // the argument.
  const Id: Type = TTAbs("A", Var("A", 0), Star());

  const Nat: Type = Ref("Nat");
  const Bool: Type = Ref("Bool");

  // The type Nat→Bool.
  const NatToBool: Type = Arrow(Nat, Bool);

  const ctx: Context = [];
  const n2b = simplifyty(ctx, NatToBool);

  // In λω, we recapitulated the mechanisms of the simply typed lambda-calculus “one level up,” taking a type and abstracting out a subexpression to obtain a type operator that can later be instantiated by applying it to different types.
  test("Nat→Bool === Nat→Bool", () =>
    expect(typeEq(n2b, simplifyty(ctx, NatToBool))).toBe(true));

  test("Nat→Bool === Nat→Id(Bool)", () => {
    let s = simplifyty(ctx, Arrow(Nat, TTApp(Id, Bool)));
    expect(typeEq(n2b, s)).toBe(true);
  });

  test("Nat→Bool === Id(Nat)→Id(Bool)", () =>
    expect(
      typeEq(n2b, simplifyty(ctx, Arrow(TTApp(Id, Nat), TTApp(Id, Bool))))
    ).toBe(true));

  test("Nat→Bool === Id(Nat)→Bool", () =>
    expect(typeEq(n2b, simplifyty(ctx, Arrow(TTApp(Id, Nat), Bool)))).toBe(
      true
    ));

  test("Nat→Bool === Id(Nat→Bool)", () =>
    expect(typeEq(n2b, simplifyty(ctx, TTApp(Id, Arrow(Nat, Bool))))).toBe(
      true
    ));

  test("Nat→Bool === Id(Id(Id(Nat)→Bool))", () => {
    const t = TTApp(Id, TTApp(Id, Arrow(TTApp(Id, Nat), Bool)));
    console.log(prettyT(t));
    const s = simplifyty(ctx, t);
    console.log(prettyT(s));
    const s2 = simplifyty(ctx, s);
    console.log(prettyT(s2));
    const s3 = simplifyty(ctx, s2);
    console.log(prettyT(s3));
    expect(typeEq(n2b, s3)).toBe(true);
  });
});
