import { describe, expect, test } from "@jest/globals";
import { Context, Def, Term } from "./ast";
import { evaluate, GetKind, GetType, shift, subst } from "./check";
import { Abs, Ann, App, Pi, Ref, Star, Var } from "./ast";
import { prettyT } from "./pretty";

// How does type checking work for function calls? We can always add Ann nodes
// to the arguments of function calls.
//
// func X(a A, b B, c C) A = a
// λ. λ. λ. 2
// X = Abs(Abs(Abs(Var(2))))
//
// X(x,y,z)
// App(App(App(X, x),y),z)
// App(App(App(X, x),y),z)
// App(App(App(Abs(Abs(Abs(Var(2)))), x), y), z)
// App(App(App(Abs(Abs(Abs(Var(2)))), x), y), z)
//         _____________________________
// App(App(Abs(Abs(x)), y), z)
// App(Abs(x), z)
// x

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
    const program = Abs("a", Var("a", 0));
    expect(
      GetType([{ type: "tbind", name: "A", kind: Star() }], program)
    ).toStrictEqual(Pi(Ref("A"), Ref("A")));
  });

  test("should calculate type of lambda body using variable from context", () => {
    // The type of λa:A. b is A->B.
    const ctx: Context = [
      { type: "tbind", name: "A", kind: Star() },
      { type: "bind", name: "b", typ: Ref("B") },
    ];
    const program = Abs("a", Var("b", 1));
    expect(GetType(ctx, program)).toStrictEqual(Pi(Ref("A"), Ref("B")));
  });

  test("should accept well-typed application", () => {
    // Γ=[B::★,A::★]  λa:A. λf:A->B. f(a)
    const program = Abs("a", Abs("f", App(Var("f", 0), Var("a", 1))));

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
    expect(prettyT(result)).toBe("A→A→B→B");
  });

  test("bound variable must exist", () => {
    const ctx: Context = [{ type: "tbind", name: "A", kind: Star() }];
    const program = Abs("a", Var("b", 2));
    expect(GetType(ctx, program)).toStrictEqual({
      _: "typecheckerror",
      msg: "undefined variable b",
    });
  });

  // test("type shift increments free variables", () => {
  //   // Both X and Y are free type variables.
  //   const type = Pi(Var("X", 0), Var("Y", 1));
  //   expect(typeShift(1, type)).toStrictEqual(Pi(Var("X", 1), Var("Y", 2)));
  // });

  // test("type shift doesn't change bound variables", () => {
  //   const type = All("X", Var("X", 0), Star());
  //   expect(typeShift(1, type)).toStrictEqual(type);
  // });

  // // ΛT::★. λf:T→T. λx:T. f(f(x))
  // const double = TAbs(
  //   "T",
  //   Abs(
  //     "f",
  //     Abs("x", App(Var("f", 1), App(Var("f", 1), Var("x", 0))), Var("T", 1)),
  //     Pi(Var("T", 0), Var("T", 0))
  //   ),
  //   Star()
  // );

  // test("polymorphic double function is well-typed", () => {
  //   const result = GetType([], double);
  //   if (result._ == "typecheckerror") {
  //     throw new Error(result.msg);
  //   }
  //   console.log(prettyT(result, false));
  //   expect(result).toStrictEqual(
  //     All(
  //       "T",
  //       Pi(Pi(Var("T", 0), Var("T", 0)), Pi(Var("T", 0), Var("T", 0))),
  //       Star()
  //     )
  //   );
  // });

  // test("instantiating double with Nat gives doubleNat", () => {
  //   const doubleNat = TApp(double, Ref("Nat"));
  //   const result = GetType(
  //     [{ type: "tbind", name: "Nat", kind: Star() }],
  //     doubleNat
  //   );
  //   if (result._ == "typecheckerror") {
  //     throw new Error(result.msg);
  //   }
  //   expect(result).toStrictEqual(
  //     Pi(Pi(Ref("Nat"), Ref("Nat")), Pi(Ref("Nat"), Ref("Nat")))
  //   );
  // });

  test("doubleNat is well-typed", () => {
    // Γ=[Nat::★]  λf:Nat→Nat. λx:Nat. f(f(x))
    const program = Abs(
      "f",
      Abs("x", App(Var("f", 1), App(Var("f", 1), Var("x", 0))))
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
      msg: "expected pi type",
    });
  });

  test("should ensure annotated type matches calculated type", () => {
    // Γ=[A::★]  (λa:A. a):A->A
    const program = Ann(Abs("a", Var("a", 0)), Pi(Ref("A"), Ref("A")));
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
    const program = Ann(Abs("a", Var("a", 0)), Ref("X"));
    expect(
      GetType([{ type: "tbind", name: "A", kind: Star() }], program)
    ).toStrictEqual({
      _: "typecheckerror",
      msg: "expected X; got A→A",
    });
  });

  test("pi types have kind ★", () => {
    // double(x Nat) Nat = 2*x
    // double has type Nat->Nat which has kind ★
    expect(
      GetKind(
        [{ type: "tbind", name: "Nat", kind: Star() }],
        Pi(Var("Nat", 0), Var("Nat", 0))
      )
    ).toStrictEqual(Star());
  });

  // test("should pass polymorphic identity function abs", () => {
  //   // id = ΛX::★. λx:X. x
  //   const program = TAbs("X", Abs("x", Var("x", 0), Var("X", 0)), Star());
  //   const result = GetType([], program);
  //   if (result._ == "typecheckerror") {
  //     throw new Error();
  //   }
  // });

  // test("should evaluate polymorphic identity function app", () => {
  //   // In system F the polymorphic id function is
  //   // Λα:★. λx:α. x
  //   // with type
  //   // ∀α:★. α→α

  //   // (ΛX::★. λx:X. x)(Y)
  //   // λx:Y. x
  //   const program = TApp(
  //     TAbs("X", Abs("x", Var("x", 0), Var("X", 1)), Star()),
  //     Ref("Y")
  //   );

  //   const actual = evaluateOnce([], program);
  //   const expected = Abs("x", Var("x", 0), Ref("Y"));
  //   expect(actual).toStrictEqual(expected);
  // });

  // test("should pass polymorphic identity function applied to a type", () => {
  //   // (ΛX::★. λx:X. x)(Int)
  //   // λx:Int. x
  //   const program = TApp(
  //     TAbs("X", Abs("x", Var("x", 0), Var("X", 1)), Star()),
  //     Var("Int", 0)
  //   );
  //   const result = GetType(
  //     [{ type: "tbind", name: "Int", kind: Star() }],
  //     program
  //   );
  //   if (result._ == "typecheckerror") {
  //     throw new Error();
  //   }
  // });

  // test("can represent bool by its eliminators", () => {
  //   // typeof Bool = ∀X. X→X→X
  //   //
  //   // untyped:
  //   // tru = λt. λf. t
  //   // fls = λt. λf. f
  //   // if = λl. λm. λn. (l(m))(n)
  //   //
  //   // typed:
  //   // tru: Bool = λX. λt:X. λf:X. t
  //   // fls: Bool = λX. λt:X. λf:X. f
  //   // if = λX. λb:Bool. λt:X. λf:X. (b(t))(f)

  //   const Bool = All(
  //     "X",
  //     Pi(Var("X", 0), Pi(Var("X", 0), Var("X", 0))),
  //     Star()
  //   );

  //   const tru = TAbs(
  //     "X",
  //     Abs("t", Abs("f", Var("t", 1), Var("X", 1)), Var("X", 0)),
  //     Star()
  //   );
  //   const fls = TAbs(
  //     "X",
  //     Abs("t", Abs("f", Var("f", 0), Var("X", 1)), Var("X", 0)),
  //     Star()
  //   );

  //   expect(GetType([], tru)).toStrictEqual(Bool);
  //   expect(GetType([], fls)).toStrictEqual(Bool);
  // });

  test("should disallow type operators with the wrong kind", () => {
    // pair = ΛA::★. ΛB::★. λa:A. λb:B. ???
    // typeof Pair = ∀X. X→X→X
    // untyped:
    // fst = λa. λb. a
    // snd = λa. λb. b
    // λX::★. X→X has kind ★=>★
    // pair = ΛA::★. ΛB::★. A→B→Pair(A,B) has kind ★=>★=>★
    // Pair(Nat) has kind ★=>★ (it's partially applied)
    // Pair(Pair) does not belong to any kind
    // const pair = ;
  });

  // test("[X/Nat](λx:X.x)", () => {
  //   // [X/Nat](λx:X.x)
  //   // λx:Nat.x
  //   let term = Abs("x", Var("x", 0), Var("X", 1));
  //   let actual = tytermSubst(Var("Nat", 5), 0, term);
  //   let expected = Abs("x", Var("x", 0), Var("Nat", 6));
  //   expect(actual).toStrictEqual(expected);
  // });
});

// describe("type operators", () => {
//   // The identity type operator λX.X: when applied to any type it gives back
//   // the argument.
//   const Id: Type = TTAbs("A", Var("A", 0), Star());

//   const Nat: Type = Ref("Nat");
//   const Bool: Type = Ref("Bool");

//   // The type Nat→Bool.
//   const NatToBool: Type = Pi(Nat, Bool);

//   const ctx: Context = [];
//   const n2b = simplifyty(ctx, NatToBool);

//   // In λω, we recapitulated the mechanisms of the simply typed lambda-calculus “one level up,” taking a type and abstracting out a subexpression to obtain a type operator that can later be instantiated by applying it to different types.
//   test("Nat→Bool === Nat→Bool", () =>
//     expect(typeEq(n2b, simplifyty(ctx, NatToBool))).toBe(true));

//   test("Nat→Bool === Nat→Id(Bool)", () => {
//     let s = simplifyty(ctx, Pi(Nat, TTApp(Id, Bool)));
//     expect(typeEq(n2b, s)).toBe(true);
//   });

//   test("Nat→Bool === Id(Nat)→Id(Bool)", () =>
//     expect(
//       typeEq(n2b, simplifyty(ctx, Pi(TTApp(Id, Nat), TTApp(Id, Bool))))
//     ).toBe(true));

//   test("Nat→Bool === Id(Nat)→Bool", () =>
//     expect(typeEq(n2b, simplifyty(ctx, Pi(TTApp(Id, Nat), Bool)))).toBe(true));

//   test("Nat→Bool === Id(Nat→Bool)", () =>
//     expect(typeEq(n2b, simplifyty(ctx, TTApp(Id, Pi(Nat, Bool))))).toBe(true));

//   test("Nat→Bool === Id(Id(Id(Nat)→Bool))", () => {
//     const t = TTApp(Id, TTApp(Id, Pi(TTApp(Id, Nat), Bool)));
//     console.log(prettyT(t));
//     const s = simplifyty(ctx, t);
//     console.log(prettyT(s));
//     const s2 = simplifyty(ctx, s);
//     console.log(prettyT(s2));
//     const s3 = simplifyty(ctx, s2);
//     console.log(prettyT(s3));
//     expect(typeEq(n2b, s3)).toBe(true);
//   });
// });

// tru = λt. λf. t
const tru = Def("tru", Abs("t", Abs("f", Var("t", 1))), Ref("unknown"));

// fls = λt. λf. f
const fls = Def("fls", Abs("t", Abs("f", Var("f", 0))), Ref("unknown"));

// test = λl. λm. λn. (l(m))(n)
// test = λ2. λ1. λ0. (2(1))(0)
const testfn = Def(
  "test",
  Abs("l", Abs("m", Abs("n", App(App(Var("l", 2), Var("m", 1)), Var("n", 0))))),
  Ref("unknown")
);

// λs. λz. z
// const zero = Abs("s", Abs("z", Var("z", 0)));

// λs. λz. s z
const one = Abs("s", Abs("z", App(Var("s", 1), Var("z", 0))));

// λs. λz. s (s z)
const two = Abs("s", Abs("z", App(Var("s", 1), App(Var("s", 1), Var("z", 0)))));

// λx. x
const id = Def("id", Abs("x", Var("x", 0)), Pi(Ref("X"), Ref("X")));

//
// Evaluation Rules
//

//     t1 → t1'
// ---------------- E-App1
// t1(t2) → t1'(t2)

//     t2 → t2'
// ---------------- E-App2
// v1(t2) → v1(t2')

// (λx:T11.t12)(v2) → [x/v2]t12     E-AppAbs

//     t1 → t1'
// ---------------- E-TApp
// t1(T2) → t1'(T2)

// (ΛX.t12)(T2) → [X/T2]t12    E-TappTabs

describe("erasure", () => {
  // test("polymorphic identity function erases to untyped identity", () => {
  //   const program = TApp(
  //     TAbs("X", Abs("x", Var("x", 0), Var("X", 1)), Star()),
  //     Ref("Y")
  //   );
  //   const actual = erase(program);
  //   const expected = Abs("x", Var("x", 0));
  //   expect(actual).toStrictEqual(expected);
  // });
});

describe("shifting", () => {
  test("ensure we only shift free variables", () => {
    // we need to shift the 2, but not the 0 or the 1, as 2 is free in this
    // expression.

    // λ.λ.1(0(2)) shifted up by 2 is:
    // λ.λ.1(0(4))
    let term = Abs(
      "x",
      Abs("y", App(Var("x", 1), App(Var("y", 0), Var("z", 2))))
    );
    let actual = shift(2, 0, term);
    let expected = Abs(
      "x",
      Abs("y", App(Var("x", 1), App(Var("y", 0), Var("z", 4))))
    );
    expect(actual).toStrictEqual(expected);
  });

  test("ensure we only shift free variables", () => {
    // note left association of app in the following syntax:
    // λ.01(λ.012) shifted up by 2 is:
    // λ.03(λ.014)
    let term = Abs(
      "",
      App(
        App(Var("", 0), Var("", 1)),
        Abs("", App(App(Var("", 0), Var("", 1)), Var("", 2)))
      )
    );
    let actual = shift(2, 0, term);
    let expected = Abs(
      "",
      App(
        App(Var("", 0), Var("", 3)),
        Abs("", App(App(Var("", 0), Var("", 1)), Var("", 4)))
      )
    );
    expect(actual).toStrictEqual(expected);
  });
});

describe("substitution", () => {
  // Examples:
  // [x/s]x = s
  // [x/s]y = y                       (if y ≠ x)
  // [x/s](λy.t1) = λy.[x/s]t1        (if y ≠ x and y ∉ FV(s))
  // [x/s](t1 t2) = [x/s]t1 [x/s]t2

  test("[x/s]x = s", () => {
    let term = Var("x", 1);
    let actual = subst(1, Var("s", 2), 0, term);
    let expected = Var("s", 2);
    expect(actual).toStrictEqual(expected);
  });

  test("[x/s]y = y", () => {
    let term = Var("y", 0);
    let actual = subst(1, Var("s", 2), 0, term);
    let expected = Var("y", 0);
    expect(actual).toStrictEqual(expected);
  });

  test("[b/a](λb. b a)", () => {
    // [b/a](λb. b a)
    // [0/1](λ. 0 2)
    // λ. 0 2 i.e. λb. b a, this is the same, nothing has been substituted.
    let term = Abs("b", App(Var("b", 0), Var("a", 2)));
    let actual = subst(0, Var("", 1), 0, term);
    let expected = Abs("b", App(Var("b", 0), Var("a", 2)));
    expect(actual).toStrictEqual(expected);
  });

  test("[b/a](b (λx.λy.b))", () => {
    // replace occurances of b with a:
    // [b/a](b (λx.λy.b))
    // (a (λx.λy.a))
    // in debruijin form b=0,a=1:
    // [0/1](0 (λ.λ.2))
    // 1 (λ.λ.3)
    let term = App(Var("", 0), Abs("", Abs("", Var("", 2))));
    let actual = subst(0, Var("", 1), 0, term);
    let expected = App(Var("", 1), Abs("", Abs("", Var("", 3))));
    expect(actual).toStrictEqual(expected);
  });
});

describe("evaluation", () => {
  // (λx. x)(λz. z) -> (λz. z)
  test("TestReduceIdentity", () => {
    const identity = App(Abs("x", Var("x", 0)), Abs("z", Var("z", 0)));
    const expected: Term = Abs("z", Var("z", 0));

    const actual = evaluate([], identity);

    expect(actual).toStrictEqual(expected);
  });

  // Test that substituting top level functions works properly.
  test("TestSubstituteDef", () => {
    const expected = Abs("z", Var("z", 0));
    const actual = evaluate([id], App(Ref("id"), Abs("z", Var("z", 0))));
    expect(actual).toStrictEqual(expected);
  });

  // "if" reduction
  //
  // top level defs (after typecheck has passed):
  //
  // tru = λt. λf. t
  // fls = λt. λf. f
  // test = λl. λm. λn. (l(m))(n)
  //
  // ((test(tru))(v))(w)
  // ------------------- def "test"
  // (((λl. λm. λn. (l(m))(n))(tru))(v))(w)
  // -------------------------------------- E-AppAbs
  // ((λm. λn. (tru(m))(n))(v))(w)
  // ----------------------------- E-AppAbs
  // (λn. (tru(v))(n))(w)
  // -------------------- E-AppAbs
  // (tru(v))(w)
  // ----------- def "tru"
  // ((λt. λf. t)(v))(w)
  // ------------------- E-AppAbs
  // (λf. v)(w)
  // ---------- E-AppAbs
  // v
  test("TestReduceIfElse", () => {
    // ((test(tru))(1))(2)
    const ifElse: Term = App(App(App(Ref("test"), Ref("tru")), one), two);
    const expected = one;
    const actual = evaluate([tru, fls, testfn], ifElse);

    expect(actual).toStrictEqual(expected);
  });

  test("should ensure redex uses up bound variable", () => {
    // Γ = [z→2, y→1]
    // (λx. y(x)(z))(λx. x)
    // y(λx. x)(z)
    // This corresponds to the nameless representation:
    // (λx. 1(0)(2))(λx. 0)
    // After one step of evaluation, then indices for y and z are evaluated by 1
    // as the x binder has now been used up.
    // 0(λx. 0)(1)

    let src = App(
      Abs("x", App(App(Var("y", 1), Var("x", 0)), Var("z", 2))),
      Abs("x", Var("x", 0))
    );

    let expected = App(App(Var("y", 0), Abs("x", Var("x", 0))), Var("z", 1));

    const actual = evaluate([], src);

    expect(actual).toStrictEqual(expected);
  });
});
