import { describe, expect, test } from "@jest/globals";
import { Context, Def, Self, Term } from "./ast";
import {
  addTermToCtx,
  check,
  dbgCheckIndices,
  equate,
  infer,
  lookupType,
  shift,
  subst,
  whnf,
} from "./check";
import { Abs, Ann, App, Pi, Ref, Star, Var } from "./ast";
import { pretty } from "./pretty";

const logFull = (x: any) => {
  const util = require("util");
  console.log(
    util.inspect(x, { showHidden: false, depth: null, colors: true })
  );
};
// logFull(result.term);
// console.log(pretty(result.term));

// Typing Rules
//
// Γ ⊢ a => A    infer     in context G, infer that a has type A
// Γ ⊢ a <= A    check     in context G, check that a has type A
//
// For variables, the context tells us what type to infer:
//
// x : A ∈ Γ
// ----------- var
// Γ ⊢ x => A
//
// For lambdas we can only check against a known type:
//
// Γ,x:A ⊢ a <= B
// Γ ⊢ A <= ★
// ---------------------- lambda
// Γ ⊢ λx.a <= (x:A) -> B
//
// We must infer the type of the function a, but once we have that type, we may
// to use it to check the type of the argument:
//
// Γ ⊢ a => (x:A) -> B
// Γ ⊢ b <= A
// ------------------- app
// Γ ⊢ a(b) => B[b/x]
//
// Γ ⊢ A <= ★
// Γ,x:A ⊢ B <= ★
// ------------------- pi
// Γ ⊢ (x:A) -> B => ★
//
//
// ---------- type-in-type
// Γ ⊢ ★ => ★
//
//
// We can always check inferrable types:
//
// Γ ⊢ a => A
// ---------- (a does not have a checking rule)
// Γ ⊢ a <= A
//
//
//    Γ ⊢ a <= A
// ---------------- annot
// Γ ⊢ (a : A) => A
//
//
// Γ ⊢ t:[t/x]T
// ------------ selfGen
//  Γ ⊢ t:ιx.T
//
//
//  Γ ⊢ t:ιx.T
// ------------ selfInst
// Γ ⊢ t:[t/x]T

const ci = <T extends Term>(t: T): T => dbgCheckIndices([], 0, t);

// λs. λz. z
const zero = Abs("s", Abs("z", Var("z", 0)));

// λs. λz. s z
const one = Abs("s", Abs("z", App(Var("s", 1), Var("z", 0))));

// λs. λz. s (s z)
const two = Abs("s", Abs("z", App(Var("s", 1), App(Var("s", 1), Var("z", 0)))));

describe("typechecker", () => {
  test("should calculate type of lambda body (id)", () => {
    // check that the type of `λa:A. a` is `A->A`.
    const program = Abs("a", Var("a", 0), Var("A", 1));
    expect(
      check(
        [],
        [{ type: "bind", name: "A", typ: Star() }],
        program,
        Pi("", Var("A", 0), Var("A", 1))
      )
    ).toBeTruthy();
  });

  test("should calculate type of lambda body using variable from context", () => {
    // The type of `λa:A. b` is `A->B`.
    const ctx: Context = [
      { type: "bind", name: "A", typ: Star() },
      { type: "bind", name: "b", typ: Ref("B") },
    ];
    const program = Abs("a", Var("b", 1));
    expect(
      check(
        [Def("B", id.term, Star())],
        ctx,
        program,
        Pi("", Ref("A"), Ref("B"))
      )
    ).toBeTruthy();
  });

  test("should accept well-typed application", () => {
    // Γ=[B::★,A::★]  λa:A. λf:A->B. f(a)
    // A -> (A->B) -> B
    const program = Abs(
      "a",
      Abs("f", App(Var("f", 0), Var("a", 1)), Pi("", Ref("A"), Ref("B"))),
      Ref("A")
    );

    const result = check(
      [Def("A", id.term, Star()), Def("B", id.term, Star())],
      [],
      program,
      Pi("", Ref("A"), Pi("", Pi("", Ref("A"), Ref("B")), Ref("B")))
    );
    if (result._ == "typecheckerror") {
      throw new Error(result.msg);
    }
    expect(pretty(result.type)).toBe("A→A→B→B");
  });

  test("bound variable must exist", () => {
    const program = Abs("a", Var("b", 2), Var("A", 1));
    const result = check(
      [Def("A", id.term, Star())],
      [],
      program,
      Pi("", Var("A", 0), Var("A", 1))
    );
    expect(result).toStrictEqual({
      _: "typecheckerror",
      msg: "undefined variable b",
    });
  });

  test("type shift increments free variables", () => {
    // Both X and Y are free type variables.
    const type = Pi("", Var("X", 0), Var("Y", 1));
    expect(shift(1, 0, type)).toStrictEqual(Pi("", Var("X", 1), Var("Y", 2)));
  });

  // λT:★. λf:T→T. λx:T. f(f(x))
  // ★ -> T -> T -> T -> T
  const double = Abs(
    "T",
    Abs(
      "f",
      Abs("x", App(Var("f", 1), App(Var("f", 1), Var("x", 0))), Var("T", 1)),
      Pi("", Var("T", 0), Var("T", 1))
    ),
    Star()
  );

  test("polymorphic double function is well-typed", () => {
    const result = check(
      [Def("T", Abs("x", Var("x", 0)), Pi("", Ref("X"), Ref("X")))],
      [],
      double,
      ci(
        Pi(
          "T",
          Star(),
          Pi(
            "",
            Pi("", Var("T", 0), Var("T", 1)),
            Pi("", Var("T", 1), Var("T", 2))
          )
        )
      )
    );
    if (result._ == "typecheckerror") {
      throw new Error(result.msg);
    }
    console.log(pretty(result.type, false));
  });

  test("app requires lhs to be an arrow", () => {
    const ctx: Context = [
      { type: "bind", name: "b", typ: Star() },
      { type: "bind", name: "a", typ: Star() },
    ];
    const program = App(Var("a", 0), Var("b", 1));
    expect(infer([], ctx, program)).toStrictEqual({
      _: "typecheckerror",
      msg: "expected pi type on the left of app; got star: ★",
    });
  });

  test("should ensure annotated type matches calculated type", () => {
    // Γ=[A::★]  (λa:A. a):A->A
    const program = Ann(
      Abs("a", Var("a", 0)),
      Pi("", Var("A", 0), Var("A", 1))
    );
    const result = infer(
      [],
      [{ type: "bind", name: "A", typ: Star() }],
      program
    );
    if (result._ == "typecheckerror") {
      throw new Error(result.msg);
    }
  });

  // test("should fail if annotated type doesn't match", () => {
  //   // (λa:A. a):X->X
  //   const program = Ann(
  //     Abs("a", Var("a", 0), Var("A", 1)),
  //     Pi(Var("X", 1), Var("X", 2))
  //   );
  //   expect(
  //     infer(
  //       [
  //         { type: "bind", name: "X", typ: Star() },
  //         { type: "bind", name: "A", typ: Star() },
  //       ],
  //       program
  //     )
  //   ).toStrictEqual({
  //     _: "typecheckerror",
  //     msg: "expected X; got A→A",
  //   });
  // });

  test("pi types have kind ★", () => {
    // double(x Nat) Nat = 2*x
    // double has type Nat->Nat which has kind ★
    let result = check(
      [],
      [{ type: "bind", name: "Nat", typ: Star() }],
      Pi("", Var("Nat", 0), Var("Nat", 1)),
      Star()
    );
    if (result._ == "typecheckerror") {
      throw new Error(result.msg);
    }
  });

  // and : Type -> Type -> Type
  // and = λp. λq. Πc:★. (p -> q -> c) -> c
  let and = ci(
    Ann(
      Abs(
        "p",
        Abs(
          "q",
          Pi(
            "c",
            Star(),
            Pi(
              "",
              Pi("", Var("p", 2), Pi("", Var("q", 2), Var("c", 2))),
              Var("c", 1)
            )
          )
        )
      ),
      Pi("", Star(), Pi("", Star(), Star()))
    )
  );

  test("type-level and", () => {
    let result = check([], [], and.term, and.typ);
    if (result._ == "typecheckerror") {
      throw new Error(result.msg);
    }
  });

  // conj : Πp:★. Πq:★. p -> q -> and p q
  // conj = λp. λq. λx. λy. λc. λf. f x y
  let conj = ci(
    Ann(
      Abs(
        "p",
        Abs(
          "q",
          Abs(
            "x",
            Abs(
              "y",
              Abs(
                "c",
                Abs("f", App(App(Var("f", 0), Var("x", 3)), Var("y", 2)))
              )
            )
          )
        )
      ),
      Pi(
        "p",
        Star(),
        Pi(
          "q",
          Star(),
          Pi(
            "",
            Var("p", 1),
            Pi("", Var("q", 1), App(App(Ref("and"), Var("p", 3)), Var("q", 2)))
          )
        )
      )
    )
  );

  test("conj checks", () => {
    let result = check(
      [Def("and", and.term, and.typ)],
      [],
      conj.term,
      conj.typ
    );
    if (result._ == "typecheckerror") {
      throw new Error(result.msg);
    }
  });

  // proj1 : Πp:★. Πq:★. and p q → p
  // proj1 : λp. λq. λa. a p (λx. λy. x)
  let proj1Body = ci(
    Abs(
      "p",
      Abs(
        "q",
        Abs(
          "a",
          App(App(Var("a", 0), Var("p", 2)), Abs("x", Abs("y", Var("x", 1))))
        )
      )
    )
  );
  let proj1Type = ci(
    Pi(
      "p",
      Star(),
      Pi(
        "q",
        Star(),
        Pi("", App(App(Ref("and"), Var("p", 1)), Var("q", 0)), Var("p", 2))
      )
    )
  );
  let proj1 = Ann(proj1Body, proj1Type);

  test("proj1 checks", () => {
    let result = check(
      [Def("and", and.term, and.typ)],
      [],
      proj1.term,
      proj1.typ
    );
    if (result._ == "typecheckerror") {
      throw new Error(result.msg);
    }
  });

  // proj2 : Πp:★. Πq:★. and p q → q
  // proj2 = λp.   λq. λa. a q (λx. λy. y)
  let proj2Body = ci(
    Abs(
      "p",
      Abs(
        "q",
        Abs(
          "a",
          App(App(Var("a", 0), Var("q", 1)), Abs("x", Abs("y", Var("y", 0))))
        )
      )
    )
  );
  let proj2Type = ci(
    Pi(
      "p",
      Star(),
      Pi(
        "q",
        Star(),
        Pi("", App(App(Ref("and"), Var("p", 1)), Var("q", 0)), Var("q", 1))
      )
    )
  );
  let proj2 = Ann(proj2Body, proj2Type);

  test("proj2 checks", () => {
    let result = check(
      [Def("and", and.term, and.typ)],
      [],
      proj2.term,
      proj2.typ
    );
    if (result._ == "typecheckerror") {
      throw new Error(result.msg);
    }
  });

  // and_commutes : Πp:★. Πq:★. and p q → and q p
  let commType = ci(
    Pi(
      "p",
      Star(),
      Pi(
        "q",
        Star(),
        Pi(
          "",
          App(App(Ref("and"), Var("p", 1)), Var("q", 0)),
          App(App(Ref("and"), Var("q", 1)), Var("p", 2))
        )
      )
    )
  );

  // and_commutes = λp. λq. λa. conj q p (proj2 p q a) (proj1 p q a)
  let commBody = ci(
    Abs(
      "p",
      Abs(
        "q",
        Abs(
          "a",
          App(
            App(
              App(App(Ref("conj"), Var("q", 1)), Var("p", 2)),
              App(App(App(Ref("proj2"), Var("p", 2)), Var("q", 1)), Var("a", 0))
            ),
            App(App(App(Ref("proj1"), Var("p", 2)), Var("q", 1)), Var("a", 0))
          )
        )
      )
    )
  );

  test("type-level and commutes", () => {
    // and(p,q) => and(q,p)
    // Logically, if we have an and(p,q) we can project out the components p,q
    // and construct an element of and(q,p) as desired.

    let result = check(
      [
        Def("and", and.term, and.typ),
        Def("conj", conj.term, conj.typ),
        Def("proj1", proj1.term, proj1.typ),
        Def("proj2", proj2.term, proj2.typ),
      ],
      [],
      commBody,
      commType
    );
    if (result._ == "typecheckerror") {
      throw new Error(result.msg);
    }
  });

  test("can represent bool by its eliminators", () => {
    // typeof Bool = ∀X. X→X→X
    //
    // untyped:
    // tru = λt. λf. t
    // fls = λt. λf. f
    // if = λl. λm. λn. (l(m))(n)
    //
    // typed:
    // tru: Bool = λX. λt:X. λf:X. t
    // fls: Bool = λX. λt:X. λf:X. f
    // if = λX. λb:Bool. λt:X. λf:X. (b(t))(f)

    const Bool = Pi(
      "X",
      Star(),
      Pi("", Var("X", 0), Pi("", Var("X", 1), Var("X", 2)))
    );

    const tru = Abs(
      "X",
      Abs("t", Abs("f", Var("t", 1), Var("X", 1)), Var("X", 0))
    );
    const fls = Abs(
      "X",
      Abs("t", Abs("f", Var("f", 0), Var("X", 1)), Var("X", 0))
    );

    let result = check([], [], tru, Bool);
    if (result._ == "typecheckerror") {
      throw new Error(result.msg);
    }
    let result2 = check([], [], fls, Bool);
    if (result2._ == "typecheckerror") {
      throw new Error(result2.msg);
    }
  });

  test("can typecheck bool with self types", () => {
    // Bool = true | false

    const bt = Abs("P", Abs("t", Abs("f", Var("t", 1))));
    const bf = Abs("P", Abs("t", Abs("f", Var("f", 0))));

    // ιb. ΠP:Bool→★. P(Bool.true) → P(Bool.false) → P(b)
    const Bool = Self(
      "b",
      Pi(
        "P",
        Pi("", Ref("Bool"), Star()),
        Pi(
          "",
          App(Var("P", 0), bt),
          Pi("", App(Var("P", 1), bf), App(Var("P", 2), Var("b", 3)))
        )
      )
    );

    const Booltrue = Def("Bool.true", bt, Bool);
    const Boolfalse = Def("Bool.false", bf, Bool);

    let result = check([Booltrue, Boolfalse], [], Booltrue.term, Bool);
    if (result._ == "typecheckerror") {
      throw new Error(result.msg);
    }
  });

  test("simple parameterised types", () => {
    // TODO: Maybe
  });

  // zero = λP. λz. λs. z
  const z = Abs("P", Abs("z", Abs("s", Var("z", 1))));
  // succ: Nat -> Nat = λn. λP. λz. λs. s(n)
  const s = Abs(
    "n",
    Abs("P", Abs("z", Abs("s", App(Var("s", 0), Var("n", 3)))))
  );

  // ιt. ΠP:Nat→★. P(Nat.zero) → (Πn:Nat. P(Nat.succ(n))) → P(t)
  const Nat = Self(
    "t",
    Pi(
      "P",
      Pi("", Ref("Nat"), Star()),
      Pi(
        "",
        App(Var("P", 0), z),
        Pi(
          "",
          Pi("n", Ref("Nat"), App(Var("P", 2), App(s, Var("n", 0)))),
          App(Var("P", 2), Var("t", 3))
        )
      )
    )
  );

  const zero = Def("Nat.zero", z, Nat);
  const succ = Def("Nat.succ", s, Pi("", Nat, Nat));

  test("recursive parameterised types: zero", () => {
    let result = check([], [], zero.term, Nat);
    if (result._ == "typecheckerror") {
      throw new Error(result.msg);
    }
  });

  test("recursive parameterised types: succ", () => {
    let result = check(
      [Def("Nat", Nat, Star())],
      [],
      s, //succ.term,
      Pi("", Nat, Nat)
    );
    if (result._ == "typecheckerror") {
      throw new Error(result.msg);
    }
  });

  // λx. x
  const id = Def("id", Abs("x", Var("x", 0)), Pi("", Ref("X"), Ref("X")));

  // The identity type operator λX.X: when applied to any type it gives back
  // the argument.
  const Id: Term = Abs("A", Var("A", 0), Star());

  // const Nat: Term = Ref("Nat");
  const Bool: Term = Ref("Bool");

  const defs = [Def("Nat", id.term, Star()), Def("Bool", id.term, Star())];

  // The type Nat→Bool.
  const NatToBool: Term = Pi("", Nat, Bool);

  const eq = (a: Term, b: Term) => equate(defs, Star(), a, b);

  test("Nat→Bool === Nat→Bool", () =>
    expect(eq(NatToBool, NatToBool)).toBe(true));

  test("Nat→Bool === Nat→Id(Bool)", () => {
    let s = Pi("", Nat, App(Id, Bool));
    expect(eq(NatToBool, s)).toBe(true);
  });

  test("Nat→Bool === Id(Nat)→Id(Bool)", () =>
    expect(eq(NatToBool, Pi("", App(Id, Nat), App(Id, Bool)))).toBe(true));

  test("Nat→Bool === Id(Nat)→Bool", () =>
    expect(eq(NatToBool, Pi("", App(Id, Nat), Bool))).toBe(true));

  test("Nat→Bool === Id(Nat→Bool)", () =>
    expect(eq(NatToBool, App(Id, Pi("", Nat, Bool)))).toBe(true));

  test("Nat→Bool === Id(Id(Id(Nat)→Bool))", () => {
    const t = App(Id, App(Id, Pi("", App(Id, Nat), Bool)));
    expect(eq(NatToBool, t)).toBe(true);
  });

  test("★ === Id(★)", () => {
    expect(eq(Star(), App(Id, Star()))).toBe(true);
  });

  test("id === id(id)", () => {
    expect(
      eq(
        Abs("x", Var("x", 0)),
        App(Abs("y", Var("y", 0)), Abs("z", Var("z", 0)))
      )
    ).toBe(true);
  });

  test("true != false", () => {
    expect(
      eq(Abs("t", Abs("f", Var("t", 1))), Abs("t", Abs("f", Var("f", 0))))
    ).toBe(false);
  });

  test("one != two", () => {
    expect(eq(one, two)).toBe(false);
  });
});

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
  // in the term `t1 t2` substitute all `x` with `s`
  // [x/s](t1 t2) = [x/s]t1 [x/s]t2

  // in the term `x` substitute all `x` with `s`
  test("[x/s]x = s", () => {
    let term = Var("x", 1);
    let actual = subst(1, Var("s", 2), 0, term, "x");
    let expected = Var("s", 2);
    expect(actual).toStrictEqual(expected);
  });

  // in the term `y` substitute all `x` with `s`
  test("[x/s]y = y", () => {
    let term = Var("y", 0);
    let actual = subst(1, Var("s", 2), 0, term, "y");
    let expected = Var("y", 0);
    expect(actual).toStrictEqual(expected);
  });

  // in the term `λb. b a` substitute all `b` with `a`
  test("[b/a](λb. b a)", () => {
    // [b/a](λb. b a)
    // [0/1](λ. 0 2)
    // λ. 0 2 i.e.
    // λb. b a, this is the same, nothing has been substituted.
    let term = Abs("b", App(Var("b", 0), Var("a", 2)));
    let actual = subst(0, Var("s", 1), 0, term, "");
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
    let actual = subst(0, Var("", 1), 0, term, "");
    let expected = App(Var("", 1), Abs("", Abs("", Var("", 3))));
    expect(actual).toStrictEqual(expected);
  });
});

describe("evaluation", () => {
  // (λx. x)(λz. z) -> (λz. z)
  test("TestReduceIdentity", () => {
    const identity = App(Abs("x", Var("x", 0)), Abs("z", Var("z", 0)));
    const expected: Term = Abs("z", Var("z", 0));

    const actual = whnf(true, [], identity);

    expect(actual).toStrictEqual(expected);
  });

  // λx. x
  const id = Def("id", Abs("x", Var("x", 0)), Pi("", Ref("X"), Ref("X")));

  // Test that substituting top level functions works properly.
  test("TestSubstituteDef", () => {
    const expected = Abs("z", Var("z", 0));
    const actual = whnf(true, [id], App(Ref("id"), Abs("z", Var("z", 0))));
    expect(actual).toStrictEqual(expected);
  });

  // // "if" reduction
  // //
  // // top level defs (after typecheck has passed):
  // //
  // // tru = λt. λf. t
  // // fls = λt. λf. f
  // // test = λl. λm. λn. (l(m))(n)
  // //
  // // ((test(tru))(v))(w)
  // // ------------------- def "test"
  // // (((λl. λm. λn. (l(m))(n))(tru))(v))(w)
  // // -------------------------------------- E-AppAbs
  // // ((λm. λn. (tru(m))(n))(v))(w)
  // // ----------------------------- E-AppAbs
  // // (λn. (tru(v))(n))(w)
  // // -------------------- E-AppAbs
  // // (tru(v))(w)
  // // ----------- def "tru"
  // // ((λt. λf. t)(v))(w)
  // // ------------------- E-AppAbs
  // // (λf. v)(w)
  // // ---------- E-AppAbs
  // // v
  // test("TestReduceIfElse", () => {
  //   // ((test(tru))(1))(2)
  //   const ifElse: Term = App(App(App(Ref("test"), Ref("tru")), one), two);
  //   const expected = one;
  //   const actual = evaluate([tru, fls, testfn], ifElse);

  //   expect(actual).toStrictEqual(expected);
  // });

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

    const actual = whnf(true, [], src);

    expect(actual).toStrictEqual(expected);
  });
});
