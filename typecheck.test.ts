import { describe, expect, test } from "vitest";
import { ADT, Def, Self, Term, identifier2str, parseFile } from "./ast";
import {
  typecheck,
  equate,
  infer,
  TypecheckError,
  Result,
  defs,
  adts,
} from "./typecheck";
import { Abs, Ann, App, Pi, Ref, Star, Var } from "./ast";
import { pretty } from "./pretty";
import {
  bool,
  cons,
  fls,
  just,
  list,
  maybe,
  mnull,
  nat,
  nil,
  succ,
  tru,
  zero,
  pair,
  ppair,
} from "./test_defs";
import { reduce } from "./equal";
import { build } from "./build";
import { Context } from "./context";
import { desugar, processADTs } from "./process";

// throw any type checking errors
const te = (t: Term | TypecheckError): Term => {
  if (t._ == "typecheckerror") {
    throw t.msg;
  } else {
    return t;
  }
};
const ensure = (r: Result | TypecheckError): Result => {
  if (r._ == "typecheckerror") {
    throw r.msg;
  } else {
    return r;
  }
};

describe("typechecker", () => {
  // Typing Rules
  //
  // Γ ⊢ a => A    infer     in context Γ, infer that a has type A
  // Γ ⊢ a <= A    check     in context Γ, check that a has type A

  describe("var", () => {
    // For variables, the context tells us what type to infer:
    //
    // x : A ∈ Γ
    // ----------- var
    // Γ ⊢ x => A
    test("should infer type of variable from context", () => {
      const ctx: Context = [{ type: "bind", name: "x", typ: Ref("A") }];
      expect(
        ensure(infer(defs(), adts(), ctx, Var("x", 0), 0, 0)).type
      ).toStrictEqual(Ref("A"));
    });

    test("ensure var lookup indices are correct", () => {
      const ctx: Context = [
        { type: "bind", name: "A", typ: Star() },
        { type: "bind", name: "a", typ: Var("A", 0) },
      ];

      expect(infer(defs(), adts(), ctx, Var("a", 0), 0, 0)).toStrictEqual({
        _: "result",
        holes: [],
        term: { _: "var", index: 0, name: "a" },
        type: { _: "var", index: 1, name: "A" },
      });
    });
  });

  describe("lambda", () => {
    // Lambdas must be checked against a supplied pi type.
    //
    // Γ,x:A ⊢ a <= B
    // Γ ⊢ A <= *
    // ---------------------- lambda
    // Γ ⊢ λx.a <= (x:A) -> B

    test("should infer the domain of a pi type to be type star", () => {
      // In this test case, the typechecker should look up the reference A and
      // ensure it's a type.
      try {
        const result = typecheck(
          defs(),
          adts(),
          [],
          Abs("a", Var("a", 0)),
          Pi("", Ref("A"), Ref("A"))
        );
      } catch (e) {
        expect(e).toStrictEqual({
          _: "typecheckerror",
          end: 0,
          msg: "reference not found: A; ctx is [a:A]",
          start: 0,
        });
        return;
      }
      throw "expected exception";
    });

    test("should check that a lambda has a pi type", () => {
      const result = ensure(
        typecheck(
          defs([Def("A", Ann(Abs("x", Var("x", 0)), Star()))]),
          adts(),
          [],
          Abs("a", Var("a", 0)),
          Pi("", Ref("A"), Ref("A"))
        )
      );
      expect(result.term).toStrictEqual(Abs("a", Var("a", 0)));
      expect(result.type).toStrictEqual(Pi("", Ref("A"), Ref("A")));
    });
  });

  describe("pi", () => {
    // We first check that A has type star, and that B has type star if x is in
    // the context, if so we're all good and the type of the pi is star.
    //
    // Γ ⊢ A <= *
    // Γ,x:A ⊢ B <= *
    // ------------------- pi
    // Γ ⊢ Πx:A. B => *

    test("should check domain is a type", () => {
      ensure(
        typecheck(
          defs([
            Def("A", Ann(Abs("x", Var("x", 0)), Star())),
            Def("B", Ann(Abs("x", Var("x", 0)), Star())),
          ]),
          adts(),
          [],
          Pi("", Ref("A"), Ref("B")),
          Star()
        )
      );
    });
  });

  describe("star", () => {
    // Under the empty set of assumptions, we postulate that star has type star
    // (i.e. we have type-in-type).
    //
    // ----------------
    // Γ ⊢ ★ => ★
    test("should infer type star for star (type-in-type)", () => {
      ensure(typecheck(defs(), adts(), [], Star(), Star()));
    });
  });

  describe("app", () => {
    //
    // Γ ⊢ f => Πx:A. B
    // Γ ⊢ a <= A
    // ------------------- app
    // Γ ⊢ f(a) => B[a/x]

    test("should infer f and use that to check the type of the argument", () => {
      const ctx: Context = [{ name: "a", typ: Ref("A"), type: "bind" }];
      ensure(
        typecheck(
          defs([
            // A:★
            Def("A", Ann(Abs("x", Var("x", 0)), Star())),
            // B:★
            Def("B", Ann(Abs("x", Var("x", 0)), Star())),
            // f:A->B
            Def(
              "f",
              Ann(Abs("a", Abs("x", Var("x", 0))), Pi("", Ref("A"), Ref("B")))
            ),
          ]),
          adts(),
          ctx,
          App(Ref("f"), Var("a", 0)), // f(a):B
          Ref("B")
        )
      );
    });

    test("should reject applications where the lhs is not an arrow", () => {
      const ctx: Context = [
        { type: "bind", name: "b", typ: Star() },
        { type: "bind", name: "a", typ: Star() },
      ];
      const program = App(Var("a", 0), Var("b", 1));
      try {
        infer(defs(), adts(), ctx, program, 0, 0);
      } catch (e) {
        expect(e).toStrictEqual({
          _: "typecheckerror",
          end: 0,
          msg: "expected function got ★",
          start: 0,
        });
        return;
      }
      throw "expected exception";
    });
  });

  describe("ann", () => {
    //    Γ ⊢ a <= A
    // ---------------- annot
    // Γ ⊢ (a : A) => A

    test("should error if the type doesn't match the annotation", () => {
      const ctx: Context = [{ name: "a", typ: Ref("A"), type: "bind" }];
      try {
        const result = typecheck(
          defs([
            Def("A", Ann(Abs("x", Abs("y", Var("y", 0))), Star())),
            Def("B", Ann(Abs("x", Abs("y", Var("x", 1))), Star())),
          ]),
          adts(),
          ctx,
          Ann(Var("a", 0), Ref("B")),
          Ref("B")
        );
      } catch (e) {
        const result = e as TypecheckError;
        expect(result.msg).toBe(`typecheck failed: B is not A`);
        return;
      }
      throw "expected checker failure";
    });

    test("should check type of a matches the annotation", () => {
      const ctx: Context = [{ name: "a", typ: Ref("A"), type: "bind" }];
      ensure(
        typecheck(
          defs([
            Def("A", Ann(Abs("x", Var("x", 0)), Star())),
            Def("B", Ann(Abs("x", Var("x", 0)), Star())),
          ]),
          adts(),
          ctx,
          Ann(Var("a", 0), Ref("A")),
          Ref("A")
        )
      );
    });

    test("should infer type from annotation", () => {
      // Γ=[A::*]  (λa:A. a):A->A
      const program = Ann(
        Abs("a", Var("a", 0)),
        Pi("", Var("A", 0), Var("A", 1))
      );
      ensure(
        infer(
          defs(),
          adts(),
          [{ type: "bind", name: "A", typ: Star() }],
          program,
          0,
          0
        )
      );
    });
  });

  describe("term reduction", () => {
    // (λx. x)(λz. z) -> (λz. z)
    test("TestReduceIdentity", () => {
      const identity = App(Abs("x", Var("x", 0)), Abs("z", Var("z", 0)));
      const expected: Term = Abs("z", Var("z", 0));

      const actual = reduce(true, [], defs(), identity);

      expect(actual).toStrictEqual(expected);
    });

    // λx. x
    const id = Def(
      "id",
      Ann(Abs("x", Var("x", 0)), Pi("", Ref("X"), Ref("X")))
    );

    // Test that substituting top level functions works properly.
    test("TestSubstituteDef", () => {
      const expected = Abs("z", Var("z", 0));
      const actual = reduce(
        true,
        [],
        defs([id]),
        App(Ref("id"), Abs("z", Var("z", 0)))
      );
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

      const actual = reduce(true, [], defs(), src);

      expect(actual).toStrictEqual(expected);
    });

    test("should not be able to reduce id", () => {
      expect(reduce(false, [], defs(), Abs("x", Var("x", 0)))).toStrictEqual(
        Abs("x", Var("x", 0))
      );
    });

    test("should not reduce refs", () => {
      expect(reduce(false, [], defs(), Ref("ref"))).toStrictEqual(Ref("ref"));
    });

    test("should not reduce constructors", () => {
      expect(
        reduce(false, [], defs(), App(Ref("succ"), Ref("zero")))
      ).toStrictEqual(App(Ref("succ"), Ref("zero")));
    });

    test("should reduce id(id) to id", () => {
      expect(
        reduce(
          false,
          [],
          defs(),
          App(Abs("x", Var("x", 0)), Abs("x", Var("x", 0)))
        )
      ).toStrictEqual(Abs("x", Var("x", 0)));
    });
  });

  test("should check polymorphic double function", () => {
    // λT:*. λf:T→T. λx:T. f(f(x))
    // * -> T -> T -> T -> T
    const double = Abs(
      "T",
      Abs("f", Abs("x", App(Var("f", 1), App(Var("f", 1), Var("x", 0)))))
    );
    ensure(
      typecheck(
        defs([
          Def("T", Ann(Abs("x", Var("x", 0)), Pi("", Ref("X"), Ref("X")))),
        ]),
        adts(),
        [],
        double,
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
  });

  // and : * -> * -> *
  // and = λp. λq. Πc:*. (p -> q -> c) -> c
  let and = Def(
    "and",
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

  test("should check type-level and function", () => {
    ensure(infer(defs(), adts(), [], and.term, 0, 0));
  });

  // conj : Πp:*. Πq:*. p -> q -> and p q
  // conj = λp. λq. λx. λy. λc. λf. f x y
  let conj = Def(
    "conj",
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

  test("should check type-level conjunction function", () => {
    ensure(infer(defs([and]), adts(), [], conj.term, 0, 0));
  });

  // proj1 : Πp:*. Πq:*. and p q → p
  // proj1 : λp. λq. λa. a p (λx. λy. x)
  let proj1 = Def(
    "proj1",
    Ann(
      Abs(
        "p",
        Abs(
          "q",
          Abs(
            "a",
            App(App(Var("a", 0), Var("p", 2)), Abs("x", Abs("y", Var("x", 1))))
          )
        )
      ),
      Pi(
        "p",
        Star(),
        Pi(
          "q",
          Star(),
          Pi("", App(App(Ref("and"), Var("p", 1)), Var("q", 0)), Var("p", 2))
        )
      )
    )
  );

  test("proj1 checks", () => {
    ensure(infer(defs([and]), adts(), [], proj1.term, 0, 0));
  });

  // proj2 : Πp:*. Πq:*. and p q → q
  // proj2 = λp.   λq. λa. a q (λx. λy. y)
  let proj2 = Def(
    "proj2",
    Ann(
      Abs(
        "p",
        Abs(
          "q",
          Abs(
            "a",
            App(App(Var("a", 0), Var("q", 1)), Abs("x", Abs("y", Var("y", 0))))
          )
        )
      ),
      Pi(
        "p",
        Star(),
        Pi(
          "q",
          Star(),
          Pi("", App(App(Ref("and"), Var("p", 1)), Var("q", 0)), Var("q", 1))
        )
      )
    )
  );

  test("proj2 checks", () => {
    ensure(infer(defs([and]), adts(), [], proj2.term, 0, 0));
  });

  // and_commutes : Πp:*. Πq:*. and p q → and q p
  // and_commutes = λp. λq. λa. conj q p (proj2 p q a) (proj1 p q a)
  const andCommutes = Def(
    "and_commutes",
    Ann(
      Abs(
        "p",
        Abs(
          "q",
          Abs(
            "a",
            App(
              App(
                App(App(Ref("conj"), Var("q", 1)), Var("p", 2)),
                App(
                  App(App(Ref("proj2"), Var("p", 2)), Var("q", 1)),
                  Var("a", 0)
                )
              ),
              App(App(App(Ref("proj1"), Var("p", 2)), Var("q", 1)), Var("a", 0))
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
            App(App(Ref("and"), Var("p", 1)), Var("q", 0)),
            App(App(Ref("and"), Var("q", 1)), Var("p", 2))
          )
        )
      )
    )
  );

  test("type-level and commutes", () => {
    // and(p,q) => and(q,p)
    // Logically, if we have an and(p,q) we can project out the components p,q
    // and construct an element of and(q,p) as desired.
    ensure(
      infer(defs([and, conj, proj1, proj2]), adts(), [], andCommutes.term, 0, 0)
    );
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

    const tru = Abs("X", Abs("t", Abs("f", Var("t", 1))));
    const fls = Abs("X", Abs("t", Abs("f", Var("f", 0))));

    let result = typecheck(defs(), adts(), [], tru, Bool);
    let result2 = typecheck(defs(), adts(), [], fls, Bool);
  });

  /*
    type Bool = false | true

    This creates the following functions:
      true : Bool
      false : Bool

    The parser should build the following:
      Bool = ιb. ΠP:Bool→*.
        P(Bool.true) →
        P(Bool.false) →
        P(b)
      true = (P) (t) (f) t
      false = (P) (t) (f) f

    To generalise a little:
      T : Type = ιt. ΠP:T→*.
        P(constructor1) →
        P(constructor2) →
        ...
        P(constructorN) →
        P(t)
      constructor1 : T = (P) (c1) (c2) ... (cN) c1
      constructor2 : T = (P) (c1) (c2) ... (cN) c2
      ...
      constructorN : T = (P) (c1) (c2) ... (cN) cN

      i.e.
      define a top-level def T:Type = as above
      define n constructors; constructor1 through constructorN.
      Def()

    Example values of this type:
      true : Bool
      false : Bool

    You can eliminate a Bool using a case statement:
      case b of
        true => "t"
        false => "f"
        : String
    desugars
      case x as t : m
    becomes
      x<(t) m>
    i.e.
      b((t) => String, "t", "f")
    In the case that b == true:
      true((t) => String, "t", "f") // def true = (P) (t) (f) t
      "t"
  */
  test("true is generated correctly", () =>
    expect(pretty(tru.term)).toBe(
      pretty(Abs("P", Abs("false", Abs("true", Var("true", 0)))))
    ));

  test("false is generated correctly", () =>
    expect(pretty(fls.term)).toBe(
      pretty(Abs("P", Abs("false", Abs("true", Var("false", 1)))))
    ));

  test("Bool term is generated correctly", () =>
    expect(pretty(bool.term)).toBe(
      pretty(
        Self(
          "t",
          Pi(
            "P",
            Pi("", Ref("Bool"), Star()),
            Pi(
              "",
              App(Var("P", 0), Ref("false")),
              Pi(
                "",
                App(Var("P", 1), Ref("true")),
                App(Var("P", 2), Var("t", 3))
              )
            )
          )
        )
      )
    ));

  test("true is a bool", () =>
    ensure(
      typecheck(defs([tru, fls, bool]), adts(), [], tru.term.term, bool.term)
    ));

  test("false is a bool", () =>
    ensure(
      typecheck(defs([tru, fls, bool]), adts(), [], fls.term.term, bool.term)
    ));

  test("Bool is a type", () =>
    ensure(
      typecheck(defs([tru, fls, bool]), adts(), [], bool.term.term, Star())
    ));

  test("recursive types", () => {
    /*
        type Nat = zero | succ(x Nat)

        This creates the following functions:
          zero : Nat
          succ : Nat → Nat

        The parser should build the following:
          Nat = ιm. ΠP:Nat→*.
            P(zero) →
            ((x Nat) → P(succ(x))) →
            P(m)
          zero = <P> (z) (s) z
          succ = (n) <P> (z) (s) s(n)

        Example values of this type:
          zero : Nat
          succ(succ(zero)) : Nat

        You can eliminate a Nat using a case statement:
          case n of
            zero => true
            succ => false
            : Bool
      */

    // ιt. ΠP:Nat→*. P(Nat.zero) → (Πn:Nat. P(Nat.succ(n))) → P(t)
    expect(pretty(nat.term)).toBe(
      pretty(
        Self(
          "t",
          Pi(
            "P",
            Pi("", Ref("Nat"), Star()),
            Pi(
              "",
              App(Var("P", 0), Ref("zero")),
              Pi(
                "",
                Pi(
                  "n",
                  Ref("Nat"),
                  App(Var("P", 2), App(Ref("succ"), Var("n", 0)))
                ),
                App(Var("P", 2), Var("t", 3))
              )
            )
          )
        )
      )
    );
  });

  test("one is a Nat", () => {
    const defns = defs([nat, zero, succ, bool, tru, fls]);
    const one = App(succ.term, zero.term); // succ(zero)
    const onewhnf = te(reduce(false, [], defns, one));
    ensure(typecheck(defns, adts(), [], onewhnf, nat.term));
  });

  test("succ(zero) should have type Nat", () => {
    const defns = defs([nat, zero, succ, bool, tru, fls]);
    const n = App(Ref("succ"), Ref("zero")); // succ(zero)
    ensure(typecheck(defns, adts(), [], n, nat.term));
  });

  test("eliminate nat", () => {
    const defns = defs([nat, zero, succ, bool, tru, fls]);
    const n = App(Ref("succ"), Ref("zero")); // succ(zero)
    const P = Abs("P", Ref("Bool")); // λP. Bool
    const eliminator = App(App(App(n, P), Ref("true")), Abs("n", Ref("false")));
    ensure(typecheck(defns, adts(), [], eliminator, bool.term.term));

    const reduced = reduce(true, [], defns, eliminator);
    expect(pretty(reduced)).toBe("λP λfalse λtrue false");
  });

  test("simple parameterised types", () => {
    /*
        type Maybe<T *> = null | just(value T)

        This creates the following functions (in the final language design: T is
        always inferred from the usage, if it's unclear an annotation is
        required). We need to create the definitions with the type parameters
        first (the T) followed by any constructor arguments:
          null : (T *) → Maybe<T>
          just : (T *) → T → Maybe<T>

        The parser generates:
          Maybe: (A *) → * =
            (A)
              ιt. ΠP:Maybe(A)→*.
              P(null(A)) →
              ((value A) → P(just(A)(value))) →
              P(t)
          just: (A *) → (value A) → Maybe(A) =
            (A) (value)
            (P) (null) (just) just(A)(value)
          null: (A *) → Maybe(A) =
            (A)
            (P) (null) (just) null(A)

        Example values of this type:
          null(Int) : Maybe<Int>
          just(Int, 6) : Maybe<Int>

          func hello(name Maybe<String>) = case name of
            null => "world"
            just => fmt.Sprintf("hello %s", name.value)
          hello(null(String)) // TODO: the type Maybe<String> is inferred from the usage
          hello(just(String, "世界")) // TODO: the type Maybe<String> can also be inferred from the argument

        You can eliminate a Maybe using a case statement:
          case m of
            null => "n"
            just => "j"
            : String
      */

    // λA. ιt. ΠP:Maybe(A)→*. P(null(A)) → ((value A) → P(just(A)(value))) → P(t)
    expect(pretty(maybe.term)).toBe(
      pretty(
        Abs(
          "A",
          Self(
            "t",
            Pi(
              "P",
              Pi("", App(Ref("Maybe"), Var("A", 1)), Star()),
              Pi(
                "",
                App(Var("P", 0), App(Ref("null"), Var("A", 2))),
                Pi(
                  "",
                  Pi(
                    "value",
                    Var("A", 3),
                    App(
                      Var("P", 2),
                      App(App(Ref("just"), Var("A", 4)), Var("value", 0))
                    )
                  ),
                  App(Var("P", 2), Var("t", 3))
                )
              )
            )
          )
        )
      )
    );

    /*
      null: (A *) → Maybe(A) =
        (A)
        (P) (null) (just) null
    */
    expect(pretty(mnull.term.typ)).toBe(
      pretty(Pi("A", Star(), App(Ref("Maybe"), Var("A", 0))))
    );

    expect(pretty(mnull.term.term)).toBe(
      pretty(Abs("A", Abs("P", Abs("null", Abs("just", Var("null", 1))))))
    );

    /*
      just: (A *) → (value A) → Maybe(A) =
        (A) (value)
        (P) (null) (just) just(value)
      */
    expect(pretty(just.term.typ)).toBe(
      pretty(
        Pi(
          "A",
          Star(),
          Pi("value", Var("A", 0), App(Ref("Maybe"), Var("A", 1)))
        )
      )
    );

    expect(pretty(just.term.term)).toBe(
      pretty(
        Abs(
          "A",
          Abs(
            "value",
            Abs(
              "P",
              Abs("null", Abs("just", App(Var("just", 0), Var("value", 3))))
            )
          )
        )
      )
    );
  });

  test("eliminate maybe", () => {
    // Check an instantiation: just(Bool, true)
    let result3 = ensure(
      typecheck(
        defs([bool, tru, fls, maybe, mnull, just]),
        adts(),
        [],
        App(App(Ref("just"), Ref("Bool")), Ref("true")),
        App(Ref("Maybe"), Ref("Bool"))
      )
    );

    // x = just(Bool)(true)
    // case x of
    //  null -> false
    //  just -> x.value
    // => evaluates to true
    // is:
    // x((m) Bool, false, (value) value)
    const caseExp = App(
      App(App(result3.term, Abs("m", Ref("Bool"))), Ref("false")),
      Abs("value", Var("value", 0))
    );

    const reduced = reduce(
      true,
      [],
      defs([bool, tru, fls, maybe, mnull, just]),
      caseExp
    );
    expect(reduced).toStrictEqual(tru.term.term);
  });

  test("null checks", () => {
    console.log(
      `checking ${pretty(mnull.term.term)} has type ${pretty(mnull.term.typ)}`
    );
    ensure(
      typecheck(
        defs([maybe, mnull, just]),
        adts(),
        [],
        mnull.term.term,
        mnull.term.typ
      )
    );
  });

  test("just checks", () => {
    ensure(
      typecheck(
        defs([maybe, mnull, just]),
        adts(),
        [],
        just.term.term,
        just.term.typ
      )
    );
  });

  test("recursive parameterised types", () => {
    /*
      // List is a singly-linked list with elements of type T.
      type List(T *) =
        // nil constructs an empty list.
        nil |
        // cons constructs a list by passing a head element and an
        // existing (though possibly empty) list.
        cons(
          // head is the first element of the list.
          head T,
          // tail is the remaining elements in the list.
          tail List<T>)

      This creates the following functions (in the final language design: T is
      always inferred from the usage, if it's unclear an annotation is
      required). We need to create the definitions with the type parameters
      first (the T) followed by any constructor arguments:
        nil : (T *) → List<T>
        cons : (T *) → (head T) → (tail List<T>) → List<T>

      The parser generates:
        List = (A)
          ιm. ΠP:List<A>→*.
          P(nil<A>) →
          ((head A) → (tail List<A>) → P(cons<A>(head)(tail))) →
          P(m)
        cons =
          <A> (head) (tail)
          <P> (nil) (cons) cons(head)(tail)
        nil =
          <A>
          <P> (nil) (cons) nil

      Example values of this type:
        nil(Int) : List<Int> // on it's own it requires an annotation, i.e.
                              // let xs = nil : List<Int>
        cons(Int, 1, nil(Int)) : List<Int>
        cons(Int, 1, cons(Int, 2, cons(Int, 3, nil(Int)))) : List<Int>

        // In the constructors for List we know that T has type *, but for
        // ordinary functions we need the T somewhere, or else we wouldn't know
        // what it is (and what type it is).
        func append(T *, a T, l List<T>) List<T> = cons(a, l)
        let l = append(Int, 4, [1,2,3])

        // In a future version:
        let l = append(4, [1,2,3])

      You can eliminate a List using a case statement:
        case l of
          nil => "n"
          cons => "c"
          : String
      */

    // λA. ιt. ΠP:List(A)→*. P(nil(A)) → ((head A) → (tail List(A)) → P(cons(A)(head)(tail))) → P(t)
    expect(pretty(list.term)).toBe(
      pretty(
        Abs(
          "A",
          Self(
            "t",
            Pi(
              "P",
              Pi("", App(Ref("List"), Var("A", 1)), Star()),
              Pi(
                "",
                App(Var("P", 0), App(Ref("nil"), Var("A", 2))),
                Pi(
                  "",
                  Pi(
                    "head",
                    Var("A", 3),
                    Pi(
                      "tail",
                      App(Ref("List"), Var("A", 3)),
                      App(
                        Var("P", 3),
                        App(
                          App(App(Ref("cons"), Var("A", 5)), Var("head", 1)),
                          Var("tail", 0)
                        )
                      )
                    )
                  ),
                  App(Var("P", 2), Var("t", 3))
                )
              )
            )
          )
        )
      )
    );

    /*
      nil: (T *) → List<T>  =
        <T>
        <P> (nil) (cons) nil
      */

    expect(pretty(nil.term.typ)).toBe(
      pretty(Pi("A", Star(), App(Ref("List"), Var("A", 0))))
    );

    expect(pretty(nil.term.term)).toBe(
      pretty(Abs("A", Abs("P", Abs("nil", Abs("cons", Var("nil", 1))))))
    );

    /*
      cons: (T *) → T → List<T> → List<T> =
        <T> (head) (tail)
        <P> (nil) (cons) cons(head)(tail)
    */
    expect(pretty(cons.term.term)).toBe(
      pretty(
        Abs(
          "A",
          Abs(
            "head",
            Abs(
              "tail",
              Abs(
                "P",
                Abs(
                  "nil",
                  Abs(
                    "cons",
                    App(App(Var("cons", 0), Var("head", 4)), Var("tail", 3))
                  )
                )
              )
            )
          )
        )
      )
    );

    expect(pretty(cons.term.typ)).toBe(
      pretty(
        Pi(
          "A",
          Star(),
          Pi(
            "head",
            Var("A", 0),
            Pi(
              "tail",
              App(Ref("List"), Var("A", 1)),
              App(Ref("List"), Var("A", 2))
            )
          )
        )
      )
    );
  });

  test("nil checks", () => {
    ensure(infer(defs([list, nil, cons]), adts([]), [], nil.term, 0, 0));
  });

  test("cons checks", () => {
    ensure(infer(defs([list, nil, cons]), adts([]), [], cons.term, 0, 0));
  });

  test("pair checks", () => {
    ensure(infer(defs([pair, ppair]), adts([]), [], ppair.term, 0, 0));
  });

  // // FIXME: this test blows the stack because the return type of snd is
  // // incorrect. This should return a valid typecheck error.
  // test("ensure wrong type fails", () => {
  //   const src = `
  //   type Bool = false | true
  //   type Nat = zero | succ(x Nat)
  //   type Pair(A *, B *) = pair(a A, b B)

  //   func snd:(Pair(Bool)(Nat))->Bool = λp case p of
  //   pair -> p.b
  //   `;
  //   const t = build(src);
  //   if (t._ == "parseerror") throw `parse failed: ${t.error}`;
  //   if (t._ == "typecheckerror") throw `check failed: ${t.msg}`;
  // });

  test("type constructor with multiple arguments", () => {
    const src = `
    type Bool = false | true
    type Pair(A *, B *) = pair(a A, b B)
    func ex:Pair(Bool)(Bool) = pair(Bool)(Bool)(true)(true)    
    `;

    const t = build(src);
    if (t.checkerErrors.length != 0) throw `check failed`;
  });

  // FIXME:
  // test("let statements should typecheck", () => {
  //   // the typechecker should infer the expression of the let statement as Bool
  //   // then with [x:Bool] check that the body of the let statement is of type
  //   // Bool.
  //   //
  //   // func ex:Bool->Bool = λb let x = b in x

  //   const term = Abs("b", Let(Identifier("x"), Var("b", 0), Var("x", 0)));
  //   const type = Pi("", Ref("Bool"), Ref("Bool"));
  //   const actual = ensure(
  //     typecheck(defs([tru, fls, bool]), adts(), [], term, type, 0)
  //   );
  //   expect(pretty(actual.type)).toBe("P(false)→P(true)→P(b)");
  // });

  test("bool match 3", () => {
    // b:Bool, P:(Πx:Bool. ★), t:P(true), f:P(false)];
    const ctx: Context = [
      { type: "bind", name: "b", typ: Ref("Bool") },
      { type: "bind", name: "P", typ: Pi("x", Ref("Bool"), Star()) },
      { type: "bind", name: "t", typ: App(Var("P", 0), Ref("true")) },
      { type: "bind", name: "f", typ: App(Var("P", 1), Ref("false")) },
    ];
    const term = App(Var("b", 3), Var("P", 2));
    const actual = ensure(
      infer(defs([tru, fls, bool]), adts(), ctx, term, 0, 0)
    );
    expect(pretty(actual.type)).toBe("P(false)→P(true)→P(b)");
  });

  test("double negation proof", () => {
    const src = `
    type Bool = true | false
    func not:Bool->Bool = λb b(λx Bool)(false)(true)
    func equal: ΠA:* Πa:A Πb:A * = λA λa λb ΠP:(A->*) Πp:P(a) P(b)
    func refl: ΠA:* Πx:A equal(A)(x)(x) = λA λx λP λp p
    func nn: Πb:Bool equal(Bool)(not(not(b)))(b) = λb
      b(λx equal(Bool)(not(not(x)))(x))(refl(Bool)(true))(refl(Bool)(false))
    `;

    const t = parseFile({ src, idx: 0 });
    if (t._ == "parseerror") throw "unexpected parse error";
    const f = processADTs(t.value);
    const adtList = t.value.content.filter((c) => c._ == "adt") as ADT[];
    const adts = new Map<string, ADT>();
    for (const adt of adtList) {
      adts.set(identifier2str(adt.name), adt);
    }
    const defs = (f.content.filter((c) => c._ == "def") as Def[]).map((def) =>
      desugar(def, adts)
    );
    let defsMap: Map<string, Def> = new Map();
    for (const def of defs) {
      defsMap.set(def.name, def);
    }
    const nn = defsMap.get("nn")!;

    const c = typecheck(defsMap, adts, [], nn.term.term, nn.term.typ);
  });

  test("reflexivity", () => {
    const src = `
    type Bool = true | false
    // refl creates an instance of x==x
    func equal: ΠA:* Πa:A Πb:A * = λA λa λb ΠP:(Πx:A *) Πp:P(a) P(b)
    func refl: ΠA:* Πx:A equal(A)(x)(x) = λA λx λP λp p
    func rt: equal(Bool)(true)(true) = refl(Bool)(true)
    `;

    const t = parseFile({ src, idx: 0 });
    if (t._ == "parseerror") throw "unexpected parse error";
    const f = processADTs(t.value);
    const adtList = t.value.content.filter((c) => c._ == "adt") as ADT[];
    const adts = new Map<string, ADT>();
    for (const adt of adtList) {
      adts.set(identifier2str(adt.name), adt);
    }
    const defs = (f.content.filter((c) => c._ == "def") as Def[]).map((def) =>
      desugar(def, adts)
    );
    let defsMap: Map<string, Def> = new Map();
    for (const def of defs) {
      defsMap.set(def.name, def);
    }
    const rt = defsMap.get("rt")!;

    const c = typecheck(defsMap, adts, [], rt.term.term, rt.term.typ);
  });

  describe("type equality", () => {
    const id = Def(
      "id",
      Ann(Abs("x", Var("x", 0)), Pi("", Ref("X"), Ref("X")))
    );

    const Nat: Term = Ref("Nat");
    const Bool: Term = Ref("Bool");

    // The identity type operator λX.X: when applied to any type it gives back
    // the argument.
    const Id: Term = Abs("A", Var("A", 0));

    const ds = defs([
      Def("Nat", Ann(id.term, Star())),
      Def("Bool", Ann(id.term, Star())),
    ]);

    // The type Nat→Bool.
    const NatToBool: Term = Pi("", Nat, Bool);

    const eq = (a: Term, b: Term) => equate([], ds, a, b);

    test("Nat→Bool === Nat→Bool", () =>
      expect(eq(NatToBool, NatToBool).eq).toBe(true));

    test("Nat→Bool === Nat→Id(Bool)", () => {
      let s = Pi("", Nat, App(Id, Bool));
      expect(eq(NatToBool, s).eq).toBe(true);
    });

    test("Nat→Bool === Id(Nat)→Id(Bool)", () =>
      expect(eq(NatToBool, Pi("", App(Id, Nat), App(Id, Bool))).eq).toBe(true));

    test("Nat→Bool === Id(Nat)→Bool", () =>
      expect(eq(NatToBool, Pi("", App(Id, Nat), Bool)).eq).toBe(true));

    test("Nat→Bool === Id(Nat→Bool)", () =>
      expect(eq(NatToBool, App(Id, Pi("", Nat, Bool))).eq).toBe(true));

    test("Nat→Bool === Id(Id(Id(Nat)→Bool))", () => {
      const t = App(Id, App(Id, Pi("", App(Id, Nat), Bool)));
      expect(eq(NatToBool, t).eq).toBe(true);
    });

    test("* === Id(*)", () => {
      expect(eq(Star(), App(Id, Star())).eq).toBe(true);
    });

    test("id === id(id)", () => {
      expect(
        eq(
          Abs("x", Var("x", 0)),
          App(Abs("y", Var("y", 0)), Abs("z", Var("z", 0)))
        ).eq
      ).toBe(true);
    });

    test("true != false", () => {
      expect(
        eq(Abs("t", Abs("f", Var("t", 1))), Abs("t", Abs("f", Var("f", 0)))).eq
      ).toBe(false);
    });

    test("one != two", () => {
      // λs. λz. s z
      const one = Abs("s", Abs("z", App(Var("s", 1), Var("z", 0))));

      // λs. λz. s (s z)
      const two = Abs(
        "s",
        Abs("z", App(Var("s", 1), App(Var("s", 1), Var("z", 0))))
      );

      expect(eq(one, two).eq).toBe(false);
    });
  });
});
