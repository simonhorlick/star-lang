import { describe, expect, test } from "vitest";
import { Def, Self, Term, definition, stripAST } from "./ast";
import { check, equate, infer, TypecheckError, defs, adts } from "./typecheck";
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
  and,
  conj,
  proj1,
  proj2,
  andCommutes,
  unit,
  unt,
} from "./test_defs";
import { reduce } from "./equal";
import { Context } from "./context";
import { desugar } from "./process";
import { Stream, parseErrorDiagnostic, Result as ParserResult } from "./parser";

export const ts = (s: string): Stream => ({
  src: `parsed${s}`,
  idx: 6,
});

export const result = <T>(x: ParserResult<T>) => {
  if (x._ == "parseerror") {
    const msg = parseErrorDiagnostic(x);
    throw msg;
  } else {
    return x.value;
  }
};

const pdef = (s: string): Def =>
  desugar(stripAST(result(definition(ts(s)))) as Def, adts());

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
      expect(infer(defs(), adts(), ctx, Var("x", 0), 0, 0).type).toStrictEqual(
        Ref("A")
      );
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
        check(
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

    test("should check that a lambda has a pi type", () =>
      check(
        defs([Def("A", Ann(Abs("x", Var("x", 0)), Star()))]),
        adts(),
        [],
        Abs("a", Var("a", 0)),
        Pi("", Ref("A"), Ref("A"))
      ));
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
      check(
        defs([
          Def("A", Ann(Abs("x", Var("x", 0)), Star())),
          Def("B", Ann(Abs("x", Var("x", 0)), Star())),
        ]),
        adts(),
        [],
        Pi("", Ref("A"), Ref("B")),
        Star()
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
      check(defs(), adts(), [], Star(), Star());
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
      check(
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
        check(
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
        expect(result.msg).toBe(`typecheck failed: B is not A in ctx [a:A]`);
        return;
      }
      throw "expected checker failure";
    });

    test("should check type of a matches the annotation", () => {
      const ctx: Context = [{ name: "a", typ: Ref("A"), type: "bind" }];
      check(
        defs([
          Def("A", Ann(Abs("x", Var("x", 0)), Star())),
          Def("B", Ann(Abs("x", Var("x", 0)), Star())),
        ]),
        adts(),
        ctx,
        Ann(Var("a", 0), Ref("A")),
        Ref("A")
      );
    });

    test("should infer type from annotation", () => {
      // Γ=[A::*]  (λa:A. a):A->A
      const program = Ann(
        Abs("a", Var("a", 0)),
        Pi("", Var("A", 0), Var("A", 1))
      );
      infer(
        defs(),
        adts(),
        [{ type: "bind", name: "A", typ: Star() }],
        program,
        0,
        0
      );
    });
  });

  test("should check polymorphic double function", () => {
    // λT:*. λf:T→T. λx:T. f(f(x))
    // * -> T -> T -> T -> T
    const double = Abs(
      "T",
      Abs("f", Abs("x", App(Var("f", 1), App(Var("f", 1), Var("x", 0)))))
    );
    check(
      defs([Def("T", Ann(Abs("x", Var("x", 0)), Pi("", Ref("X"), Ref("X"))))]),
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
    );
  });

  test("should check type-level and function", () =>
    check(defs(), adts(), [], and.term.term, and.term.typ));

  test("should check type-level conjunction function", () =>
    check(defs([and]), adts(), [], conj.term.term, conj.term.typ));

  test("proj1 checks", () =>
    check(defs([and]), adts(), [], proj1.term.term, proj1.term.typ));

  test("proj2 checks", () => {
    check(defs([and]), adts(), [], proj2.term.term, proj2.term.typ);
  });

  test("type-level and commutes", () =>
    // and(p,q) => and(q,p)
    // Logically, if we have an and(p,q) we can project out the components p,q
    // and construct an element of and(q,p) as desired.
    check(
      defs([and, conj, proj1, proj2]),
      adts(),
      [],
      andCommutes.term.term,
      andCommutes.term.typ
    ));

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
    check(defs([tru, fls, bool]), adts(), [], tru.term.term, bool.term));

  test("false is a bool", () =>
    check(defs([tru, fls, bool]), adts(), [], fls.term.term, bool.term));

  test("Bool is a type", () =>
    check(defs([tru, fls, bool]), adts(), [], bool.term.term, Star()));

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
    const one = App(succ.term, zero.term); // succ(zero)
    check(defs([nat, zero, succ, bool, tru, fls]), adts(), [], one, nat.term);
  });

  test("succ(zero) should have type Nat", () => {
    const n = App(Ref("succ"), Ref("zero")); // succ(zero)
    check(defs([nat, zero, succ, bool, tru, fls]), adts(), [], n, nat.term);
  });

  test("eliminate nat", () => {
    const defns = defs([nat, zero, succ, bool, tru, fls]);
    const n = App(Ref("succ"), Ref("zero")); // succ(zero)
    const P = Abs("P", Ref("Bool")); // λP. Bool
    const eliminator = App(App(App(n, P), Ref("true")), Abs("n", Ref("false")));
    check(defns, adts(), [], eliminator, bool.term.term);

    const reduced = reduce(true, [], defns, eliminator);
    expect(pretty(reduced)).toBe("λP λfalse λtrue false");
  });

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
  test("Maybe is generated correctly", () =>
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
    ));

  test("type of null is generated correctly", () =>
    /*
      null: (A *) → Maybe(A) =
        (A)
        (P) (null) (just) null
    */
    expect(pretty(mnull.term.typ)).toBe(
      pretty(Pi("A", Star(), App(Ref("Maybe"), Var("A", 0))))
    ));

  test("null is generated correctly", () =>
    expect(pretty(mnull.term.term)).toBe(
      pretty(Abs("A", Abs("P", Abs("null", Abs("just", Var("null", 1))))))
    ));

  test("type of just is generated correctly", () =>
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
    ));

  test("just is generated correctly", () =>
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
    ));

  const justTrue = App(App(Ref("just"), Ref("Bool")), Ref("true"));

  test("just(Bool)(true):Maybe(Bool)", () =>
    check(
      defs([bool, tru, fls, maybe, mnull, just]),
      adts(),
      [],
      justTrue,
      App(Ref("Maybe"), Ref("Bool"))
    ));

  test("eliminate maybe", () => {
    // We can eliminate a type by providing a term for each of the values of a
    // sum type. This is how case statements are implemented. In the following
    // example we provide a term for `null` and a term for `just` to the term
    // `just(Bool)(true)`. As it's a `just` we should get back the value we
    // passed for the `just` case - `x.value`.

    // let x = just(Bool)(true)
    // case x of
    //  null -> false
    //  just -> x.value

    // this is desugared as
    //  x(λm Bool, false, λvalue value)
    const caseExp = //
      App(
        App(
          App(
            justTrue, // x
            Abs("m", Ref("Bool"))
          ),
          Ref("false") // the null branch of the case statement
        ),
        Abs("value", Var("value", 0)) // the just branch of the case statement
      );

    const reduced = reduce(
      true,
      [],
      defs([bool, tru, fls, maybe, mnull, just]),
      caseExp
    );
    expect(reduced).toStrictEqual(tru.term.term);
  });

  test("null checks", () =>
    check(
      defs([maybe, mnull, just]),
      adts(),
      [],
      mnull.term.term,
      mnull.term.typ
    ));

  test("just checks", () =>
    check(
      defs([maybe, mnull, just]),
      adts(),
      [],
      just.term.term,
      just.term.typ
    ));

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

  test("list is generated correctly", () =>
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
    ));

  /*
  nil: (T *) → List<T>  =
    <T>
    <P> (nil) (cons) nil
  */
  test("type of nil is generated correctly", () =>
    expect(pretty(nil.term.typ)).toBe(
      pretty(Pi("A", Star(), App(Ref("List"), Var("A", 0))))
    ));

  test("nil is generated correctly", () =>
    expect(pretty(nil.term.term)).toBe(
      pretty(Abs("A", Abs("P", Abs("nil", Abs("cons", Var("nil", 1))))))
    ));

  /*
      cons: (T *) → T → List<T> → List<T> =
        <T> (head) (tail)
        <P> (nil) (cons) cons(head)(tail)
    */
  test("cons is generated correctly", () =>
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
    ));

  test("type of cons is generated correctly", () =>
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
    ));

  test("nil checks", () =>
    check(defs([list, nil, cons]), adts([]), [], nil.term.term, nil.term.typ));

  test("cons checks", () =>
    check(
      defs([list, nil, cons]),
      adts([]),
      [],
      cons.term.term,
      cons.term.typ
    ));

  test("pair checks", () =>
    // ppair is the constructor for the type pair
    check(defs([pair, ppair]), adts([]), [], ppair.term.term, ppair.term.typ));

  test("pair(Bool)(Bool)(true)(true):Pair(Bool)(Bool)", () =>
    check(
      defs([pair, ppair, bool, tru]),
      adts([]),
      [],
      App(
        App(App(App(Ref("pair"), Ref("Bool")), Ref("Bool")), Ref("true")),
        Ref("true")
      ),
      App(App(Ref("Pair"), Ref("Bool")), Ref("Bool"))
    ));

  // TODO:
  // test("let statements should typecheck", () => {
  //   // the typechecker should infer the expression of the let statement as Bool
  //   // then with [x:Bool] check that the body of the let statement is of type
  //   // Bool.
  //   //
  //   // func ex:Bool->Bool = λb let x = b in x

  //   const term = Abs("b", Let(Identifier("x"), Var("b", 0), Var("x", 0)));
  //   const type = Pi("", Ref("Bool"), Ref("Bool"));
  //   const actual = check(defs([tru, fls, bool]), adts(), [], term, type, 0);
  //   expect(pretty(actual.type)).toBe("P(false)→P(true)→P(b)");
  // });

  test("correct self-type is inferred for Bool(Πx:Bool ★)", () => {
    // b:Bool, P:(Πx:Bool. ★), t:P(true), f:P(false)];
    const ctx: Context = [
      { type: "bind", name: "b", typ: Ref("Bool") },
      { type: "bind", name: "P", typ: Pi("x", Ref("Bool"), Star()) },
      { type: "bind", name: "t", typ: App(Var("P", 0), Ref("true")) },
      { type: "bind", name: "f", typ: App(Var("P", 1), Ref("false")) },
    ];
    const term = App(Var("b", 3), Var("P", 2));
    const actual = infer(defs([tru, fls, bool]), adts(), ctx, term, 0, 0);
    expect(pretty(actual.type)).toBe("P(false)→P(true)→P(b)");
  });

  const not = pdef(`func not:Bool->Bool = λb b(λx Bool)(true)(false)`);

  // A value of type equal(A)(a)(b) can only be constructed if a == b.
  const equal = pdef(
    `func equal: ΠA:* Πa:A Πb:A * = λA λa λb ΠP:(A->*) Πp:P(a) P(b)`
  );
  const refl = pdef(`func refl: ΠA:* Πx:A equal(A)(x)(x) = λA λx λP λp p`);
  const nn = pdef(
    `func nn: Πb:Bool equal(Bool)(not(not(b)))(b) = λb b(λx equal(Bool)(not(not(x)))(x))(refl(Bool)(false))(refl(Bool)(true))`
  );

  test("double negation proof", () =>
    // Check that not(not(b)) == b on the type level.
    check(
      defs([bool, tru, fls, not, equal, refl]),
      adts(),
      [],
      nn.term.term,
      nn.term.typ
    ));

  const reflTrue = pdef(`func rt: equal(Bool)(true)(true) = refl(Bool)(true)`);

  test("reflexivity of true has type equal(Bool)(true)(true)", () =>
    check(
      defs([bool, tru, fls, not, equal, refl]),
      adts(),
      [],
      reflTrue.term.term,
      reflTrue.term.typ
    ));

  // A vector is essentially a List, but with the length encoded as
  // part of the type. In the following tests we hard-code the type argument of
  // the Vector to be Bool as it slightly simplifies the tests.
  //
  // Vect : Πsz:Nat ★
  //      = λsz ιt
  //        ΠP:(Πn:Nat Πx:Vect(n) ★)
  //        Πcnil:P(zero)(vnil)
  //        Πcext:(Πn:Nat Πhead:Bool Πtail:Vect(n) P(succ(n))(ext(n)(head)(tail))
  //        P(sz)(t)
  // vnil : Vect(zero)
  //      = λP λcnil λcext cnil
  //  ext : Πn:Nat Πhead:Bool Πtail:Vect(n) Vect(succ(n))
  //      = λn λhead λtail λP λcnil λcext cext(n)(head)(tail)
  const vect = Def(
    "Vect",
    Ann(
      // λsz
      Abs(
        "sz", // the length of the tail Vector
        // ιt
        Self(
          "t",
          // ΠP:(Πn:Nat Vect(n)→★)
          Pi(
            "P",
            Pi("n", Ref("Nat"), Pi("x", App(Ref("Vect"), Var("n", 0)), Star())),
            // Πcnil:P(zero)(vnil)
            Pi(
              "cnil",
              App(App(Var("P", 0), Ref("zero")), Ref("vnil")),
              // Πcext:(Πn:Nat Πhead:Bool Πtail:Vect(n) P(succ(n))(ext(n)(head)(tail))
              Pi(
                "cext",
                Pi(
                  "n",
                  Ref("Nat"),
                  Pi(
                    "head",
                    Ref("Bool"),
                    Pi(
                      "tail",
                      App(Ref("Vect"), Var("n", 1)),
                      // P(succ(n))(ext(n)(head)(tail))
                      App(
                        App(Var("P", 4), App(Ref("succ"), Var("n", 2))),
                        App(
                          App(App(Ref("ext"), Var("n", 2)), Var("head", 1)),
                          Var("tail", 0)
                        )
                      )
                    )
                  )
                ),
                App(App(Var("P", 2), Var("sz", 4)), Var("t", 3))
              )
            )
          )
        )
      ),
      Pi("sz", Ref("Nat"), Star())
    )
  );

  //  ext : Πn:Nat Πhead:Bool Πtail:Vect(n) Vect(succ(n))
  //      = λn λhead λtail λP λcnil λcext cext(n)(head)(tail)
  const ext = Def(
    "ext",
    Ann(
      // λn λhead λtail λP λcnil λcext cext(n)(head)(tail)
      Abs(
        "n",
        Abs(
          "head",
          Abs(
            "tail",
            Abs(
              "P",
              Abs(
                "cnil",
                Abs(
                  "cext",
                  App(
                    App(App(Var("cext", 0), Var("n", 5)), Var("head", 4)),
                    Var("tail", 3)
                  )
                )
              )
            )
          )
        )
      ),
      // Πn:Nat Πhead:Bool Πtail:Vect(n) Vect(succ(n))
      Pi(
        "n",
        Ref("Nat"),
        Pi(
          "head",
          Ref("Bool"),
          Pi(
            "tail",
            App(Ref("Vect"), Var("n", 1)),
            App(Ref("Vect"), App(Ref("succ"), Var("n", 2)))
          )
        )
      )
    )
  );

  // vnil : Vect(zero)
  //      = λP λcnil λcext cnil
  const vnil = Def(
    "vnil",
    Ann(
      // λP λcnil λcext cnil
      Abs("P", Abs("cnil", Abs("cext", Var("cnil", 1)))),
      // Vect(zero)
      App(Ref("Vect"), Ref("zero"))
    )
  );

  test("vnil has type Vect(zero)", () =>
    check(
      defs([nat, zero, succ, vect, vnil, ext, bool, tru, fls]),
      adts(),
      [],
      vnil.term.term,
      vnil.term.typ
    ));

  test("ext has type Πn:Nat Πhead:Bool Πtail:Vect(n) Vect(succ(n))", () =>
    check(
      defs([nat, zero, succ, vect, vnil, ext, bool, tru, fls]),
      adts(),
      [],
      ext.term.term,
      ext.term.typ
    ));

  test("the type of ext(0)(true)(vnil) is Vect(1)", () => {
    // The n in the argument to ext is the size of the tail vector, which as
    // it's vnil gives 0.
    const one = App(Ref("succ"), Ref("zero"));
    const tm = App(App(App(Ref("ext"), Ref("zero")), Ref("true")), Ref("vnil"));
    const ty = App(Ref("Vect"), one);

    expect(
      pretty(
        infer(
          defs([nat, zero, succ, vect, vnil, ext, bool, tru, fls]),
          adts(),
          [],
          tm,
          0,
          0
        ).type
      )
    ).toStrictEqual(pretty(ty));
  });

  // vhead returns the first element of a Vector. If the vector is empty the
  // return type is Unit - which gives a type error if the user attempts to use
  // it where the element type is required.
  const vhead = Def(
    "vhead",
    Ann(
      // λn λxs xs(...)(unit)(λn λhead λtail head)
      Abs(
        "n",
        Abs(
          "xs",
          App(
            App(
              App(
                Var("xs", 0),
                Abs(
                  "n",
                  Abs(
                    "x",
                    // return type needs to be a case statement:
                    // n(λP *)(Unit)(λn Bool)
                    App(
                      App(App(Var("n", 1), Abs("P", Star())), Ref("Unit")),
                      Abs("n", Ref("Bool"))
                    )
                  )
                )
              ),
              Ref("unit")
            ),
            Abs("n", Abs("head", Abs("tail", Var("head", 1))))
          )
        )
      ),
      // Πn:Nat xs:Vect(n) n(λP *)(Unit)(λv Bool)
      Pi(
        "n",
        Ref("Nat"),
        Pi(
          "xs",
          App(Ref("Vect"), Var("n", 0)),
          // n(λP *)(Unit)(λv Bool)
          App(
            App(App(Var("n", 1), Abs("P", Star())), Ref("Unit")),
            Abs("v", Ref("Bool"))
          )
        )
      )
    )
  );

  test("vhead has type blah", () => {
    check(
      defs([nat, zero, succ, vect, vnil, ext, bool, tru, fls, unit, unt]),
      adts(),
      [],
      vhead.term.term,
      vhead.term.typ,
      0
    );
  });

  test("vhead allows non-empty Vectors", () => {
    // vhead(1)(ext(0)(true)(vnil)) has type Bool
    const tm = App(
      App(Ref("vhead"), App(Ref("succ"), Ref("zero"))),
      App(App(App(Ref("ext"), Ref("zero")), Ref("true")), Ref("vnil"))
    );

    check(
      defs([
        nat,
        zero,
        succ,
        vect,
        vnil,
        ext,
        bool,
        tru,
        fls,
        unit,
        unt,
        vhead,
      ]),
      adts(),
      [],
      tm,
      Ref("Bool"),
      0
    );
  });

  test("vhead rejects non-empty Vectors", () => {
    // vhead(0)(vnil) has type Unit
    const tm = App(App(Ref("vhead"), Ref("zero")), Ref("vnil"));

    check(
      defs([
        nat,
        zero,
        succ,
        vect,
        vnil,
        ext,
        bool,
        tru,
        fls,
        unit,
        unt,
        vhead,
      ]),
      adts(),
      [],
      tm,
      Ref("Unit"),
      0,
      0
    );
  });
});

describe("type equality", () => {
  const id = Def("id", Ann(Abs("x", Var("x", 0)), Pi("", Ref("X"), Ref("X"))));

  const Nat: Term = Ref("Nat");
  const Bool: Term = Ref("Bool");

  // The identity type operator λX.X: when applied to any type it gives back
  // the argument.
  const Id: Term = Abs("A", Var("A", 0));

  const ds = defs([
    Def("Nat", Ann(id.term, Star())),
    Def("Bool", Ann(id.term, Star())),
    Def("Unit", Ann(id.term, Star())),
  ]);

  // The type Nat→Bool.
  const NatToBool: Term = Pi("", Nat, Bool);

  const eq = (a: Term, b: Term) => equate([], ds, a, b, Ref("unused"));

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

  // n(λP ★)(Unit)(λv Bool) == (λn λx n(λP ★)(Unit)(λn Bool))(n)(xs)
  test("AbsApp terms are fully reduced", () => {
    const lhs = App(
      App(App(Var("n", 1), Abs("P", Star())), Ref("Unit")),
      Abs("v", Ref("Bool"))
    );
    const rhs = App(
      App(
        Abs(
          "n",
          Abs(
            "x",
            App(
              App(App(Var("n", 1), Abs("P", Star())), Ref("Unit")),
              Abs("n", Ref("Bool"))
            )
          )
        ),
        Var("n", 1)
      ),
      Var("xs", 0)
    );
    expect(eq(lhs, rhs).eq).toBeTruthy();
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
  const id = Def("id", Ann(Abs("x", Var("x", 0)), Pi("", Ref("X"), Ref("X"))));

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
