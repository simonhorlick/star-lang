import { describe, expect, test } from "vitest";
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
  tru,
} from "./test_defs";
import { Abs, App, Pi, Ref, Self, Star, Var } from "./ast";

describe("adts", () => {
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
  test("term for Nat is generated correctly", () => {
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

  test("should generate term for Vector", () => {
    // type List(A *) = nil | cons(head A, tail List(A))
    // made explicit:
    // type List(A *) =
    //   | nil : Vector(A)
    //   | cons(head A, tail List(A)) : Vector(A)
    //
    // List : ΠA:★ ★
    //      = λA ιt
    //        ΠP:(List(A)→*)
    //        Πcnil:P(nil(A))
    //        Πccons:(Πhead:A Πtail:List(A) P(cons(A)(head)(tail)))
    //        P(t)
    //
    // type Vector(T ★, n Nat) =
    //   | vnil : Vector(T, 0)
    //   | ext(head T, tail Vector(T, n)) : Vector(T, succ(n))
    //
    // VectBool : Πsz:Nat ★
    //          = λsz ιt
    //            ΠP:(Πn:Nat Πx:Vect(n) ★)
    //            Πcnil:P(zero)(vnil)
    //            Πcext:(Πn:Nat Πhead:Bool Πtail:Vect(n) P(succ(n))(ext(n)(head)(tail))
    //            P(sz)(t)

    // In List, A is static (i.e. not passed to P), but for Vector we have
    // different sz for each branch.

    // const list = buildType(Identifier("List"), listParams, listConstructors);

    // const nil = Def(
    //   "nil",
    //   Ann(
    //     GenerateConstructorTerm(listParams, listConstructors, 0),
    //     GenerateConstructorType("List", listParams, listConstructors[0])
    //   )
    // );

    // const cons = Def(
    //   "cons",
    //   Ann(
    //     GenerateConstructorTerm(listParams, listConstructors, 1),
    //     GenerateConstructorType("List", listParams, listConstructors[1])
    //   )
    // );

    expect(true).toBe(false);
  });
});
