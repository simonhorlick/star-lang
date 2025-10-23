import { describe, expect, test } from "vitest";
import {
  Branch,
  Case,
  Hole,
  Identifier,
  Let,
  Origin,
  Abs,
  Ann,
  App,
  Pi,
  Ref,
  Star,
  Var,
  CTerm,
} from "./sugar";
import { ADT, Constructor, Def2 as Def, definition, stripAST } from "./ast";
import {
  check,
  equate,
  infer,
  TypecheckError,
  defs,
  adts,
  desugarCaseStatement,
} from "./typecheck";
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
  unit,
  unt,
  listADT,
  boolADT,
} from "./test_defs";
import {
  and,
  conj,
  proj1,
  proj2,
  andCommutes,
  vect,
  vnil,
  ext,
} from "./test_defs2";
import { reduce } from "./equal";
import { Context } from "./context";
import { desugar } from "./adts";
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

const ensureSuccess = (d: Def) => {
  const ct = (t: CTerm): void => {
    switch (t._) {
      case "app":
        ct(t.func);
        ct(t.arg);
        break;
      case "lam":
        ct(t.name);
        ct(t.body);
        break;
      case "ann":
        ct(t.term);
        ct(t.type);
        break;
      case "case":
        ct(t.name);
        t.branches.forEach((b) => {
          ct(b.constructor);
          ct(b.term);
        });
        break;
      case "let":
        ct(t.name);
        ct(t.expr);
        ct(t.body);
        break;
      case "orig":
        ct(t.child);
        break;
      case "syn":
        ct(t.child);
        break;
      case "pi":
        ct(t.from);
        ct(t.body);
        break;
      case "label":
        ct(t.child);
        break;
      case "self":
        ct(t.body);
        break;

      // Leaf terms
      case "id":
      case "key":
      case "int":
      case "hole":
      case "star":
      case "str":
      case "var":
      case "ref":
        break;
      case "err":
        throw new Error("unexpected error node in checkTree: " + t.msg);

      default:
        throw new Error(`unexpected term in checkTree`);
    }
  };
  ct(d.term);
  return d;
};

const pdef = (s: string): Def =>
  ensureSuccess(desugar(stripAST(result(definition(ts(s)))) as Def));

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
        defs([
          Def("A", Ann(Abs("x", Var("x", 0)), Star()), undefined, undefined),
        ]),
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
          Def("A", Ann(Abs("x", Var("x", 0)), Star()), undefined, undefined),
          Def("B", Ann(Abs("x", Var("x", 0)), Star()), undefined, undefined),
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
          Def("A", Ann(Abs("x", Var("x", 0)), Star()), undefined, undefined),
          // B:★
          Def("B", Ann(Abs("x", Var("x", 0)), Star()), undefined, undefined),
          // f:A->B
          Def(
            "f",
            Ann(Abs("a", Abs("x", Var("x", 0))), Pi("", Ref("A"), Ref("B"))),
            undefined,
            undefined
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
            Def(
              "A",
              Ann(Abs("x", Abs("y", Var("y", 0))), Star()),
              undefined,
              undefined
            ),
            Def(
              "B",
              Ann(Abs("x", Abs("y", Var("x", 1))), Star()),
              undefined,
              undefined
            ),
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
          Def("A", Ann(Abs("x", Var("x", 0)), Star()), undefined, undefined),
          Def("B", Ann(Abs("x", Var("x", 0)), Star()), undefined, undefined),
        ]),
        adts(),
        ctx,
        Ann(Var("a", 0), Ref("A")),
        Ref("A")
      );
    });

    test("should error when reference type doesn't match expected type", () => {
      const definitions = defs([
        bool,
        nat,
        Def(
          "id",
          Ann(Abs("z", Var("z", 0)), Ref("Bool")),
          undefined,
          undefined
        ),
      ]);

      // check id:Nat - it should fail
      expect(() =>
        check(definitions, adts(), [], Ref("id"), Ref("Nat"))
      ).toThrow();
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
      defs([
        Def(
          "T",
          Ann(Abs("x", Var("x", 0)), Pi("", Ref("X"), Ref("X"))),
          undefined,
          undefined
        ),
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
    );
  });

  test("should check type-level and function", () =>
    check(defs(), adts(), [], and.term.term, and.term.type));

  test("should check type-level conjunction function", () =>
    check(defs([and]), adts(), [], conj.term.term, conj.term.type));

  test("proj1 checks", () =>
    check(defs([and]), adts(), [], proj1.term.term, proj1.term.type));

  test("proj2 checks", () => {
    check(defs([and]), adts(), [], proj2.term.term, proj2.term.type);
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
      andCommutes.term.type
    ));

  test("true is a bool", () =>
    check(defs([tru, fls, bool]), adts(), [], tru.term.term, bool.term));

  test("false is a bool", () =>
    check(defs([tru, fls, bool]), adts(), [], fls.term.term, bool.term));

  test("Bool is a type", () =>
    check(defs([tru, fls, bool]), adts(), [], bool.term.term, Star()));

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
    expect(pretty(reduced)).toBe(pretty(tru.term.term));
  });

  test("null checks", () =>
    check(
      defs([maybe, mnull, just]),
      adts(),
      [],
      mnull.term.term,
      mnull.term.type
    ));

  test("just checks", () =>
    check(
      defs([maybe, mnull, just]),
      adts(),
      [],
      just.term.term,
      just.term.type
    ));

  test("nil checks", () =>
    check(defs([list, nil, cons]), adts([]), [], nil.term.term, nil.term.type));

  test("cons checks", () =>
    check(
      defs([list, nil, cons]),
      adts([]),
      [],
      cons.term.term,
      cons.term.type
    ));

  test("pair checks", () =>
    // ppair is the constructor for the type pair
    check(defs([pair, ppair]), adts([]), [], ppair.term.term, ppair.term.type));

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

  test("let statements should typecheck", () => {
    // the typechecker should infer the expression of the let statement as Bool
    // then with [x:Bool] check that the body of the let statement is of type
    // Bool.
    //
    // func ex:Bool->Bool = λb let x = b in x

    const term = Abs("b", Let(Identifier("x"), Var("b", 0), Var("x", 0)));
    const type = Pi("", Ref("Bool"), Ref("Bool"));
    const actual = check(defs([tru, fls, bool]), adts(), [], term, type, 0);
    expect(pretty(actual.type)).toBe("Bool→Bool");
  });

  test("correct self-type is inferred for Bool((x:Bool) -> ★)", () => {
    // b:Bool, P:((x:Bool) -> ★), t:P(true), f:P(false)];
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

  const not = pdef(`func not:Bool->Bool = λb b(λx Bool,true,false)`);

  // A value of type equal(A)(a)(b) can only be constructed if a == b.
  const equal = pdef(
    `func equal: (A:*) -> (a:A) -> (b:A) -> * = λA λa λb (P:(A->*)) -> (p:P(a)) -> P(b)`
  );
  const refl = pdef(
    `func refl: (A:*) -> (x:A) -> equal(A,x,x) = λA λx λP λp p`
  );
  const nn = pdef(
    `func nn: (b:Bool) -> equal(Bool,not(not(b)),b) = λb b(λx equal(Bool,not(not(x)),x),refl(Bool,false),refl(Bool,true))`
  );

  test("double negation proof", () =>
    // Check that not(not(b)) == b on the type level.
    check(
      defs([bool, tru, fls, not, equal, refl]),
      adts(),
      [],
      nn.term.term,
      nn.term.type
    ));

  // This is eqivalent to nn, but using a case expression rather than the
  // desugared version.
  const nn2 = pdef(
    `func nn: (b:Bool) -> equal(Bool,not(not(b)),b) = λb
  case b of
  | false => refl(Bool,false)
  | true => refl(Bool,true)`
  );

  test("double negation proof using case", () => {
    // Check that not(not(b)) == b on the type level.
    try {
      const x = check(
        defs([bool, tru, fls, not, equal, refl]),
        adts([boolADT]),
        [],
        nn2.term.term,
        nn2.term.type
      );
      console.log(x);
    } catch (e) {
      console.log(e);
      throw e;
    }
  });

  test("should desugar nn case statement", () => {
    // This test ensures that case statements are desugared to the expected
    // terms.

    // λb case b of
    // | false -> refl(Bool,false)
    // | true -> refl(Bool,true)
    const term = Abs(
      "b",
      Case(Var("b", 0), [
        Branch(
          Identifier("false"),
          App(App(Ref("refl"), Ref("Bool")), Ref("false"))
        ),
        Branch(
          Identifier("true"),
          App(App(Ref("refl"), Ref("Bool")), Ref("true"))
        ),
      ])
    );

    // equal(Bool,not(not(b)),b)
    const nnb = App(Ref("not"), App(Ref("not"), Var("b", 0)));
    const typ = Pi(
      "b",
      Ref("Bool"),
      App(App(App(Ref("equal"), Ref("Bool")), nnb), Var("b", 0))
    );

    const ctx: Context = [];
    const result = check(
      defs([bool, tru, fls, not, equal, refl]),
      adts([boolADT]),
      ctx,
      term,
      typ
    );

    expect(pretty(result.term)).toBe(
      "λb b(λ equal(Bool,not(not(b)),b),refl(Bool,false),refl(Bool,true))"
    );
  });

  const reflTrue = pdef(`func rt: equal(Bool,true,true) = refl(Bool,true)`);

  test("reflexivity of true has type equal(Bool,true,true)", () =>
    check(
      defs([bool, tru, fls, not, equal, refl]),
      adts(),
      [],
      reflTrue.term.term,
      reflTrue.term.type
    ));

  test("vnil has type Vect(zero)", () =>
    check(
      defs([nat, zero, succ, vect, vnil, ext, bool, tru, fls]),
      adts(),
      [],
      vnil.term.term,
      vnil.term.type
    ));

  test("ext has type (n:Nat) -> (head:Bool) -> (tail:Vect(n)) -> Vect(succ(n))", () =>
    check(
      defs([nat, zero, succ, vect, vnil, ext, bool, tru, fls]),
      adts(),
      [],
      ext.term.term,
      ext.term.type
    ));

  test("the type of ext(0,true,vnil) is Vect(1)", () => {
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
      // λn λxs xs(...,unit,λn λhead λtail head)
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
                    // n(λP *,Unit,λn Bool)
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
      // (n:Nat) -> (xs:Vect(n)) -> n(λP *,Unit,λv Bool)
      Pi(
        "n",
        Ref("Nat"),
        Pi(
          "xs",
          App(Ref("Vect"), Var("n", 0)),
          // n(λP *,Unit,λv Bool)
          App(
            App(App(Var("n", 1), Abs("P", Star())), Ref("Unit")),
            Abs("v", Ref("Bool"))
          )
        )
      )
    ),
    undefined,
    undefined
  );

  test("vhead has the correct type", () => {
    check(
      defs([nat, zero, succ, vect, vnil, ext, bool, tru, fls, unit, unt]),
      adts(),
      [],
      vhead.term.term,
      vhead.term.type,
      0
    );
  });

  test("vhead allows non-empty Vectors", () => {
    // vhead(1,ext(0,true,vnil)) has type Bool
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
    // vhead(0,vnil) has type Unit
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

  test("should desugar case statement", () => {
    // Desugar the boolean not function:
    //   not = λb case b of true -> false | false -> true
    // should desugar to:
    //   not = λb b(λP Bool,false,true)

    const boolConstructors = [
      { name: Identifier("true"), args: [], typ: null },
      { name: Identifier("false"), args: [], typ: null },
    ];

    const dts = adts([ADT(Identifier("Bool"), [], boolConstructors)]);

    const stmt = Abs(
      "b",
      Case(Var("b", 0), [
        Branch(Identifier("true"), Ref("false")),
        Branch(Identifier("false"), Ref("true")),
      ])
    );
    const stmttyp = Pi("", Ref("Bool"), Ref("Bool"));

    const result = check(defs([bool, tru, fls]), dts, [], stmt, stmttyp);
    expect(pretty(result.term, false, true)).toBe(
      "(λb b((λ Bool):Bool→★,false,true)):Bool→Bool"
    );
  });

  test("should annotate lambdas in desugared case branches", () => {
    const natConstructors: Constructor[] = [
      { name: Identifier("zero"), args: [], typ: null },
      {
        name: Identifier("succ"),
        args: [{ name: "x", type: Ref("Nat") }],
        typ: null,
      },
    ];

    const dts = adts([ADT(Identifier("Nat"), [], natConstructors)]);

    const stmt = Abs(
      "n",
      Case(Var("n", 0), [
        Branch(Identifier("zero"), Ref("zero")),
        Branch(Identifier("succ"), Ref("n.x")),
      ])
    );
    const stmttyp = Pi("", Ref("Nat"), Ref("Nat"));

    const result = check(defs([nat, zero, succ]), dts, [], stmt, stmttyp);
    expect(pretty(result.term, false, true)).toBe(
      "(λn n((λ Nat):Nat→★,zero,(λn.x n.x):Nat→((λ Nat):Nat→★)(succ(n)))):Nat→Nat"
    );
  });

  test("should desugar case statement with bound constructor arguments", () => {
    /*
    type List(A *) = nil | cons(head A, tail List(A))

    type Bool = true | false

    func head:List(Bool)->Bool = λxs
      case xs of
      | nil -> false
      | cons -> xs.head
    */
    const ctx: Context = [
      { type: "bind", name: "xs", typ: App(Ref("List"), Ref("Bool")) },
    ];

    const term = Case(Var("xs", 0), [
      Branch(Identifier("nil"), Ref("false")),
      // Note that xs.head is still a Ref at this point, only after desugaring
      // it turns into a Var.
      Branch(Identifier("cons"), Ref("xs.head")),
    ]);
    const typ = Ref("Bool");

    const actual = desugarCaseStatement(
      defs([bool, list, tru, fls]),
      adts([listADT]),
      ctx,
      term,
      0,
      0,
      typ
    );

    // We expect the case statement to desugar to:
    //   xs(λP Bool,false,λxs.head λxs.tail xs.head)
    const expected = App(
      App(App(Var("xs", 0), Abs("", Ref("Bool"))), Ref("false")),
      Abs("xs.head", Abs("xs.tail", Var("xs.head", 1)))
    );

    expect(pretty(actual.term)).toBe(pretty(expected));
  });
});

describe("type equality", () => {
  const Nat: CTerm = nat.term;
  const Bool: CTerm = bool.term;

  // The identity type operator λX.X: when applied to any type it gives back
  // the argument.
  const Id: CTerm = Abs("A", Var("A", 0));

  const ds = defs([nat, bool, unit]);

  // The type Nat→Bool.
  const NatToBool: CTerm = Pi("", Nat, Bool);

  const eq = (a: CTerm, b: CTerm) => equate([], ds, a, b, Ref("unused"));

  test("Bool→Bool != Bool", () =>
    expect(eq(Pi("", Bool, Bool), Bool).eq).toBe(false));

  test("Bool != Bool→★", () =>
    expect(eq(Bool, Pi("", Bool, Star())).eq).toBe(false));

  test("Bool→★ != Bool", () =>
    expect(eq(Pi("", Bool, Star()), Bool).eq).toBe(false));

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

  test("let equality", () => {
    const one = Abs("s", Abs("z", App(Var("s", 1), Var("z", 0))));

    // let x = one in x
    const x = Let(Identifier("x"), one, Var("x", 0));
    // let z = one in z
    const z = Let(Identifier("z"), one, Var("z", 0));

    expect(eq(x, z).eq).toBe(true);
  });

  // n(λP ★,Unit,λv Bool) == (λn λx n(λP ★,Unit,λn Bool),n,xs)
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

  test("equate should ignore origins for non ⍺-eq terms", () => {
    const t1 = Origin(0, 1, Origin(0, 1, Hole(1)));
    const t2 = Origin(0, 1, Origin(0, 1, Origin(0, 1, Hole(2))));
    const e = equate([], defs(), t1, t2, Ref("y"));
    expect(e.eq).toBeTruthy();
  });
});
