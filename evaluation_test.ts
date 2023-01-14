import { describe, expect, test } from "@jest/globals";
import { Context, Def as DefT, getDeBruijinIndex, Term, Type } from "./ast";
import { addTermToCtx, addTypeToCtx } from "./check";
import {
  Abs,
  All,
  Ann,
  App,
  Arrow,
  Def,
  isValue,
  reduceOnce,
  Ref,
  Star,
  TAbs,
  TApp,
  termShift,
  termSubst,
  termSubstTop,
  TTAbs,
  TTApp,
  typeSubst,
  tytermSubst,
  Var,
} from "./evaluation";
import { pretty } from "./pretty";

function reduce(defs: DefT[], t: Term): Term {
  let prevTerm = "";
  while (true) {
    let printTerm = pretty(t);
    console.log(printTerm);

    if (prevTerm == printTerm) {
      throw "term was not reduced";
    }

    if (isValue(t)) {
      break;
    }

    t = reduceOnce(defs, t);
    prevTerm = printTerm;
  }

  return t;
}

export function transformDebruijin(term: Term, ctx: Context = []): Term {
  switch (term._) {
    case "app":
      return App(
        transformDebruijin(term.left, ctx),
        transformDebruijin(term.right, ctx)
      );
    case "lam": {
      const newCtx = addTermToCtx(ctx, term.name, term.bindType);
      return Abs(
        term.name,
        transformDebruijin(term.body, newCtx),
        term.bindType
      );
    }
    case "tabs": {
      const newCtx = addTypeToCtx(ctx, term.name, term.kind);
      return TAbs(term.name, transformDebruijin(term.body, newCtx), term.kind);
    }
    case "var":
      return term;
    case "ann":
      return Ann(transformDebruijin(term.term, ctx), term.typ);
    case "ref":
      // If this name exists in the context then compute its index. If it
      // doesn't exist, leave it as a ref.
      if (ctx.some((x) => x.name == term.name)) {
        return Var(term.name, getDeBruijinIndex(ctx, term.name));
      } else {
        return term;
      }
    case "tapp":
      return TApp(
        transformDebruijin(term.left, ctx),
        transformDebruijinT(term.right, ctx)
      );
  }
}

export function transformDebruijinT(term: Type, ctx: Context = []): Type {
  switch (term._) {
    case "all":
      return All(term.name, transformDebruijinT(term.to), term.kind);
    case "arrow":
      return Arrow(
        transformDebruijinT(term.from),
        transformDebruijinT(term.to)
      );
    case "ers":
      return term;
    case "var":
      return term;
    case "ref":
      // If this name exists in the context then compute its index. If it
      // doesn't exist, leave it as a ref.
      if (ctx.some((x) => x.name == term.name)) {
        return Var(term.name, getDeBruijinIndex(ctx, term.name));
      } else {
        return term;
      }
    case "ttabs":
      const newCtx = addTypeToCtx(ctx, term.name, term.kind);
      return TTAbs(
        term.name,
        transformDebruijinT(term.body, newCtx),
        term.kind
      );
    case "ttapp":
      return TTApp(
        transformDebruijinT(term.left, ctx),
        transformDebruijinT(term.right, ctx)
      );
  }
}

// tru = λt. λf. t
const tru: DefT = Def("tru", transformDebruijin(Abs("t", Abs("f", Ref("t")))));

// fls = λt. λf. f
const fls: DefT = Def("fls", transformDebruijin(Abs("t", Abs("f", Ref("f")))));

// test = λl. λm. λn. (l(m))(n)
const testfn = Def(
  "test",
  transformDebruijin(
    Abs("l", Abs("m", Abs("n", App(App(Ref("l"), Ref("m")), Ref("n")))))
  )
);

// λs. λz. z
const zero = Abs("s", Abs("z", Var("z", 0)));

// λs. λz. s z
const one = Abs("s", Abs("z", App(Var("s", 1), Var("z", 0))));

// λs. λz. s (s z)
const two = Abs("s", Abs("z", App(Var("s", 1), App(Var("s", 1), Var("z", 0)))));

// λx. x
const id = Def("id", transformDebruijin(Abs("x", Ref("x"))));

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

describe("debruijin", () => {
  test("TestComputeDebruijinIndicesSingleBinder", () => {
    // Γ = [t]; λx.t
    // λ.1
    const expected: Term = Abs("x", Var("t", 1));

    const actual = transformDebruijin(Abs("x", Ref("t")), [
      { type: "bind", name: "t", typ: { _: "ers" } },
    ]);

    expect(actual).toStrictEqual(expected);
  });

  test("TestComputeDebruijinIndicesIdApp", () => {
    // (λx. x)(λz. z)
    // (λ. 0)(λ. 0)
    const expected: Term = App(Abs("x", Var("x", 0)), Abs("z", Var("z", 0)));
    const actual = transformDebruijin(
      App(Abs("x", Ref("x")), Abs("z", Ref("z")))
    );

    expect(actual).toStrictEqual(expected);
  });

  test("TestComputeDebruijinIndicesChurchNat", () => {
    // λs. λz. s (s z)
    // λ. λ. 1 (1 0)
    const expected = two;

    const actual = transformDebruijin(
      Abs("s", Abs("z", App(Ref("s"), App(Ref("s"), Ref("z")))))
    );

    expect(actual).toStrictEqual(expected);
  });
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
    let actual = termShift(2, term);
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
    let actual = termShift(2, term);
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
    let actual = termSubst(1, Var("s", 2), term);
    let expected = Var("s", 2);
    expect(actual).toStrictEqual(expected);
  });

  test("[x/s]y = y", () => {
    let term = Var("y", 0);
    let actual = termSubst(1, Var("s", 2), term);
    let expected = Var("y", 0);
    expect(actual).toStrictEqual(expected);
  });

  test("[b/a](λb. b a)", () => {
    // [b/a](λb. b a)
    // [0/1](λ. 0 2)
    // λ. 0 2 i.e. λb. b a, this is the same, nothing has been substituted.
    let term = Abs("b", App(Var("b", 0), Var("a", 2)));
    let actual = termSubst(0, Var("", 1), term);
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
    let actual = termSubst(0, Var("", 1), term);
    let expected = App(Var("", 1), Abs("", Abs("", Var("", 3))));
    expect(actual).toStrictEqual(expected);
  });

  test("[X/Nat](λx:X.x)", () => {
    // [X/Nat](λx:X.x)
    // λx:Nat.x
    let term = Abs("x", Var("x", 0), Var("X", 1));
    let actual = tytermSubst(Var("Nat", 5), 0, term);
    let expected = Abs("x", Var("x", 0), Var("Nat", 6));
    expect(actual).toStrictEqual(expected);
  });
});

describe("evaluation", () => {
  // (λx. x)(λz. z) -> (λz. z)
  test("TestReduceIdentity", () => {
    const identity = transformDebruijin(
      App(Abs("x", Ref("x")), Abs("z", Ref("z")))
    );

    const expected: Term = transformDebruijin(Abs("z", Ref("z")));

    const actual = reduce([], identity);

    expect(actual).toStrictEqual(expected);
  });

  // Test that substituting top level functions works properly.
  test("TestSubstituteDef", () => {
    const expected = Abs("z", Var("z", 0));
    const actual = reduce([id], App(Ref("id"), Abs("z", Var("z", 0))));
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
    const ifElse: Term = transformDebruijin(
      App(App(App(Ref("test"), Ref("tru")), one), two)
    );

    const expected = one;
    const actual = reduce([tru, fls, testfn], ifElse);

    expect(actual).toStrictEqual(expected);
  });

  test("should ensure redex uses up bound variable", () => {
    // Γ = [z→2, y→1]
    // (λx. y(x)(z))(λx. x)
    // y(λx. x)(z)
    // This corresponds to the nameless representation:
    // (λx. 1(0)(2))(λx. 0)
    // After one step of evaluation, then indices for y and z are reduced by 1
    // as the x binder has now been used up.
    // 0(λx. 0)(1)

    let src = App(
      Abs("x", App(App(Var("y", 1), Var("x", 0)), Var("z", 2))),
      Abs("x", Var("x", 0))
    );

    let expected = App(App(Var("y", 0), Abs("x", Var("x", 0))), Var("z", 1));

    const actual = reduceOnce([], src);

    expect(actual).toStrictEqual(expected);
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
});
