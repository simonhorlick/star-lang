import { describe, expect, test } from "@jest/globals";
import { Def as DefT, Term, transformDebruijin } from "./ast";
import {
  Abs,
  App,
  Def,
  isValue,
  reduceOnce,
  Ref,
  All,
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
const zero = Abs("s", Abs("z", Var("z", 0, 2)));

// λs. λz. s z
const one = Abs("s", Abs("z", App(Var("s", 1, 2), Var("z", 0, 2))));

// λs. λz. s (s z)
const two = Abs(
  "s",
  Abs("z", App(Var("s", 1, 2), App(Var("s", 1, 2), Var("z", 0, 2))))
);

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
    const expected: Term = Abs("x", Var("t", 1, 2));

    const actual = transformDebruijin(Abs("x", Ref("t")), [
      { type: "bind", name: "t", typ: { type: "ers" } },
    ]);

    expect(actual).toStrictEqual(expected);
  });

  test("TestComputeDebruijinIndicesIdApp", () => {
    // (λx. x)(λz. z)
    // (λ. 0)(λ. 0)
    const expected: Term = App(
      Abs("x", Var("x", 0, 1)),
      Abs("z", Var("z", 0, 1))
    );
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
    const expected = Abs("z", Var("z", 0, 1));
    const actual = reduce([id], App(Ref("id"), Abs("z", Var("z", 0, 1))));
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
      Abs("x", App(App(Var("y", 1, 3), Var("x", 0, 3)), Var("z", 2, 3))),
      Abs("x", Var("x", 0, 3))
    );

    let expected = App(
      App(Var("y", 0, 2), Abs("x", Var("x", 0, 3))),
      Var("z", 1, 2)
    );

    const actual = reduceOnce([], src);

    expect(actual).toStrictEqual(expected);
  });

  test("should evaluate polymorphic identity function app", () => {
    // (λX. λx:X. x)(Y)
    // λx:Y. x
    const program = App(All("X", Abs("x", Var("x", 0), Var("X", 1))), Ref("Y"));

    const actual = reduceOnce([], program);
    const expected = Abs("x", Var("x", 0), Ref("Y"));

    expect(actual).toStrictEqual(expected);
  });
});
