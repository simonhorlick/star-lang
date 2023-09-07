import { describe, expect, test } from "@jest/globals";
import { Ref, Var } from "./ast";
import * as Erased from "./erased";
import { reduce, reduceOnce3, termShift2, termSubst2 } from "./evaluation";

// tru = λt. λf. t
const tru = Erased.Def(
  "tru",
  Erased.Abs("t", Erased.Abs("f", Erased.Var("t", 1)))
);

// fls = λt. λf. f
const fls = Erased.Def(
  "fls",
  Erased.Abs("t", Erased.Abs("f", Erased.Var("f", 0)))
);

// test = λl. λm. λn. (l(m))(n)
// test = λ2. λ1. λ0. (2(1))(0)
const testfn = Erased.Def(
  "test",
  Erased.Abs(
    "l",
    Erased.Abs(
      "m",
      Erased.Abs(
        "n",
        Erased.App(
          Erased.App(Erased.Var("l", 2), Erased.Var("m", 1)),
          Erased.Var("n", 0)
        )
      )
    )
  )
);

// λs. λz. z
// const zero = Abs("s", Abs("z", Var("z", 0)));

// λs. λz. s z
const one = Erased.Abs(
  "s",
  Erased.Abs("z", Erased.App(Erased.Var("s", 1), Erased.Var("z", 0)))
);

// λs. λz. s (s z)
const two = Erased.Abs(
  "s",
  Erased.Abs(
    "z",
    Erased.App(
      Erased.Var("s", 1),
      Erased.App(Erased.Var("s", 1), Erased.Var("z", 0))
    )
  )
);

// λx. x
const id = Erased.Def("id", Erased.Abs("x", Erased.Var("x", 0)));

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
  //   const expected = Erased.Abs("x", Erased.Var("x", 0));
  //   expect(actual).toStrictEqual(expected);
  // });
});

describe("shifting", () => {
  test("ensure we only shift free variables", () => {
    // we need to shift the 2, but not the 0 or the 1, as 2 is free in this
    // expression.

    // λ.λ.1(0(2)) shifted up by 2 is:
    // λ.λ.1(0(4))
    let term = Erased.Abs(
      "x",
      Erased.Abs(
        "y",
        Erased.App(
          Erased.Var("x", 1),
          Erased.App(Erased.Var("y", 0), Erased.Var("z", 2))
        )
      )
    );
    let actual = termShift2(2, term);
    let expected = Erased.Abs(
      "x",
      Erased.Abs(
        "y",
        Erased.App(
          Erased.Var("x", 1),
          Erased.App(Erased.Var("y", 0), Erased.Var("z", 4))
        )
      )
    );
    expect(actual).toStrictEqual(expected);
  });

  test("ensure we only shift free variables", () => {
    // note left association of app in the following syntax:
    // λ.01(λ.012) shifted up by 2 is:
    // λ.03(λ.014)
    let term = Erased.Abs(
      "",
      Erased.App(
        Erased.App(Erased.Var("", 0), Erased.Var("", 1)),
        Erased.Abs(
          "",
          Erased.App(
            Erased.App(Erased.Var("", 0), Erased.Var("", 1)),
            Erased.Var("", 2)
          )
        )
      )
    );
    let actual = termShift2(2, term);
    let expected = Erased.Abs(
      "",
      Erased.App(
        Erased.App(Erased.Var("", 0), Erased.Var("", 3)),
        Erased.Abs(
          "",
          Erased.App(
            Erased.App(Erased.Var("", 0), Erased.Var("", 1)),
            Erased.Var("", 4)
          )
        )
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
    let term = Erased.Var("x", 1);
    let actual = termSubst2(1, Erased.Var("s", 2), term);
    let expected = Erased.Var("s", 2);
    expect(actual).toStrictEqual(expected);
  });

  test("[x/s]y = y", () => {
    let term = Erased.Var("y", 0);
    let actual = termSubst2(1, Erased.Var("s", 2), term);
    let expected = Erased.Var("y", 0);
    expect(actual).toStrictEqual(expected);
  });

  test("[b/a](λb. b a)", () => {
    // [b/a](λb. b a)
    // [0/1](λ. 0 2)
    // λ. 0 2 i.e. λb. b a, this is the same, nothing has been substituted.
    let term = Erased.Abs(
      "b",
      Erased.App(Erased.Var("b", 0), Erased.Var("a", 2))
    );
    let actual = termSubst2(0, Var("", 1), term);
    let expected = Erased.Abs(
      "b",
      Erased.App(Erased.Var("b", 0), Erased.Var("a", 2))
    );
    expect(actual).toStrictEqual(expected);
  });

  test("[b/a](b (λx.λy.b))", () => {
    // replace occurances of b with a:
    // [b/a](b (λx.λy.b))
    // (a (λx.λy.a))
    // in debruijin form b=0,a=1:
    // [0/1](0 (λ.λ.2))
    // 1 (λ.λ.3)
    let term = Erased.App(
      Erased.Var("", 0),
      Erased.Abs("", Erased.Abs("", Erased.Var("", 2)))
    );
    let actual = termSubst2(0, Erased.Var("", 1), term);
    let expected = Erased.App(
      Erased.Var("", 1),
      Erased.Abs("", Erased.Abs("", Erased.Var("", 3)))
    );
    expect(actual).toStrictEqual(expected);
  });
});

// describe("runtime evaluation", () => {
//   test("only evaluate runtime functions if the arguments are values", () => {
//     // println("hello") -  is ok
//     // λx println(x) - cannot be reduced
//     const not = Erased.Abs(
//       "x",
//       Erased.App(
//         Erased.App(Erased.Var("b", 0), Erased.Ref("fls")),
//         Erased.Ref("tru")
//       )
//     );
//     const expected: Erased.Term = Erased.Ref("tru");

//     const actual = reduceOnce3([tru, fls], Erased.App(not, Erased.Ref("fls")));
//     console.log(actual);

//     expect(actual).toStrictEqual(expected);
//   });
// });

// describe("evaluation", () => {
//   // (λx. x)(λz. z) -> (λz. z)
//   test("TestReduceIdentity", () => {
//     const identity = Erased.App(
//       Erased.Abs("x", Erased.Var("x", 0)),
//       Erased.Abs("z", Erased.Var("z", 0))
//     );
//     const expected: Erased.Term = Erased.Abs("z", Erased.Var("z", 0));

//     const actual = reduce([], identity);

//     expect(actual).toStrictEqual(expected);
//   });

//   // Test that substituting top level functions works properly.
//   test("TestSubstituteDef", () => {
//     const expected = Erased.Abs("z", Erased.Var("z", 0));
//     const actual = reduce(
//       [id],
//       Erased.App(Ref("id"), Erased.Abs("z", Erased.Var("z", 0)))
//     );
//     expect(actual).toStrictEqual(expected);
//   });

//   // "if" reduction
//   //
//   // top level defs (after typecheck has passed):
//   //
//   // tru = λt. λf. t
//   // fls = λt. λf. f
//   // test = λl. λm. λn. (l(m))(n)
//   //
//   // ((test(tru))(v))(w)
//   // ------------------- def "test"
//   // (((λl. λm. λn. (l(m))(n))(tru))(v))(w)
//   // -------------------------------------- E-AppAbs
//   // ((λm. λn. (tru(m))(n))(v))(w)
//   // ----------------------------- E-AppAbs
//   // (λn. (tru(v))(n))(w)
//   // -------------------- E-AppAbs
//   // (tru(v))(w)
//   // ----------- def "tru"
//   // ((λt. λf. t)(v))(w)
//   // ------------------- E-AppAbs
//   // (λf. v)(w)
//   // ---------- E-AppAbs
//   // v
//   test("TestReduceIfElse", () => {
//     // ((test(tru))(1))(2)
//     const ifElse: Erased.Term = Erased.App(
//       Erased.App(Erased.App(Erased.Ref("test"), Erased.Ref("tru")), one),
//       two
//     );
//     const expected = one;
//     const actual = reduce([tru, fls, testfn], ifElse);

//     expect(actual).toStrictEqual(expected);
//   });

//   test("should ensure redex uses up bound variable", () => {
//     // Γ = [z→2, y→1]
//     // (λx. y(x)(z))(λx. x)
//     // y(λx. x)(z)
//     // This corresponds to the nameless representation:
//     // (λx. 1(0)(2))(λx. 0)
//     // After one step of evaluation, then indices for y and z are reduced by 1
//     // as the x binder has now been used up.
//     // 0(λx. 0)(1)

//     let src = Erased.App(
//       Erased.Abs(
//         "x",
//         Erased.App(
//           Erased.App(Erased.Var("y", 1), Erased.Var("x", 0)),
//           Erased.Var("z", 2)
//         )
//       ),
//       Erased.Abs("x", Erased.Var("x", 0))
//     );

//     let expected = Erased.App(
//       Erased.App(Erased.Var("y", 0), Erased.Abs("x", Erased.Var("x", 0))),
//       Erased.Var("z", 1)
//     );

//     const actual = reduceOnce2([], src);

//     expect(actual).toStrictEqual(expected);
//   });
// });
