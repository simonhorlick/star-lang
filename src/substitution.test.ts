import { describe, expect, test } from "vitest";
import { shift, subst } from "./substitution";
import { Abs, App, Pi, Var } from "./ast";

describe("shifting", () => {
  test("type shift increments free variables", () => {
    // Both X and Y are free type variables.
    const type = Pi("", Var("X", 0), Var("Y", 1));
    expect(shift(1, 0, type)).toStrictEqual(Pi("", Var("X", 1), Var("Y", 2)));
  });

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
