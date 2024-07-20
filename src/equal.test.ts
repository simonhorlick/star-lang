import { describe, expect, test } from "vitest";
import { reduce } from "./equal";
import {
  Def,
  Key,
  Origin,
  Syntax,
  Term,
  Abs,
  Ann,
  App,
  Pi,
  Ref,
  Var,
} from "./ast";
import { defs } from "./typecheck";

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

  test("should remove syn nodes", () => {
    expect(
      reduce(
        false,
        [],
        defs(),
        Syntax(Origin(0, 0, Key("key")), Abs("x", Var("x", 0)))
      )
    ).toStrictEqual(Abs("x", Var("x", 0)));
  });
});
