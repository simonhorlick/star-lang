import { describe, expect, test } from "@jest/globals";

import { Abs, TAbs, App, Def, Ref, Var, TApp, Star } from "./evaluation";
import { pretty, prettyC, prettyT } from "./pretty";
import * as Erased from "./erased";

describe("pretty", () => {
  // tru = λt. λf. t
  const tru = Erased.Def(
    "tru",
    Erased.Abs("t", Erased.Abs("f", Erased.Ref("t")))
  );

  // fls = λt. λf. f
  const fls = Erased.Def(
    "fls",
    Erased.Abs("t", Erased.Abs("f", Erased.Ref("f")))
  );

  // test = λl. λm. λn. (l(m))(n)
  const testFn = Erased.Def(
    "test",
    Erased.Abs(
      "l",
      Erased.Abs(
        "m",
        Erased.Abs(
          "n",
          Erased.App(
            Erased.App(Erased.Ref("l"), Erased.Ref("m")),
            Erased.Ref("n")
          )
        )
      )
    )
  );

  // fst: Nat = λn:Nat. λm:Nat. n
  const fst = Def(
    "fst",
    Abs("n", Abs("m", Ref("n"), Ref("Nat")), Ref("Nat")),
    Ref("Nat")
  );

  const id = Erased.App(Erased.Abs("x", Erased.Ref("x")), Erased.Ref("y"));

  test("λt. λf. t", () => expect(prettyC(tru.term)).toBe("λt. λf. t"));
  test("λt. λf. f", () => expect(prettyC(fls.term)).toBe("λt. λf. f"));
  test("λl. λm. λn. l(m)(n)", () =>
    expect(prettyC(testFn.term)).toBe("λl. λm. λn. l(m)(n)"));
  test("λn:Nat. λm:Nat. n", () =>
    expect(pretty(fst.term)).toBe("λn:Nat. λm:Nat. n"));
  test("(λx. x)(y)", () => expect(prettyC(id)).toBe("(λx. x)(y)"));
  test("(λx. 0)(λz. 0)", () =>
    expect(
      prettyC(
        Erased.App(
          Erased.Abs("x", Erased.Var("x", 0)),
          Erased.Abs("z", Erased.Var("z", 0))
        )
      )
    ).toBe("(λx. 0)(λz. 0)"));
  test("λs. λz. 1(0)", () =>
    expect(
      prettyC(
        Erased.Abs(
          "s",
          Erased.Abs("z", Erased.App(Erased.Var("s", 1), Erased.Var("z", 0)))
        )
      )
    ).toBe("λs. λz. 1(0)"));
  test("λs. λz. 1(1(0))", () =>
    expect(
      prettyC(
        Erased.Abs(
          "s",
          Erased.Abs(
            "z",
            Erased.App(
              Erased.Var("s", 1),
              Erased.App(Var("s", 1), Erased.Var("z", 0))
            )
          )
        )
      )
    ).toBe("λs. λz. 1(1(0))"));
  test("type abstraction", () =>
    expect(
      pretty(
        TApp(TAbs("X", Abs("x", Var("x", 0), Var("X", 1)), Star()), Ref("Y"))
      )
    ).toBe("(ΛX. λx:1. 0)(Y)"));
});
