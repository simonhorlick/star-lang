import { describe, expect, test } from "@jest/globals";

import { Abs, TAbs, App, Def, Ref, Var } from "./evaluation";
import { pretty, prettyT } from "./pretty";

describe("pretty", () => {
  // tru = λt. λf. t
  const tru = Def("tru", Abs("t", Abs("f", Ref("t"))));

  // fls = λt. λf. f
  const fls = Def("fls", Abs("t", Abs("f", Ref("f"))));

  // test = λl. λm. λn. (l(m))(n)
  const testFn = Def(
    "test",
    Abs("l", Abs("m", Abs("n", App(App(Ref("l"), Ref("m")), Ref("n")))))
  );

  // fst: Nat = λn:Nat. λm:Nat. n
  const fst = Def("fst", Abs("n", Abs("m", Ref("n"), Ref("Nat")), Ref("Nat")));

  const id = App(Abs("x", Ref("x")), Ref("y"));

  test("", () => expect(pretty(tru.term)).toBe("λt. λf. t"));
  test("", () => expect(pretty(fls.term)).toBe("λt. λf. f"));
  test("", () => expect(pretty(testFn.term)).toBe("λl. λm. λn. l(m)(n)"));
  test("", () => expect(pretty(fst.term)).toBe("λn:Nat. λm:Nat. n"));
  test("", () => expect(pretty(id)).toBe("(λx. x)(y)"));
  test("", () =>
    expect(pretty(App(Abs("x", Var("x", 0)), Abs("z", Var("z", 0))))).toBe(
      "(λx. 0)(λz. 0)"
    ));
  test("", () =>
    expect(
      pretty(Abs("s", Abs("z", App(Var("s", 1, 2), Var("z", 0, 2)))))
    ).toBe("λs. λz. 1(0)"));
  test("", () =>
    expect(
      pretty(
        Abs(
          "s",
          Abs("z", App(Var("s", 1, 2), App(Var("s", 1, 2), Var("z", 0, 2))))
        )
      )
    ).toBe("λs. λz. 1(1(0))"));
  test("type abstraction", () =>
    expect(
      pretty(App(TAbs("X", Abs("x", Var("x", 0), Var("X", 1))), Ref("Y")))
    ).toBe("(ΛX. λx:1. 0)(Y)"));
});
