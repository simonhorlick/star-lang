import { Abs, Ann, App, Def, Identifier, Par, Pi, Ref, Star, Var } from "./ast";
import {
  GenerateConstructorTerm,
  GenerateConstructorType,
  buildType,
} from "./process";

const boolConstructors = [
  { name: Identifier("false"), args: [] },
  { name: Identifier("true"), args: [] },
];

export const bool = buildType(Identifier("Bool"), [], boolConstructors);

export const fls = Def(
  "false",
  Ann(
    GenerateConstructorTerm([], boolConstructors, 0),
    GenerateConstructorType("Bool", [], boolConstructors[0])
  )
);

export const tru = Def(
  "true",
  Ann(
    GenerateConstructorTerm([], boolConstructors, 1),
    GenerateConstructorType("Bool", [], boolConstructors[1])
  )
);

const unitConstructors = [{ name: Identifier("unit"), args: [] }];

export const unit = buildType(Identifier("Unit"), [], unitConstructors);

export const unt = Def(
  "unit",
  Ann(
    GenerateConstructorTerm([], unitConstructors, 0),
    GenerateConstructorType("Unit", [], unitConstructors[0])
  )
);

const natConstructors = [
  { name: Identifier("zero"), args: [] },
  { name: Identifier("succ"), args: [{ name: "n", type: Ref("Nat") }] },
];

export const nat = buildType(Identifier("Nat"), [], natConstructors);

export const zero = Def(
  "zero",
  Ann(
    GenerateConstructorTerm([], natConstructors, 0),
    GenerateConstructorType("Nat", [], natConstructors[0])
  )
);

export const succ = Def(
  "succ",
  Ann(
    GenerateConstructorTerm([], natConstructors, 1),
    GenerateConstructorType("Nat", [], natConstructors[1])
  )
);

const listParams = [{ name: "A", type: Star() }];

const listConstructors = [
  { name: Identifier("nil"), args: [] },
  {
    name: Identifier("cons"),
    args: [
      {
        name: "head",
        type: Par("A"),
      },
      {
        name: "tail",
        type: App(Ref("List"), Par("A")),
      },
    ],
  },
];

export const list = buildType(Identifier("List"), listParams, listConstructors);

export const nil = Def(
  "nil",
  Ann(
    GenerateConstructorTerm(listParams, listConstructors, 0),
    GenerateConstructorType("List", listParams, listConstructors[0])
  )
);

export const cons = Def(
  "cons",
  Ann(
    GenerateConstructorTerm(listParams, listConstructors, 1),
    GenerateConstructorType("List", listParams, listConstructors[1])
  )
);

const maybeParams = [{ name: "A", type: Star() }];

const maybeConstructors = [
  { name: Identifier("null"), args: [] },
  {
    name: Identifier("just"),
    args: [
      {
        name: "value",
        type: Par("A"),
      },
    ],
  },
];

export const maybe = buildType(
  Identifier("Maybe"),
  maybeParams,
  maybeConstructors
);

export const mnull = Def(
  "null",
  Ann(
    GenerateConstructorTerm(maybeParams, maybeConstructors, 0),
    GenerateConstructorType("Maybe", maybeParams, maybeConstructors[0])
  )
);

export const just = Def(
  "just",
  Ann(
    GenerateConstructorTerm(maybeParams, maybeConstructors, 1),
    GenerateConstructorType("Maybe", maybeParams, maybeConstructors[1])
  )
);

const pairParams = [
  { name: "A", type: Star() },
  { name: "B", type: Star() },
];

const pairConstructors = [
  {
    name: Identifier("pair"),
    args: [
      {
        name: "a",
        type: Par("A"),
      },
      {
        name: "b",
        type: Par("B"),
      },
    ],
  },
];

export const pair = buildType(Identifier("Pair"), pairParams, pairConstructors);
export const ppair = Def(
  "pair",
  Ann(
    GenerateConstructorTerm(pairParams, pairConstructors, 0),
    GenerateConstructorType("Pair", pairParams, pairConstructors[0])
  )
);

// and : * -> * -> *
// and = λp. λq. Πc:*. (p -> q -> c) -> c
export const and = Def(
  "and",
  Ann(
    Abs(
      "p",
      Abs(
        "q",
        Pi(
          "c",
          Star(),
          Pi(
            "",
            Pi("", Var("p", 2), Pi("", Var("q", 2), Var("c", 2))),
            Var("c", 1)
          )
        )
      )
    ),
    Pi("", Star(), Pi("", Star(), Star()))
  )
);

// conj : Πp:*. Πq:*. p -> q -> and p q
// conj = λp. λq. λx. λy. λc. λf. f x y
export const conj = Def(
  "conj",
  Ann(
    Abs(
      "p",
      Abs(
        "q",
        Abs(
          "x",
          Abs(
            "y",
            Abs("c", Abs("f", App(App(Var("f", 0), Var("x", 3)), Var("y", 2))))
          )
        )
      )
    ),
    Pi(
      "p",
      Star(),
      Pi(
        "q",
        Star(),
        Pi(
          "",
          Var("p", 1),
          Pi("", Var("q", 1), App(App(Ref("and"), Var("p", 3)), Var("q", 2)))
        )
      )
    )
  )
);

// proj1 : Πp:*. Πq:*. and p q → p
// proj1 : λp. λq. λa. a p (λx. λy. x)
export const proj1 = Def(
  "proj1",
  Ann(
    Abs(
      "p",
      Abs(
        "q",
        Abs(
          "a",
          App(App(Var("a", 0), Var("p", 2)), Abs("x", Abs("y", Var("x", 1))))
        )
      )
    ),
    Pi(
      "p",
      Star(),
      Pi(
        "q",
        Star(),
        Pi("", App(App(Ref("and"), Var("p", 1)), Var("q", 0)), Var("p", 2))
      )
    )
  )
);

// proj2 : Πp:*. Πq:*. and p q → q
// proj2 = λp.   λq. λa. a q (λx. λy. y)
export const proj2 = Def(
  "proj2",
  Ann(
    Abs(
      "p",
      Abs(
        "q",
        Abs(
          "a",
          App(App(Var("a", 0), Var("q", 1)), Abs("x", Abs("y", Var("y", 0))))
        )
      )
    ),
    Pi(
      "p",
      Star(),
      Pi(
        "q",
        Star(),
        Pi("", App(App(Ref("and"), Var("p", 1)), Var("q", 0)), Var("q", 1))
      )
    )
  )
);

// and_commutes : Πp:*. Πq:*. and p q → and q p
// and_commutes = λp. λq. λa. conj q p (proj2 p q a) (proj1 p q a)
export const andCommutes = Def(
  "and_commutes",
  Ann(
    Abs(
      "p",
      Abs(
        "q",
        Abs(
          "a",
          App(
            App(
              App(App(Ref("conj"), Var("q", 1)), Var("p", 2)),
              App(App(App(Ref("proj2"), Var("p", 2)), Var("q", 1)), Var("a", 0))
            ),
            App(App(App(Ref("proj1"), Var("p", 2)), Var("q", 1)), Var("a", 0))
          )
        )
      )
    ),
    Pi(
      "p",
      Star(),
      Pi(
        "q",
        Star(),
        Pi(
          "",
          App(App(Ref("and"), Var("p", 1)), Var("q", 0)),
          App(App(Ref("and"), Var("q", 1)), Var("p", 2))
        )
      )
    )
  )
);
