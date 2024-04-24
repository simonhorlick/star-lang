import {
  ADT,
  Abs,
  Ann,
  App,
  Def,
  Identifier,
  Par,
  Pi,
  Ref,
  Self,
  Star,
  Var,
} from "./ast";
import {
  GenerateConstructorTerm,
  GenerateConstructorType,
  buildType,
} from "./adts";

const boolConstructors = [
  { name: Identifier("false"), args: [] },
  { name: Identifier("true"), args: [] },
];

export const boolADT = ADT(Identifier("Bool"), [], boolConstructors);

export const bool = buildType(boolADT);

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

export const unitADT = ADT(Identifier("Unit"), [], unitConstructors);

export const unit = buildType(unitADT);

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

export const natADT = ADT(Identifier("Nat"), [], natConstructors);

export const nat = buildType(natADT);

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

export const listADT = ADT(Identifier("List"), listParams, listConstructors);

export const list = buildType(listADT);

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

export const maybeADT = ADT(
  Identifier("Maybe"),
  maybeParams,
  maybeConstructors
);

export const maybe = buildType(maybeADT);

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

export const pairADT = ADT(Identifier("Pair"), pairParams, pairConstructors);

export const pair = buildType(pairADT);
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

// A vector is essentially a List, but with the length encoded as
// part of the type. In the following tests we hard-code the type argument of
// the Vector to be Bool as it slightly simplifies the tests.
//
// Vect : Πsz:Nat ★
//      = λsz ιt
//        ΠP:(Πn:Nat Πx:Vect(n) ★)
//        Πcnil:P(zero)(vnil)
//        Πcext:(Πn:Nat Πhead:Bool Πtail:Vect(n) P(succ(n))(ext(n)(head)(tail))
//        P(sz)(t)
// vnil : Vect(zero)
//      = λP λcnil λcext cnil
//  ext : Πn:Nat Πhead:Bool Πtail:Vect(n) Vect(succ(n))
//      = λn λhead λtail λP λcnil λcext cext(n)(head)(tail)
export const vect = Def(
  "Vect",
  Ann(
    // λsz
    Abs(
      "sz", // the length of the tail Vector
      // ιt
      Self(
        "t",
        // ΠP:(Πn:Nat Vect(n)→★)
        Pi(
          "P",
          Pi("n", Ref("Nat"), Pi("x", App(Ref("Vect"), Var("n", 0)), Star())),
          // Πcnil:P(zero)(vnil)
          Pi(
            "cnil",
            App(App(Var("P", 0), Ref("zero")), Ref("vnil")),
            // Πcext:(Πn:Nat Πhead:Bool Πtail:Vect(n) P(succ(n))(ext(n)(head)(tail))
            Pi(
              "cext",
              Pi(
                "n",
                Ref("Nat"),
                Pi(
                  "head",
                  Ref("Bool"),
                  Pi(
                    "tail",
                    App(Ref("Vect"), Var("n", 1)),
                    // P(succ(n))(ext(n)(head)(tail))
                    App(
                      App(Var("P", 4), App(Ref("succ"), Var("n", 2))),
                      App(
                        App(App(Ref("ext"), Var("n", 2)), Var("head", 1)),
                        Var("tail", 0)
                      )
                    )
                  )
                )
              ),
              App(App(Var("P", 2), Var("sz", 4)), Var("t", 3))
            )
          )
        )
      )
    ),
    Pi("sz", Ref("Nat"), Star())
  )
);

//  ext : Πn:Nat Πhead:Bool Πtail:Vect(n) Vect(succ(n))
//      = λn λhead λtail λP λcnil λcext cext(n)(head)(tail)
export const ext = Def(
  "ext",
  Ann(
    // λn λhead λtail λP λcnil λcext cext(n)(head)(tail)
    Abs(
      "n",
      Abs(
        "head",
        Abs(
          "tail",
          Abs(
            "P",
            Abs(
              "cnil",
              Abs(
                "cext",
                App(
                  App(App(Var("cext", 0), Var("n", 5)), Var("head", 4)),
                  Var("tail", 3)
                )
              )
            )
          )
        )
      )
    ),
    // Πn:Nat Πhead:Bool Πtail:Vect(n) Vect(succ(n))
    Pi(
      "n",
      Ref("Nat"),
      Pi(
        "head",
        Ref("Bool"),
        Pi(
          "tail",
          App(Ref("Vect"), Var("n", 1)),
          App(Ref("Vect"), App(Ref("succ"), Var("n", 2)))
        )
      )
    )
  )
);

// vnil : Vect(zero)
//      = λP λcnil λcext cnil
export const vnil = Def(
  "vnil",
  Ann(
    // λP λcnil λcext cnil
    Abs("P", Abs("cnil", Abs("cext", Var("cnil", 1)))),
    // Vect(zero)
    App(Ref("Vect"), Ref("zero"))
  )
);
