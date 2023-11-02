import { Ann, App, Def, Identifier, Par, Ref, Star } from "./ast";
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
