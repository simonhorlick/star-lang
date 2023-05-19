import { App, Def, Identifier, Par, Ref, Star } from "./ast";
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
  GenerateConstructorTerm([], boolConstructors, 0),
  GenerateConstructorType("Bool", [], boolConstructors[0])
);

export const tru = Def(
  "true",
  GenerateConstructorTerm([], boolConstructors, 1),
  GenerateConstructorType("Bool", [], boolConstructors[1])
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
  GenerateConstructorTerm(listParams, listConstructors, 0),
  GenerateConstructorType("List", listParams, listConstructors[0])
);

export const cons = Def(
  "cons",
  GenerateConstructorTerm(listParams, listConstructors, 1),
  GenerateConstructorType("List", listParams, listConstructors[1])
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
  GenerateConstructorTerm(maybeParams, maybeConstructors, 0),
  GenerateConstructorType("Maybe", maybeParams, maybeConstructors[0])
);

export const just = Def(
  "just",
  GenerateConstructorTerm(maybeParams, maybeConstructors, 1),
  GenerateConstructorType("Maybe", maybeParams, maybeConstructors[1])
);
