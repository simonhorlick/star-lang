import { Ann, App, Identifier, Par, Ref, Star } from "./pratt";
import {
  GenerateConstructorTerm,
  GenerateConstructorType,
  buildType,
  desugar,
} from "./adts";
import { ADT, Constructor, Def } from "./ast";

export const boolConstructors: Constructor[] = [
  { name: Identifier("false"), args: [], typ: null },
  { name: Identifier("true"), args: [], typ: null },
];

export const boolADT = ADT(Identifier("Bool"), [], boolConstructors);

export const bool = desugar(buildType(boolADT));

export const fls = desugar(
  Def(
    "false",
    Ann(
      GenerateConstructorTerm([], boolConstructors, 0),
      GenerateConstructorType("Bool", [], boolConstructors[0])
    )
  )
);

export const tru = desugar(
  Def(
    "true",
    Ann(
      GenerateConstructorTerm([], boolConstructors, 1),
      GenerateConstructorType("Bool", [], boolConstructors[1])
    )
  )
);

const unitConstructors: Constructor[] = [
  { name: Identifier("unit"), args: [], typ: null },
];

export const unitADT = ADT(Identifier("Unit"), [], unitConstructors);

export const unit = desugar(buildType(unitADT));

export const unt = desugar(
  Def(
    "unit",
    Ann(
      GenerateConstructorTerm([], unitConstructors, 0),
      GenerateConstructorType("Unit", [], unitConstructors[0])
    )
  )
);

const natConstructors: Constructor[] = [
  { name: Identifier("zero"), args: [], typ: null },
  {
    name: Identifier("succ"),
    args: [{ name: "n", type: Ref("Nat") }],
    typ: null,
  },
];

export const natADT = ADT(Identifier("Nat"), [], natConstructors);

export const nat = desugar(buildType(natADT));

export const zero = desugar(
  Def(
    "zero",
    Ann(
      GenerateConstructorTerm([], natConstructors, 0),
      GenerateConstructorType("Nat", [], natConstructors[0])
    )
  )
);

export const succ = desugar(
  Def(
    "succ",
    Ann(
      GenerateConstructorTerm([], natConstructors, 1),
      GenerateConstructorType("Nat", [], natConstructors[1])
    )
  )
);

const listParams = [{ name: "A", type: Star() }];

const listConstructors: Constructor[] = [
  { name: Identifier("nil"), args: [], typ: null },
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
    typ: null,
  },
];

export const listADT = ADT(Identifier("List"), listParams, listConstructors);

export const list = desugar(buildType(listADT));

export const nil = desugar(
  Def(
    "nil",
    Ann(
      GenerateConstructorTerm(listParams, listConstructors, 0),
      GenerateConstructorType("List", listParams, listConstructors[0])
    )
  )
);

export const cons = desugar(
  Def(
    "cons",
    Ann(
      GenerateConstructorTerm(listParams, listConstructors, 1),
      GenerateConstructorType("List", listParams, listConstructors[1])
    )
  )
);

const maybeParams = [{ name: "A", type: Star() }];

const maybeConstructors: Constructor[] = [
  { name: Identifier("null"), args: [], typ: null },
  {
    name: Identifier("just"),
    args: [
      {
        name: "value",
        type: Par("A"),
      },
    ],
    typ: null,
  },
];

export const maybeADT = ADT(
  Identifier("Maybe"),
  maybeParams,
  maybeConstructors
);

export const maybe = desugar(buildType(maybeADT));

export const mnull = desugar(
  Def(
    "null",
    Ann(
      GenerateConstructorTerm(maybeParams, maybeConstructors, 0),
      GenerateConstructorType("Maybe", maybeParams, maybeConstructors[0])
    )
  )
);

export const just = desugar(
  Def(
    "just",
    Ann(
      GenerateConstructorTerm(maybeParams, maybeConstructors, 1),
      GenerateConstructorType("Maybe", maybeParams, maybeConstructors[1])
    )
  )
);

const pairParams = [
  { name: "A", type: Star() },
  { name: "B", type: Star() },
];

const pairConstructors: Constructor[] = [
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
    typ: null,
  },
];

export const pairADT = ADT(Identifier("Pair"), pairParams, pairConstructors);

export const pair = desugar(buildType(pairADT));
export const ppair = desugar(
  Def(
    "pair",
    Ann(
      GenerateConstructorTerm(pairParams, pairConstructors, 0),
      GenerateConstructorType("Pair", pairParams, pairConstructors[0])
    )
  )
);

const vectBoolParams = [{ name: "sz", type: Ref("Nat") }];

const vectBoolConstructors: Constructor[] = [
  {
    name: Identifier("vbnil"),
    args: [],
    // vbnil : VectBool(zero)
    typ: App(Ref("VectBool"), Ref("zero")),
  },
  {
    name: Identifier("vbext"),
    args: [
      {
        name: "n",
        type: Ref("Nat"),
      },
      {
        name: "head",
        type: Ref("Bool"),
      },
      {
        name: "tail",
        type: App(Ref("VectBool"), Par("n")),
      },
    ],
    // vbext : (n:Nat) -> (head:Bool) -> (tail:VectBool(n)) -> VectBool(succ(n))
    typ: App(Ref("VectBool"), App(Ref("succ"), Par("n"))),
  },
];

export const vectBoolADT = ADT(
  Identifier("VectBool"),
  vectBoolParams,
  vectBoolConstructors
);

export const vectBool = desugar(buildType(vectBoolADT));

export const vbnil = desugar(
  Def(
    "vbnil",
    Ann(
      GenerateConstructorTerm(vectBoolParams, vectBoolConstructors, 0),
      GenerateConstructorType(
        "VectBool",
        vectBoolParams,
        vectBoolConstructors[0]
      )
    )
  )
);

export const vbext = desugar(
  Def(
    "vbext",
    Ann(
      GenerateConstructorTerm(vectBoolParams, vectBoolConstructors, 1),
      GenerateConstructorType(
        "VectBool",
        vectBoolParams,
        vectBoolConstructors[1]
      )
    )
  )
);
