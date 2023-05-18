import { describe, expect, test } from "@jest/globals";
import { Ann, App, Def, Hole, Identifier, Par, Ref, Star } from "./ast";
import { infer } from "./check";
import {
  GenerateConstructorTerm,
  GenerateConstructorType,
  buildConstructor,
  buildType,
} from "./process";
import { adts, defs } from "./typecheck_test";

describe("holes", () => {
  const boolConstructors = [
    { name: Identifier("false"), args: [] },
    { name: Identifier("true"), args: [] },
  ];

  const bool = buildType(Identifier("Bool"), [], boolConstructors);

  const fls = Def(
    "false",
    GenerateConstructorTerm([], boolConstructors, 0),
    GenerateConstructorType("Bool", [], boolConstructors[0])
  );

  const tru = Def(
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

  const list = buildType(Identifier("List"), listParams, listConstructors);

  const nil = Def(
    "nil",
    GenerateConstructorTerm(listParams, listConstructors, 0),
    GenerateConstructorType("List", listParams, listConstructors[0])
  );

  const cons = Def(
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

  const maybe = buildType(Identifier("Maybe"), maybeParams, maybeConstructors);

  const mnull = Def(
    "null",
    GenerateConstructorTerm(maybeParams, maybeConstructors, 0),
    GenerateConstructorType("Maybe", maybeParams, maybeConstructors[0])
  );

  const just = Def(
    "just",
    GenerateConstructorTerm(maybeParams, maybeConstructors, 1),
    GenerateConstructorType("Maybe", maybeParams, maybeConstructors[1])
  );

  /*
  
  A hole is a place in the AST that's left blank for the compiler to figure
  out the contents. Generally speaking, this is allowed only when it's
  obvious from the context what should be filled in. For example, in the
  term `cons(▨, true, nil(▨))` we can fill both holes with Bool (as the true has type Bool).
  
  Note that the constructors for List are defined as:
    nil : (T *) → List(T)
    cons : (T *) → (head T) → (tail List(T)) → List(T)
  
  When we parse `cons(▨, true, nil(▨))` we get the following AST:
      
               ap
            /      \
          ap        ap
         /  \      /  \
       ap  true  nil   ▨
      /  \
    cons  ▨
    
  We should be able to infer
    cons(▨, true, nil(▨))
    cons(α, true, nil(α))
  i.e. the two holes represent the same term.

  Now we replace the holes with metavariables - holes that must represent the
  same term get assigned the same metavariable. This is inferred in the normal
  way through type inference.
  
  When we encounter a hole - how do we know it's the same metavariable as another hole? Can we look it up in the typing context and see if that's a hole?
  
              ap
            /    \
          ap      ap:List(α)
         /  \        /    \
       ap   1:α     nil   α:*
      /  \
    cons  α:*

  Now because 1:Int we can infer T=Int. (we should have α in a context somewhere so we can use this to set all the occurances of it, then typecheck again).

               ap
            /      \
          ap        ap:List(Int)
         /  \        /  \
       ap   1:Int  nil   Int:*
      /  \
    cons  Int:*
    
    
    TODO: We need to somehow return the hole substitution (+constraints) to
    higher levels of the checker so that we can do substitutions there too.
    Either that or we compute the substitutions in one pass, apply them and
    check them in a subsequent pass.
*/

  test("cons(▨, true, nil(▨))", () => {
    const expr = App(
      App(App(Ref("cons"), Hole(0)), Ref("true")),
      App(Ref("nil"), Hole(1))
    );

    const result = infer(
      defs([list, nil, cons, bool, tru, fls]),
      adts([]),
      [],
      expr,
      0,
      0
    );
    console.log(result);
  });

  /*
  Note that the constructors for Maybe are defined as:
    null : (T *) → Maybe(T)
    just : (T *) → (value T) → Maybe(T)
  
  When we parse `null(▨):Maybe(Bool)` we get the following AST:
  
  Ann(App(Ref("null"),Hole()),App(Ref("Maybe"), Ref("Bool")))
  
  Using the definition of null we have
    null : (T *) → Maybe(T)
    null : ΠT:* Maybe(Var(0))
  so given that `null(▨)` has type `Maybe(Bool)`
    null(▨) : Maybe(Bool)
    check null(▨) has type Maybe(Bool)
    infer type Maybe(▨)
    
    
           ann
        /      \
       ap       ap
      /  \    /    \
    null  ▨  Maybe Bool
    
    we'll have case Hole (check Bool) so we can fill the Hole with Bool.
  */

  test("null(▨):Maybe(Bool)", () => {
    const expr = Ann(App(Ref("null"), Hole(0)), App(Ref("Maybe"), Ref("Bool")));

    const result = infer(
      defs([maybe, mnull, just, bool, tru, fls]),
      adts([]),
      [],
      expr,
      0,
      0
    );
    console.log(result);
  });
});
