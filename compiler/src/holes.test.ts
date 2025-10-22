import { describe, expect, test } from "vitest";
import { Ann, App, Hole, Ref } from "./sugar";
import { infer, adts, defs, fill } from "./typecheck";
import { pretty } from "./pretty";
import {
  bool,
  cons,
  fls,
  just,
  list,
  maybe,
  mnull,
  nil,
  tru,
} from "./test_defs";

describe("holes", () => {
  /*
  
  A hole is a place in the AST that's left blank for the compiler to figure
  out the contents. Generally speaking, this is allowed only when it's
  obvious from the context what should be filled in. For example, in the
  term `cons(▨, true, nil(▨))` we can fill both holes with Bool (as the true
  here has type Bool).
  
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

  Now we assign numbers to the holes. Holes that must necessarily represent the
  same term are assigned the same number. As part of the typechecking we do
  equality testing of terms, if one side is a hole we note down what it
  should correspond to (see typecheck.ts:equate). Similarly if we equate two
  holes (with possibly different numbers) we can mark that these two holes
  represent the same thing.
    
              ap
            /    \
          ap      ap:List(▨0)
         /  \        /    \
       ap   1:▨0    nil   ▨0:*
      /  \
    cons  ▨0:*

  Because 1:Int we can infer T=Int. We can go through the AST substituting Int
  every time we see the appropriate hole and run the checker again to verify.

               ap
            /      \
          ap        ap:List(Int)
         /  \        /  \
       ap   1:Int  nil   Int:*
      /  \
    cons  Int:*
    
  */

  test("cons(▨, true, nil(▨))", () => {
    const expr = App(
      App(App(Ref("cons"), Hole(0)), Ref("true")),
      App(Ref("nil"), Hole(1))
    );

    const result = infer(
      defs([list, nil, cons, bool, tru, fls]),
      adts(),
      [],
      expr,
      0,
      0
    );
    const filled = fill(result);
    expect(pretty(filled.term) + ":" + pretty(filled.type)).toBe(
      "cons(Bool,true,nil(Bool)):List(Bool)"
    );
  });

  test("cons(▨, true, nil(Bool))", () => {
    const expr = App(
      App(App(Ref("cons"), Hole(0)), Ref("true")),
      App(Ref("nil"), Ref("Bool"))
    );

    const result = infer(
      defs([list, nil, cons, bool, tru, fls]),
      adts(),
      [],
      expr,
      0,
      0
    );
    const filled = fill(result);
    expect(pretty(filled.term) + ":" + pretty(filled.type)).toBe(
      "cons(Bool,true,nil(Bool)):List(Bool)"
    );
  });

  test("unify many holes", () => {
    // [true, true, true]
    // cons(▨, true, cons(▨, true, cons(▨, true, nil(▨))))
    // all the holes should have the same type
    const expr = App(
      App(App(Ref("cons"), Hole(0)), Ref("true")),
      App(
        App(App(Ref("cons"), Hole(1)), Ref("true")),
        App(
          App(App(Ref("cons"), Hole(2)), Ref("true")),
          App(Ref("nil"), Ref("Bool"))
        )
      )
    );

    const result = infer(
      defs([list, nil, cons, bool, tru, fls]),
      adts(),
      [],
      expr,
      0,
      0
    );
    const filled = fill(result);
    expect(pretty(filled.term) + ":" + pretty(filled.type)).toBe(
      "cons(Bool,true,cons(Bool,true,cons(Bool,true,nil(Bool)))):List(Bool)"
    );
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
      adts(),
      [],
      expr,
      0,
      0
    );
    const filled = fill(result);
    expect(pretty(filled.term) + ":" + pretty(filled.type)).toBe(
      "null(Bool):Maybe(Bool)"
    );
  });
});
