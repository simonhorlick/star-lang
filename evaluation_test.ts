import { describe, expect, test } from "@jest/globals";
import { Ref, Var, identifier, identifier2, utf8 } from "./ast";
import * as Erased from "./erased";
import {
  mockRuntime,
  reduce,
  reduceOnce3,
  termShift2,
  termSubst2,
} from "./evaluation";
import { prettyC } from "./pretty";
import {
  Parser,
  Stream,
  any3,
  any4,
  bind,
  char,
  either,
  lazy,
  many,
  many1,
  map,
  optional,
  pure,
  spaces,
  str,
  whitespace,
} from "./parser";
import { result } from "./parser_test";

describe("shifting", () => {
  test("ensure we only shift free variables", () => {
    // we need to shift the 2, but not the 0 or the 1, as 2 is free in this
    // expression.

    // λ.λ.1(0(2)) shifted up by 2 is:
    // λ.λ.1(0(4))
    let term = Erased.Abs(
      "x",
      Erased.Abs(
        "y",
        Erased.App(
          Erased.Var("x", 1),
          Erased.App(Erased.Var("y", 0), Erased.Var("z", 2))
        )
      )
    );
    let actual = termShift2(2, term);
    let expected = Erased.Abs(
      "x",
      Erased.Abs(
        "y",
        Erased.App(
          Erased.Var("x", 1),
          Erased.App(Erased.Var("y", 0), Erased.Var("z", 4))
        )
      )
    );
    expect(actual).toStrictEqual(expected);
  });

  test("ensure we only shift free variables", () => {
    // note left association of app in the following syntax:
    // λ.01(λ.012) shifted up by 2 is:
    // λ.03(λ.014)
    let term = Erased.Abs(
      "",
      Erased.App(
        Erased.App(Erased.Var("", 0), Erased.Var("", 1)),
        Erased.Abs(
          "",
          Erased.App(
            Erased.App(Erased.Var("", 0), Erased.Var("", 1)),
            Erased.Var("", 2)
          )
        )
      )
    );
    let actual = termShift2(2, term);
    let expected = Erased.Abs(
      "",
      Erased.App(
        Erased.App(Erased.Var("", 0), Erased.Var("", 3)),
        Erased.Abs(
          "",
          Erased.App(
            Erased.App(Erased.Var("", 0), Erased.Var("", 1)),
            Erased.Var("", 4)
          )
        )
      )
    );
    expect(actual).toStrictEqual(expected);
  });
});

describe("substitution", () => {
  // Examples:
  // [x/s]x = s
  // [x/s]y = y                       (if y ≠ x)
  // [x/s](λy.t1) = λy.[x/s]t1        (if y ≠ x and y ∉ FV(s))
  // [x/s](t1 t2) = [x/s]t1 [x/s]t2

  test("[x/s]x = s", () => {
    let term = Erased.Var("x", 1);
    let actual = termSubst2(1, Erased.Var("s", 2), term);
    let expected = Erased.Var("s", 2);
    expect(actual).toStrictEqual(expected);
  });

  test("[x/s]y = y", () => {
    let term = Erased.Var("y", 0);
    let actual = termSubst2(1, Erased.Var("s", 2), term);
    let expected = Erased.Var("y", 0);
    expect(actual).toStrictEqual(expected);
  });

  test("[b/a](λb. b a)", () => {
    // [b/a](λb. b a)
    // [0/1](λ. 0 2)
    // λ. 0 2 i.e. λb. b a, this is the same, nothing has been substituted.
    let term = Erased.Abs(
      "b",
      Erased.App(Erased.Var("b", 0), Erased.Var("a", 2))
    );
    let actual = termSubst2(0, Var("", 1), term);
    let expected = Erased.Abs(
      "b",
      Erased.App(Erased.Var("b", 0), Erased.Var("a", 2))
    );
    expect(actual).toStrictEqual(expected);
  });

  test("[b/a](b (λx.λy.b))", () => {
    // replace occurances of b with a:
    // [b/a](b (λx.λy.b))
    // (a (λx.λy.a))
    // in debruijin form b=0,a=1:
    // [0/1](0 (λ.λ.2))
    // 1 (λ.λ.3)
    let term = Erased.App(
      Erased.Var("", 0),
      Erased.Abs("", Erased.Abs("", Erased.Var("", 2)))
    );
    let actual = termSubst2(0, Erased.Var("", 1), term);
    let expected = Erased.App(
      Erased.Var("", 1),
      Erased.Abs("", Erased.Abs("", Erased.Var("", 3)))
    );
    expect(actual).toStrictEqual(expected);
  });
});

// abstraction parses a lambda abstraction `λx t`. The binder x is separated
// from the body by spaces.
const abstraction = (term: () => Parser<Erased.Term>): Parser<Erased.Abs> =>
  bind(char("λ"), (_) =>
    bind(optional(spaces), (_) =>
      bind(identifier, (name) =>
        bind(spaces, (_) =>
          bind(lazy(term), (body) => pure(Erased.Abs(name, body)))
        )
      )
    )
  );

// parenthesis is a parser that requires an opening and closing parenthesis to
// surround the given parser.
const parenthesis = <T>(between: Parser<T>): Parser<T> =>
  bind(char("("), (_) => bind(between, (x) => bind(char(")"), (_) => pure(x))));

// application is a parser for function application `f(x)`; `f(x)(y)`; `f (x(t))`.
const application = (
  term: () => Parser<Erased.Term>,
  lhs: Erased.Term
): Parser<Erased.Term> =>
  // f(x) or (some term)(x)
  bind(many(whitespace), (_) =>
    // args: greedily parse as many as we're able to
    bind(many1(parenthesis(lazy(term))), (ts) => {
      const terms = [lhs, ...ts];
      // Application is left-associative, so form the following tree of
      // applications, i.e. f(x)(y) == (f(x))(y):
      //      ap
      //     /  \
      //    ap   y
      //   /  \
      //  f    x

      // ["f","x","y","z"]
      //    {f x}["y","z"]
      //    {{f x} y}["z"]
      //     {{{f x} y} z}
      const expr = terms.slice(2).reduce<Erased.App>(
        (acc, t) => ({
          _: "app",
          left: acc,
          right: t,
        }),
        {
          _: "app",
          left: terms[0],
          right: terms[1],
        }
      );

      return pure(expr);
    })
  );

// reference parses a "variable" in the programming language.
const reference: Parser<Erased.Term> = map(identifier, (result: string) =>
  Ref(result)
);

export const stringLiteral: Parser<Erased.Term> = bind(str('"'), (_) =>
  bind(many(utf8), (s) =>
    bind(str('"'), (_) => pure({ _: "str", str: s.join("") }))
  )
);

const term: Parser<Erased.Term> = bind(
  any4(
    parenthesis(lazy(() => term)),
    abstraction(() => term),
    reference,
    stringLiteral
  ),
  (lhs) =>
    // A term followed by another term is a function application, for
    // example `g(x)(y)(z)`.
    either(
      application(() => term, lhs),
      pure(lhs)
    )
);

export const ts = (s: string): Stream => ({
  src: s,
  idx: 0,
});

export type Context = string[];

export const desugar = (t: Erased.Term, ctx: Context = []): Erased.Term => {
  switch (t._) {
    case "app":
      return Erased.App(desugar(t.left, ctx), desugar(t.right, ctx));
    case "lam":
      return Erased.Abs(t.name, desugar(t.body, ctx.concat(t.name)));
    case "ref":
      // At this point we're still unsure whether this node is a Var or a Ref.
      // So look it up first and if a Var exists then use that.
      for (let i = 0; i < ctx.length; i++) {
        const binding = ctx[ctx.length - i - 1];
        if (binding == t.name) {
          return Var(binding, i);
        }
      }
      return t;
    case "var":
      throw "unexpected var";
    case "str": {
      return t;
    }
  }
};

// parse a term of untyped lambda calculus.
const pt = (src: string): Erased.Term => desugar(result(term(ts(src))));

const expectEquivalent = (a: Erased.Term, b: Erased.Term) =>
  expect(prettyC(a, true)).toBe(prettyC(b, true));

describe("untyped lambda calculus parser", () => {
  test("parse pair", () => {
    const pair = pt("λa λb λf f(a)(b)");
    const expected = Erased.Abs(
      "a",
      Erased.Abs(
        "b",
        Erased.Abs(
          "f",
          Erased.App(
            Erased.App(Erased.Var("f", 0), Erased.Var("a", 2)),
            Erased.Var("b", 1)
          )
        )
      )
    );
    expectEquivalent(pair, expected);
  });

  test("parse fst", () => {
    const fst = pt("λg g(λa λb a)");
    const expected = Erased.Abs(
      "g",
      Erased.App(
        Erased.Var("g", 0),
        Erased.Abs("a", Erased.Abs("b", Erased.Var("a", 1)))
      )
    );
    expectEquivalent(fst, expected);
  });
});

describe("runtime evaluation", () => {
  test("beta reduction of pair is in applicative order", () => {
    const pair = Erased.Def("pair", pt("λa λb λf f(a)(b)"));
    const fst = Erased.Def("fst", pt("λg g(λa λb a)"));
    const snd = Erased.Def("snd", pt("λg g(λa λb b)"));
    let t = pt(`fst(pair("p")("q"))`);

    console.log(prettyC(t));
    let result = reduceOnce3(mockRuntime, [pair, fst, snd], t);

    for (let i = 0; i < 7; i++) {
      console.log(prettyC(result.term));
      result = reduceOnce3(mockRuntime, [pair, fst, snd], result.term);
    }

    let expected = Erased.StringLit("p");
    expect(result.term).toStrictEqual(expected);
  });

  test("zero cannot be reduced", () => {
    const zero = pt("λs λz z");
    let result = reduceOnce3(mockRuntime, [], zero);
    expect(result.term).toStrictEqual(zero);
  });

  test("beta reduce succ(zero)", () => {
    const t = pt("(λn λs λz s(n))(λs λz z)");
    let result = reduceOnce3(mockRuntime, [], t);
    expect(result.term).toStrictEqual(pt("λs λz s(λs λz z)"));
  });

  test("reduction order is Beta, then Nu, and finally Mu", () => {
    const t = pt("(λn λs λz s(n))(λs λz z)");
    let result = reduceOnce3(mockRuntime, [], t);
    expect(result.term).toStrictEqual(pt("λs λz s(λs λz z)"));
    throw "TODO";
  });

  test("println", () => {
    // TODO: undefined reference?
    const t = pt(`println("hello")(λs λz z)`);
    let result = reduceOnce3(mockRuntime, [], t);
    expect(result.term).toStrictEqual(pt("λs λz s(λs λz z)"));
  });

  test("getchar", () => {
    // TODO: inject runtime functions
    const t = pt(`getchar(λs λz z)`);
    let result = reduceOnce3(mockRuntime, [], t);
    expect(result.term).toStrictEqual(pt("λs λz s(λs λz z)"));
  });

  test("beta reduction of recursive function", () => {
    const zero = Erased.Def("zero", pt("λs λz z"));
    const succ = Erased.Def("succ", pt("λn λs λz s(n)"));

    // counts backwards from n and returns zero
    const cnt = Erased.Def("cnt", pt("λn n(λx cnt(x))(zero)"));

    const defs = [zero, succ, cnt];

    // cnt(2)
    let t = pt(`cnt(λs λz s(λs λz s(λs λz z)))`);

    /*
         example = cnt(2)
                 = cnt(λs λz s(λs λz s(λs λz z)))
                 = (λn n(λx cnt(x))(zero))(λs λz s(λs λz s(λs λz z)))
                 = (λs λz s(λs λz s(λs λz z)))(λx cnt(x))(zero)
                 = λz (λx cnt(x))(λs λz s(λs λz z))(zero)
                 = (λx cnt(x))(λs λz s(λs λz z))
                 = cnt(λs λz s(λs λz z))
                 = (λn n(λx cnt(x))(zero))(λs λz s(λs λz z))
                 = (λs λz s(λs λz z))(λx cnt(x))(zero)
                 = λz (λx cnt(x))(λs λz z)(zero)
                 = (λx cnt(x))(λs λz z)
                 = cnt(λs λz z)
                 = (λn n(λx cnt(x))(zero))(λs λz z)
                 = (λs λz z)(λx cnt(x))(zero)
                 = zero
    */
    let result = reduceOnce3(mockRuntime, defs, t);

    for (let i = 0; i < 17; i++) {
      console.log(prettyC(result.term));
      result = reduceOnce3(mockRuntime, defs, result.term);
    }

    expect(result.term).toStrictEqual(pt("λs λz z"));
  });
});

// describe("evaluation", () => {
//   // (λx. x)(λz. z) -> (λz. z)
//   test("TestReduceIdentity", () => {
//     const identity = Erased.App(
//       Erased.Abs("x", Erased.Var("x", 0)),
//       Erased.Abs("z", Erased.Var("z", 0))
//     );
//     const expected: Erased.Term = Erased.Abs("z", Erased.Var("z", 0));

//     const actual = reduce([], identity);

//     expect(actual).toStrictEqual(expected);
//   });

//   // Test that substituting top level functions works properly.
//   test("TestSubstituteDef", () => {
//     const expected = Erased.Abs("z", Erased.Var("z", 0));
//     const actual = reduce(
//       [id],
//       Erased.App(Ref("id"), Erased.Abs("z", Erased.Var("z", 0)))
//     );
//     expect(actual).toStrictEqual(expected);
//   });

//   // "if" reduction
//   //
//   // top level defs (after typecheck has passed):
//   //
//   // tru = λt. λf. t
//   // fls = λt. λf. f
//   // test = λl. λm. λn. (l(m))(n)
//   //
//   // ((test(tru))(v))(w)
//   // ------------------- def "test"
//   // (((λl. λm. λn. (l(m))(n))(tru))(v))(w)
//   // -------------------------------------- E-AppAbs
//   // ((λm. λn. (tru(m))(n))(v))(w)
//   // ----------------------------- E-AppAbs
//   // (λn. (tru(v))(n))(w)
//   // -------------------- E-AppAbs
//   // (tru(v))(w)
//   // ----------- def "tru"
//   // ((λt. λf. t)(v))(w)
//   // ------------------- E-AppAbs
//   // (λf. v)(w)
//   // ---------- E-AppAbs
//   // v
//   test("TestReduceIfElse", () => {
//     // ((test(tru))(1))(2)
//     const ifElse: Erased.Term = Erased.App(
//       Erased.App(Erased.App(Erased.Ref("test"), Erased.Ref("tru")), one),
//       two
//     );
//     const expected = one;
//     const actual = reduce([tru, fls, testfn], ifElse);

//     expect(actual).toStrictEqual(expected);
//   });

//   test("should ensure redex uses up bound variable", () => {
//     // Γ = [z→2, y→1]
//     // (λx. y(x)(z))(λx. x)
//     // y(λx. x)(z)
//     // This corresponds to the nameless representation:
//     // (λx. 1(0)(2))(λx. 0)
//     // After one step of evaluation, then indices for y and z are reduced by 1
//     // as the x binder has now been used up.
//     // 0(λx. 0)(1)

//     let src = Erased.App(
//       Erased.Abs(
//         "x",
//         Erased.App(
//           Erased.App(Erased.Var("y", 1), Erased.Var("x", 0)),
//           Erased.Var("z", 2)
//         )
//       ),
//       Erased.Abs("x", Erased.Var("x", 0))
//     );

//     let expected = Erased.App(
//       Erased.App(Erased.Var("y", 0), Erased.Abs("x", Erased.Var("x", 0))),
//       Erased.Var("z", 1)
//     );

//     const actual = reduceOnce2([], src);

//     expect(actual).toStrictEqual(expected);
//   });
// });
