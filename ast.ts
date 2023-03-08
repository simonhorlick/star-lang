import { addTermToCtx } from "./check";
import {
  Parser,
  bind,
  alpha,
  many,
  any,
  digit,
  oneOf,
  pure,
  Stream,
  Result,
  str,
  line,
  map,
  any3,
  any5,
  char,
  consumeAll,
  either,
  front,
  last,
  lazy,
  many1,
  newline,
  optional,
  orFail,
  whitespace,
  join,
  join1,
  any4,
  spaces,
  spc,
  spc1,
  any6,
} from "./parser";

export type VariableBinding = { type: "bind"; name: string; typ: Type };

export type Binding = VariableBinding;

export type Context = Binding[];

// Π is the type of functions.
export type Pi = {
  _: "pi";
  from: Type;
  to: Type;
  name: string; // name of the binder
};

export const Pi = (name: string, from: Type, to: Type): Pi => ({
  _: "pi",
  from: from,
  to: to,
  name: name,
});

// Abs is a lambda abstraction.
export type Abs = {
  _: "lam";
  name: string; // name of the binder
  body: Term; // the body of the abstraction
  argtype?: Term; // the type of the argument
};

export const Abs = (name: string, body: Term, argtype?: Term): Abs => ({
  _: "lam",
  name: name,
  body: body,
  argtype: argtype,
});

// Self is a way of abstracting out the value currently being typechecked so
// that it can be used within the body.
export type Self = {
  _: "self";
  name: string; // name of the binder
  body: Term; // the body of the abstraction
};

export const Self = (name: string, body: Term): Self => ({
  _: "self",
  name: name,
  body: body,
});

// App is a function application.
export type App = {
  _: "app";
  left: Term;
  right: Term;
};

export const App = (left: Term, right: Term): App => ({
  _: "app",
  left: left,
  right: right,
});

// A bound variable.
export type Var = {
  _: "var";

  // The variable name for pretty printing.
  name: string;

  // The de Bruijn index of this node. The number index stands for “the variable
  // bound by the index’th enclosing λ.”
  index: number;
};

export const Var = (name: string, index: number): Var => ({
  _: "var",
  name: name,
  index: index,
});

// A bound variable that has not yet been resolved to a debruijin index.
export type Par = {
  _: "par";

  // The variable name.
  name: string;
};

export const Par = (name: string): Par => ({
  _: "par",
  name: name,
});

// A reference.
export type Ref = {
  _: "ref";

  // The name of the definition being referenced.
  name: string;
};

export const Ref = (name: string): Ref => ({
  _: "ref",
  name: name,
});

// ★ is the kind of proper types.
export type Star = {
  _: "star";
};

export const Star = (): Star => ({
  _: "star",
});

// A type annotation.
export type Ann = {
  _: "ann";

  // The term this annotation applies to.
  term: Term;

  // The annotated type.
  typ: Type;
};

export const Ann = (term: Term, type: Type): Ann => ({
  _: "ann",
  term: term,
  typ: type,
});

export type Term = Abs | App | Var | Par | Ref | Ann | Pi | Star | Self | Case;
export type Type = Term;

type Argument = {
  name: string;
  type: Type;
};

export const Argument = (name: string, type: Type): Argument => ({
  name: name,
  type: type,
});

export type Constructor = {
  name: string;
  args: Argument[];
};

export const Constructor = (name: string, args: Argument[]): Constructor => ({
  name: name,
  args: args,
});

export type ADT = {
  _: "adt";
  name: string;
  params: Argument[];
  constructors: Constructor[];
};

export const ADT = (
  name: string,
  params: Argument[],
  constructors: Constructor[]
): ADT => ({
  _: "adt",
  name: name,
  params: params,
  constructors: constructors,
});

type Branch = {
  constructor: string;
  term: Term;
};

export const Branch = (constructor: string, term: Term): Branch => ({
  constructor: constructor,
  term: term,
});

export type Case = {
  _: "case";
  name: Ref;
  branches: Branch[];
};

export const Case = (name: Ref, branches: Branch[]): Case => ({
  _: "case",
  name: name,
  branches: branches,
});

// A top-level definition.
export type Def = {
  _: "def";
  name: string;
  term: Term;
  typ: Type;
};

export const Def = (name: string, term: Term, type: Type): Def => ({
  _: "def",
  name: name,
  typ: type,
  term: term,
});

export type Pkg = { _: "pkg"; name: string };

export type Com = { _: "com"; text: string };

export type Space = { _: "sp" };
export type Newline = { _: "nl" };

export type File = {
  _: "file";
  content: (Pkg | Com | Def | ADT | Space | Newline)[];
};

// identifier parses a letter from the alphabet followed by letters, numbers and
// other allowed special characters.
export const identifier: Parser<string> = orFail(
  "expected identifier",
  bind(alpha, (a) =>
    bind(many(any(alpha, digit, oneOf("_"))), (b) =>
      pure(a + (b?.join("") ?? ""))
    )
  )
);

type Origin<T> = {
  _: "ori";
  start: number;
  end: number;
  child: T;
};

// block is a parser that adds origin information into the parse tree. It can be
// disabled by setting origins to false in the stream.
export const block =
  <T>(parser: Parser<T>): Parser<Origin<T>> =>
  (s: Stream): Result<Origin<T>> => {
    const start = s.idx;
    const result = parser(s);

    if (result.type == "parseerror") {
      return result;
    }

    const origin: Origin<T> = {
      _: "ori",
      start: start,
      end: result.stream.idx,
      child: result.value,
    };
    return pure(origin)(result.stream);
  };

// parsePackage parses a package declaration such as `package abc`.
export const parsePackage: Parser<Pkg> = bind(str("package"), (_) =>
  bind(many1(whitespace), (_) =>
    bind(identifier, (a) => pure({ _: "pkg", name: a }))
  )
);

// parseLineComment parses an end-of-line comment and stops either at the end of
// the line or EOF.
export const parseLineComment: Parser<Com> = bind(str("//"), (_) =>
  bind(line, (l) =>
    pure({
      _: "com",
      text: l,
    })
  )
);

// reference parses a "variable" in the programming language.
export const reference: Parser<Ref> = map(identifier, (result: string) =>
  Ref(result)
);

// parenthesis is a parser that requires an opening and closing parenthesis to
// surround the given parser.
export const parenthesis = <T>(between: Parser<T>): Parser<T> =>
  bind(char("("), (_) => bind(between, (x) => bind(char(")"), (_) => pure(x))));

export const arrow: (type: () => Parser<Type>) => (s: Stream) => Result<Pi> = (
  type
) =>
  bind(
    // (A->B)->C
    either(reference, parenthesis(lazy(type))),
    (lhs) =>
      bind(
        many1(
          bind(str("->"), (_) =>
            bind(either(lazy(type), parenthesis(lazy(type))), (r) => pure(r))
          )
        ),
        // Mapping for arrows. We've already parsed the LHS, this is the first
        // arrow and onwards  ... ->B->C->D.
        //
        // A->(B->C)
        //      ar
        //     /  \
        //    A   ar
        //       /  \
        //      B    C
        (r) =>
          pure(
            Pi(
              "",
              lhs,
              front(r).reduceRight((prev, curr) => Pi("", curr, prev), last(r))
            )
          )
      )
  );

const star: Parser<Star> = bind(char("*"), () => pure(Star()));

export const type: Parser<Type> = any4(
  arrow(() => type),
  parenthesis(lazy(() => type)),
  star,
  reference
);

// // abstraction parses a lambda abstraction `λx:X. t`.
export const abstraction = (term: () => Parser<Term>): Parser<Abs> =>
  bind(char("λ"), (_) =>
    bind(optional(spaces), (_) =>
      bind(identifier, (name) =>
        bind(optional(spaces), (_) =>
          bind(char(":"), (_) =>
            bind(optional(spaces), (_) =>
              bind(type, (typ) =>
                bind(optional(spaces), () =>
                  bind(char("."), () =>
                    bind(optional(spaces), () =>
                      bind(lazy(term), (body) =>
                        pure(Abs(name, body /*, typ*/))
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  );

// application is a parser for function application `f(x)`; `f(x)(y)`; `f (x(t))`.
export const application = (term: () => Parser<Term>): Parser<App> =>
  // f(x) or (some term)(x)
  bind(either(reference, parenthesis(lazy(term))), (lhs) =>
    // allow `f(x)` and `f (x)`.
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
        const expr = terms.slice(2).reduce<App>(
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
    )
  );

//  true -> false
const caseBranch: Parser<Branch> = orFail(
  "case branch not well formed",
  bind(spaces, (_) =>
    bind(identifier, (id) =>
      bind(many(whitespace), (_) =>
        bind(str("->"), (_) =>
          bind(many(whitespace), (_) => bind(term, (t) => pure(Branch(id, t))))
        )
      )
    )
  )
);

// case b of
//  true -> false
//  false -> true
export const caseStatement: Parser<Case> = bind(str("case"), (_) =>
  bind(spc1(identifier), (id) =>
    bind(str("of"), (_) =>
      bind(newline, (_) =>
        bind(many1(caseBranch), (branches) => pure(Case(Ref(id), branches)))
      )
    )
  )
);

// term is a parser for terms in the programming language - i.e. the expressions
// that can be evaluated.
export const term: Parser<Term> = any4(
  // abstraction `λx.t`
  abstraction(() => term),
  // application `f(x)`
  application(() => term),
  caseStatement,
  // a reference for example `t`
  reference
);

// definition parses a top-level function definition, for example
// `func id: A->A = λx.x`.
export const definition: Parser<Def> = bind(str("func"), (_) =>
  bind(many1(whitespace), (_) =>
    bind(identifier, (name) =>
      bind(many(whitespace), (_) =>
        bind(char(":"), (_) =>
          bind(many(whitespace), (_) =>
            bind(type, (typ) =>
              bind(spaces, (_) =>
                bind(char("="), (_) =>
                  bind(spaces, (_) =>
                    bind(term, (tm) => pure(Def(name, tm, typ)))
                  )
                )
              )
            )
          )
        )
      )
    )
  )
);

// argument parses a single argument, i.e. `identifier Type`.
export const argument: Parser<Argument> = bind(identifier, (name) =>
  bind(spaces, (_) => bind(type, (typ) => pure(Argument(name, typ))))
);

// argumentList parses a list of arguments, i.e. `(a A, ..., z Z)`.
export const argumentList: Parser<Argument[]> = bind(
  parenthesis(join(argument, spc(char(",")))),
  (args) => pure(args)
);

// name(arg1 ArgType1, ..., ArgN ArgTypeN)
export const constructor: Parser<Constructor> = bind(identifier, (name) =>
  bind(many(whitespace), (_) =>
    bind(optional(argumentList), (args) => pure(Constructor(name, args || [])))
  )
);

// adt parses an abstract data type, for example
// `type List(A *) = nil | cons(head A, tail List(A))`
export const adt: Parser<ADT> = bind(str("type"), (_) =>
  bind(spaces, (_) =>
    bind(constructor, (c) =>
      bind(optional(spaces), (_) =>
        bind(char("="), (_) =>
          bind(optional(spaces), (_) =>
            bind(join1(constructor, spc(char("|"))), (ctrs) =>
              pure(ADT(c.name, c.args, ctrs))
            )
          )
        )
      )
    )
  )
);

const parseWhitespace: Parser<Space> = map(whitespace, () => ({ _: "sp" }));
const parseNewline: Parser<Newline> = map(newline, () => ({ _: "nl" }));

// parseFile is a parser for a source file.
export const parseFile: Parser<File> = map(
  consumeAll(
    many(
      any6(
        parseWhitespace,
        parseNewline,
        parsePackage,
        definition,
        adt,
        parseLineComment
      )
    )
  ),
  (r) => ({ _: "file", content: r })
);

export function getDeBruijinIndex(ctx: Context, name: string): number {
  let idx = -1;
  for (let i = 0; i < ctx.length; i++) {
    if (ctx[i].name == name) {
      idx = i;
      break;
    }
  }
  // binder not found in context.
  if (idx == -1) {
    console.error("failed to find binder for " + name);
  }
  return ctx.length - 1 - idx;
}

// export function transformDebruijin(term: Term, ctx: Context = []): Term {
//   switch (term._) {
//     case "app":
//       return App(
//         transformDebruijin(term.left, ctx),
//         transformDebruijin(term.right, ctx)
//       );
//     case "lam": {
//       // Where do we get this type from then?
//       const newCtx = addTermToCtx(ctx, term.name, term.bindType);
//       return Abs(term.name, transformDebruijin(term.body, newCtx));
//     }
//     case "var":
//       return term;
//     case "ann":
//       return Ann(transformDebruijin(term.term, ctx), term.typ);
//     case "ref":
//       // If this name exists in the context then compute its index. If it
//       // doesn't exist, leave it as a ref.
//       if (ctx.some((x) => x.name == term.name)) {
//         return Var(term.name, getDeBruijinIndex(ctx, term.name));
//       } else {
//         return term;
//       }
//   }
// }

// export function transformDebruijinT(term: Type, ctx: Context = []): Type {
//   switch (term._) {
//     case "pi":
//       return Pi(transformDebruijinT(term.from), transformDebruijinT(term.to));
//     case "var":
//       return term;
//     case "ref":
//       // If this name exists in the context then compute its index. If it
//       // doesn't exist, leave it as a ref.
//       if (ctx.some((x) => x.name == term.name)) {
//         return Var(term.name, getDeBruijinIndex(ctx, term.name));
//       } else {
//         return term;
//       }
//   }
// }
