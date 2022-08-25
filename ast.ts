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
} from ".";

type Type = Arrow | Ref;

type Arrow = {
  type: "arrow";
  from: Type;
  to: Type;
};

type Abs = {
  type: "lam";
  name: string; // name of the binder
  typ: Type; // type of the bound variable
  body: Term; // the body of the lambda
};

type App = {
  type: "app";
  name: Term;
  arg: Term;
};

type Ref = {
  type: "ref";
  name: string;
};

type Term = Abs | App | Ref;

type Def = {
  type: "def";
  name: string;
  term: Term;
  typ: Type;
};

type Pkg = { type: "pkg"; name: string };

type Com = { type: "com"; text: string };

type Space = { type: "sp" };
type Newline = { type: "nl" };

type File = { type: "file"; content: (Pkg | Com | Def | Space | Newline)[] };

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
  type: "ori";
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
      type: "ori",
      start: start,
      end: result.stream.idx,
      child: result.value,
    };
    return pure(origin)(result.stream);
  };

// parsePackage parses a package declaration such as `package abc`.
export const parsePackage: Parser<Pkg> = bind(str("package"), (_) =>
  bind(whitespace, (_) =>
    bind(identifier, (a) => pure({ type: "pkg", name: a }))
  )
);

// parseLineComment parses an end-of-line comment and stops either at the end of
// the line or EOF.
export const parseLineComment: Parser<Com> = bind(str("//"), (_) =>
  bind(line, (l) =>
    pure({
      type: "com",
      text: l,
    })
  )
);

// reference parses a "variable" in the programming language.
export const reference: Parser<Ref> = map(identifier, (result: string) => ({
  type: "ref",
  name: result,
}));

// parenthesis is a parser that requires an opening and closing parenthesis to
// surround the given parser.
export const parenthesis = <T>(between: Parser<T>): Parser<T> =>
  bind(char("("), (_) => bind(between, (x) => bind(char(")"), (_) => pure(x))));

export const arrow: (
  type: () => Parser<Type>
) => (s: Stream) => Result<Arrow> = (type) =>
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
          pure({
            type: "arrow",
            from: lhs,
            to: front(r).reduceRight(
              (prev, curr) => ({
                type: "arrow",
                from: curr,
                to: prev,
              }),
              last(r)
            ),
          })
      )
  );

export const type: Parser<Type> = any3(
  arrow(() => type),
  parenthesis(lazy(() => type)),
  reference
);

// // abstraction parses a lambda abstraction `λx:X. t`.
export const abstraction = (term: () => Parser<Term>): Parser<Abs> =>
  bind(char("λ"), (_) =>
    bind(optional(whitespace), (_) =>
      bind(identifier, (name) =>
        bind(optional(whitespace), (_) =>
          bind(char(":"), (_) =>
            bind(optional(whitespace), (_) =>
              bind(type, (typ) =>
                bind(optional(whitespace), () =>
                  bind(char("."), () =>
                    bind(optional(whitespace), () =>
                      bind(lazy(term), (body) =>
                        pure({
                          type: "lam",
                          name: name, // name of the binder
                          typ: typ, // type of the bound variable
                          body: body, // the body of the lambda
                        })
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
            type: "app",
            name: acc,
            arg: t,
          }),
          {
            type: "app",
            name: terms[0],
            arg: terms[1],
          }
        );

        return pure(expr);
      })
    )
  );

// term is a parser for terms in the programming language - i.e. the expressions
// that can be evaluated.
export const term: Parser<Term> = any3(
  // abstraction `λx.t`
  abstraction(() => term),
  // application `f(x)`
  application(() => term),
  // a reference for example `t`
  reference
);

// definition parses a top-level function definition, for example
// `func id = λx.x`.
export const definition: Parser<Def> = bind(str("func"), (_) =>
  bind(whitespace, (_) =>
    bind(identifier, (name) =>
      bind(optional(whitespace), (_) =>
        bind(char(":"), (_) =>
          bind(optional(whitespace), (_) =>
            bind(type, (typ) =>
              bind(optional(whitespace), (_) =>
                bind(char("="), (_) =>
                  bind(whitespace, (_) =>
                    bind(term, (tm) =>
                      pure({
                        type: "def",
                        name: name,
                        term: tm,
                        typ: typ,
                      })
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

const parseWhitespace: Parser<Space> = map(whitespace, () => ({ type: "sp" }));
const parseNewline: Parser<Newline> = map(newline, () => ({ type: "nl" }));

// parseFile is a parser for a source file.
export const parseFile: Parser<File> = map(
  consumeAll(
    many(
      any5(
        parseWhitespace,
        parseNewline,
        parsePackage,
        definition,
        parseLineComment
      )
    )
  ),
  (r) => ({ type: "file", content: r })
);
