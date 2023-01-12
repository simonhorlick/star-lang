import {
  Abs,
  All,
  Ann,
  App,
  Arrow,
  Def,
  Ref,
  Star,
  TAbs,
  TApp,
  Var,
} from "./evaluation";
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
} from "./parser";

export type VariableBinding = { type: "bind"; name: string; typ: Type };
export type TypeVariableBinding = { type: "tbind"; name: string; kind: Kind };

export type Binding = VariableBinding | TypeVariableBinding;

export type Context = Binding[];

// A type that has been erased.
export type Erased = {
  _: "ers";
};

export type All = {
  _: "all";
  name: string;
  to: Type;
  kind: Kind; // The kind of the argument.
};

// KArrow (=>) is the kind of operators.
export type KArrow = {
  _: "karrow";
  from: Kind;
  to: Kind;
};

// Arrow is the type of functions.
export type Arrow = {
  _: "arrow";
  from: Type;
  to: Type;
};

// Abs is a lambda abstraction.
export type Abs = {
  _: "lam";
  name: string; // name of the binder
  bindType: Type; // type of the bound variable
  body: Term; // the body of the abstraction
};

// TAbs is a type abstraction. Types that occur within the body of
// this abstraction are substituted when an application occurs.
export type TAbs = {
  _: "tabs";
  name: string; // name of the binder
  body: Term; // the body of the abstraction
  kind: Kind; // the kind of the type abstraction
};

// App is a function application.
export type App = {
  _: "app";
  left: Term;
  right: Term;
};

// TApp is a type application. We use Abs to abstract terms out of terms and
// App to supply values for the variables we've abstracted out. TAbs is a way
// of abstracting types out of terms so that we can use TApp to substitute
// them back in later. When doing evaluation we can reduce a type abstraction
// and a type application using the E-TappTabs rule, this will give us back a
// term.
export type TApp = {
  _: "tapp";
  left: Term;
  right: Type;
};

// A bound variable.
export type Var = {
  _: "var";

  // The variable name for pretty printing.
  name: string;

  // The de Bruijn index of this node. The number index stands for “the variable
  // bound by the index’th enclosing λ.”
  index: number;
};

// A reference.
export type Ref = {
  _: "ref";

  // The name of the definition being referenced.
  name: string;
};

// ★ is the kind of proper types.
export type Star = {
  _: "star";
};

// A type annotation.
export type Ann = {
  _: "ann";

  // The term this annotation applies to.
  term: Term;

  // The annotated type.
  typ: Type;
};

export type Kind = KArrow | Star;

export type Type = Arrow | Ref | Erased | Var | All;

export type Term = Abs | App | TAbs | TApp | Var | Ref | Ann;

// A top-level definition.
export type Def = {
  _: "def";
  name: string;
  term: Term;
  typ: Type;
};

export type Pkg = { _: "pkg"; name: string };

export type Com = { _: "com"; text: string };

export type Space = { _: "sp" };
export type Newline = { _: "nl" };

export type File = {
  _: "file";
  content: (Pkg | Com | Def | Space | Newline)[];
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
  bind(whitespace, (_) => bind(identifier, (a) => pure({ _: "pkg", name: a })))
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
            _: "arrow",
            from: lhs,
            to: front(r).reduceRight(
              (prev, curr) => Arrow(curr, prev),
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
                      bind(lazy(term), (body) => pure(Abs(name, body, typ)))
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

const parseWhitespace: Parser<Space> = map(whitespace, () => ({ _: "sp" }));
const parseNewline: Parser<Newline> = map(newline, () => ({ _: "nl" }));

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
