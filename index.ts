#!/usr/bin/env ./node_modules/.bin/ts-node-script

// Parser for a programming language. The parser takes as input a source file as
// a string and, if successful, spits out an AST that describes the file.
//
// The next step from here is to resolve references, both internally and any
// external references and ensure they're available. This should probably use a
// configuration file that specifies which module the current package is inside
// and which versions of dependencies have been pinned.
//
// We must then type-check the AST to ensure consistency.

// head gives the first element of a list.
const head = (l: any[]) => l[0];

// tail gives all elements of a list except the head.
const tail = (l: any[]) => l.splice(1);

// Stream tracks where a parser is currently reading.
export type Stream = {
  src: string;

  // The index of the reader within the src string.
  idx: number;

  // If true, attach origin information to the parse tree.
  origins: boolean;
};

// s constructs a new stream from a string.
export const s = (s: string): Stream => ({ src: s, idx: 0, origins: true });

// A successful parse result.
export interface OutputValue {
  type: "outputvalue";
  stream: Stream;
  value: any;
}

// Parse error with its location.
export interface ParseError {
  type: "parseerror";
  error: string;
  idx: number;
}

export type Result = OutputValue | ParseError;
export type Parser = (s: Stream) => Result;
export type ParserGenerator = (s: string) => Parser;

// line matches until either a newline character is encountered, or EOF.
export const line: Parser = ({ src, idx, origins }) => {
  let n = src.indexOf("\n", idx);
  if (n == -1) {
    n = src.length;
  }

  return {
    type: "outputvalue",
    stream: { src, idx: n + 1, origins: origins },
    value: src.substring(idx, n),
  };
};

// char matches a single character.
export const char: ParserGenerator =
  (c) =>
  ({ src, idx, origins }) =>
    c === src?.[idx]
      ? {
          type: "outputvalue",
          stream: { src, idx: idx + 1, origins },
          value: src[idx],
        }
      : {
          type: "parseerror",
          error: `expected "${c}"; got "${src?.[idx]}"`,
          idx: idx,
        };

// str returns a Parser that matches on the provided string.
export const str: ParserGenerator =
  (s) =>
  ({ src, idx, origins }) =>
    src.startsWith(s, idx)
      ? {
          type: "outputvalue",
          stream: { src, idx: idx + s.length, origins },
          value: s,
        }
      : {
          type: "parseerror",
          error: `expected "${s}"; got "${src.substring(idx, idx + s.length)}"`,
          idx: idx,
        };

type Combinator = (...parsers: Parser[]) => Parser;

// identity is an example parser combinator that does nothing.
const identity: Combinator = (parser: Parser): Parser => {
  return (s: Stream) => {
    return parser(s);
  };
};

// choice is successful if either of the two parsers are successful.
export const choice: Combinator = (p1, p2) => (input) => {
  const left = p1(input);
  if (left.type == "outputvalue") {
    return left;
  }
  return p2(input);
};

// and combines two parsers in order.
export const and: Combinator = (p1, p2) => (input) => {
  const r = p1(input);
  if (r.type == "outputvalue") {
    const r2 = p2(r.stream);
    if (r2.type == "outputvalue") {
      return {
        type: "outputvalue",
        stream: r2.stream,
        value: [r.value, r2.value].flat(),
      };
    } else {
      return r2;
    }
  } else {
    return r;
  }
};

// any succeeds if any of the given parsers succeed.
export const any: Combinator = (...ps) => ps.reduce((p1, p2) => choice(p1, p2));

// optional returns a parser that attempts to use the supplied parser, but
// if it fails it doesn't return a parse error and instead allows the parsing to
// continue.
export const optional: Combinator = (parser) => (input) => {
  const result = parser(input);

  if (result.type == "parseerror") {
    // Return success, but continue from the same starting position.
    return {
      type: "outputvalue",
      stream: input,
      value: null,
    };
  }

  return {
    type: "outputvalue",
    stream: result.stream,
    value: result.value,
  };
};

// Parses as many times as possible, but at least once.
export const many: Combinator = (parser) => (input) => {
  const result = parser(input);

  if (result.type == "parseerror") {
    return result;
  }

  // Run the parser again and if it succeeds combine the results.
  const next = many(parser)(result.stream);
  if (next.type == "parseerror") {
    return {
      type: "outputvalue",
      stream: result.stream,
      value: [result.value],
    };
  }

  return {
    type: "outputvalue",
    stream: next.stream,
    value: [result.value, next.value].flat(),
  };
};

// anyChar matches a character from the string of characters.
export const anyChar: ParserGenerator =
  (str): Parser =>
  (input) =>
    any(...str.split("").map(char))(input);

// andThen combines multiple parsers in order.
export const andThen: Combinator = (...ps) =>
  ps.reduce((p1, p2) => and(p1, p2));

// If the parser succeeds, run it's matched value through the function.
export const map =
  (parser: Parser, fn: Function) =>
  (input: Stream): Result => {
    const out = parser(input);

    if (out.type == "parseerror") {
      return out;
    }

    return {
      type: "outputvalue",
      stream: out.stream,
      value: fn(out.value),
    };
  };

const digit = anyChar("0123456789");

const alpha = anyChar("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ");

const quote = char(`"`);
const whitespace = char(" ");
const newline = char("\n");

// identifier parses a letter from the alphabet followed by letters, numbers and
// other allowed special characters.
export const identifier = map(
  andThen(
    alpha,
    map(optional(many(any(alpha, digit, anyChar("_")))), (r: any[] | null) => {
      if (r == null) {
        return "";
      }
      return r.join("");
    })
  ),
  (v: string[]) => {
    return v.join("");
  }
);

// block is a parser that adds origin information into the parse tree. It can be
// disabled by setting origins to false in the stream.
export const block: Combinator = (parser: Parser): Parser => {
  return (s: Stream): Result => {
    const start = s.idx;
    const result = parser(s);

    if (result.type == "parseerror") {
      return result;
    }

    if (!s.origins) {
      return result;
    }

    return {
      type: "outputvalue",
      stream: result.stream,
      value: {
        type: "ori",
        start: start,
        end: result.stream.idx,
        child: result.value,
      },
    };
  };
};

// parsePackage parses a package declaration such as `package abc`.
export const parsePackage = map(
  andThen(
    str("package"),
    whitespace,
    block(map(identifier, (r: string) => ({ type: "pkg", name: r })))
  ),
  (r: any[]) => r[2]
);

// parseLineComment parses an end-of-line comment and stops either at the end of
// the line or EOF.
export const parseLineComment = block(
  map(andThen(str("//"), line), (r: any[]) => ({
    type: "com",
    text: r[1],
  }))
);

// reference parses a "variable" in the programming language.
export const reference = block(
  map(identifier, (result: any) => ({
    type: "ref",
    name: result,
  }))
);

// lazy is a parser that takes a parser generator and generates the parser at
// parse-time rather than when constructing the parsers. This allows for
// recursive parsers to be defined.
export const lazy =
  (g: () => Parser): Parser =>
  (input): Result =>
    // Create this parser lazily at parse-time.
    g()(input);

// abstraction parses a lambda abstraction `λx.t`.
export const abstraction = (term: () => Parser) =>
  block(
    map(
      andThen(
        char("λ"),
        optional(whitespace),
        identifier,
        optional(whitespace),
        char("."),
        optional(whitespace),
        lazy(term)
      ),
      (result: any[]) => ({ type: "lam", name: result[2], body: result[6] })
    )
  );

// parenthesis is a parser that requires an opening and closing parenthesis to
// surround the given parser.
export const parenthesis = (between: Parser): Parser =>
  map(andThen(char("("), between, char(")")), (r: any) => {
    return r[1];
  });

// application is a parser for function application `f(x)`; `f(x)(y)`; `f (x(t))`.
export const application = (term: () => Parser): Parser =>
  block(
    map(
      andThen(
        // f(x) or (some term)(x)
        choice(reference, parenthesis(lazy(term))),
        // allow `f(x)` and `f (x)`.
        optional(whitespace),
        // args
        map(many(parenthesis(lazy(term))), (r: any) => {
          return [r];
        })
      ),
      (result: any[]) => {
        const terms = [result[0], result[2]].flat();
        // Application is left-associative, so form the following tree of
        // applications, i.e. f(x)(y) == (f(x))(y):
        //      ap
        //     /  \
        //    ap   y
        //   /  \
        //  f    x
        return tail(terms).reduce(
          (prev, curr) => ({
            type: "app",
            name: prev,
            arg: curr,
          }),
          head(terms)
        );
      }
    )
  );

// term is a parser for terms in the programming language - i.e. the expressions
// that can be evaluated.
export const term = any(
  // abstraction `λx.t`
  abstraction(() => term),
  // application `f(x)`
  application(() => term),
  // a reference for example `t`
  reference
);

// definition parses a top-level function definition, for example
// `func id = λx.x`.
export const definition = block(
  map(
    andThen(
      str("func"),
      whitespace,
      identifier,
      whitespace,
      char("="),
      whitespace,
      term
    ),
    (r: any[]) => ({ type: "def", name: r[2], term: r[6] })
  )
);

// consumeAll raises a parse error if the parser doesn't consume all of its
// input.
export const consumeAll = (parser: Parser): Parser => {
  return function (input) {
    const result = parser(input);

    if (
      result.type == "outputvalue" &&
      result.stream.idx < result.stream.src.length
    ) {
      return {
        type: "parseerror",
        idx: result.stream.idx,
        error: "unexpected input",
      };
    }

    return result;
  };
};

// parseFile is a parser for a source file.
export const parseFile = map(
  consumeAll(
    many(
      any(
        map(whitespace, () => ({ type: "sp" })),
        map(newline, () => ({ type: "nl" })),
        parsePackage,
        definition,
        parseLineComment
      )
    )
  ),
  (r: any[]) => ({ type: "file", content: r })
);

// Loc is a location in a source file.
type Loc = {
  col: number;
  line: number;
};

// indexToLineCol converts an index into a pair (line,col) describing the line
// number and character where idx appears in src.
export const indexToLineCol = (src: string, idx: number) =>
  src
    .split("")
    .slice(0, idx)
    .reduce(
      (accumulator: Loc, char: string) => {
        // While scanning through the string check for newlines and update the
        // counters.
        if (char == "\n") {
          return { col: 0, line: accumulator.line + 1 };
        } else {
          return { col: accumulator.col + 1, line: accumulator.line };
        }
      },
      { col: 0, line: 0 }
    );
