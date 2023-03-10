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
export const head = <T>(l: T[]) => l[0];

// tail gives all elements of a list except the head.
export const tail = <T>(l: T[]) => l.slice(1);

// last gives the last element of a list.
export const last = <T>(l: T[]) => l[l.length - 1];

// front gives all elements of a list except the last element.
export const front = <T>(l: T[]) => l.slice(0, -1);

// Stream tracks where a parser is currently reading.
export type Stream = {
  src: string;

  // The index of the reader within the src string.
  idx: number;
};

// s constructs a new stream from a string.
export const s = (s: string): Stream => ({ src: s, idx: 0 });

// A successful parse result.
export interface OutputValue<T> {
  type: "outputvalue";
  stream: Stream;
  value: T;
}

// Parse error with its location.
export interface ParseError {
  type: "parseerror";
  stream: Stream;
  error: string;
}

export type Result<T> = OutputValue<T> | ParseError;

export type Parser<T> = (s: Stream) => Result<T>;

// pure is a parser that succeeds without consuming any of the input string, and
// returns the single result x.
export const pure =
  <A>(x: A): Parser<A> =>
  (s: Stream): Result<A> => ({
    type: "outputvalue",
    stream: s,
    value: x,
  });

// bind allows sequencing/chaining of parsers. If the first parser succeeds, the
// resulting value is passed to f, however if the parser fails the error is
// returned immediately. This allows users to form chains of bind callbacks that
// behave naturally in the presence of parse errors:
//
//   bind(p1, (v1) => bind(p2, (v2) => ...))
//
export const bind =
  <A, B>(p: Parser<A>, f: (v: A) => Parser<B>): Parser<B> =>
  (input: Stream) => {
    const parsed = p(input);
    if (parsed.type == "outputvalue") {
      return f(parsed.value)(parsed.stream);
    } else {
      return parsed;
    }
  };

// seq sequences two parsers one after another and returns both of their
// results.
export const seq = <P, Q>(p: Parser<P>, q: Parser<Q>): Parser<[P, Q]> =>
  bind(p, (x) => bind(q, (y) => pure([x, y])));

// seq3 is the same as seq. This is so typescript can infer the type arguments.
export const seq3 = <P, Q, R>(
  p: Parser<P>,
  q: Parser<Q>,
  r: Parser<R>
): Parser<[P, Q, R]> =>
  bind(p, (x) => bind(q, (y) => bind(r, (z) => pure([x, y, z]))));

// zero constructs a parser that always fails with the message err.
export const zero =
  <T>(err: string): Parser<T> =>
  (s: Stream) => ({
    type: "parseerror",
    stream: s,
    error: err,
    idx: s.idx,
  });

// error constructs a parser that always fails and returns an error message
// indicating what it expected.
export const error =
  <T>(expected: string): Parser<T> =>
  (s: Stream) => ({
    type: "parseerror",
    stream: s,
    error: `expected "${expected}"; got "${s.src[s.idx]}"`,
    idx: s.idx,
  });

// advance increments returns the stream s incremented by n characters.
export const advance = (n: number, s: Stream): Stream => ({
  src: s.src,
  idx: s.idx + n,
});

// pos returns the stream s with the position reset to character n.
export const pos = (n: number, s: Stream): Stream => ({
  src: s.src,
  idx: n,
});

// item reads a single character from the stream and advances the stream by one
// character.
export const item: Parser<string> = (cs) =>
  cs.idx < cs.src.length
    ? {
        type: "outputvalue",
        stream: advance(1, cs),
        value: cs.src[cs.idx],
      }
    : {
        type: "parseerror",
        stream: cs,
        error: "EOF",
        idx: cs.idx,
      };

// reads a single character then checks whether it satisfies the given
// predicate.
export const sat = (p: (x: string) => boolean) =>
  bind(item, (x) => (p(x) ? pure(x) : zero<string>("not satisfied")));

export const digit = sat((x) => x >= "0" && x <= "9");
export const lower = sat((x) => x >= "a" && x <= "z");
export const upper = sat((x) => x >= "A" && x <= "Z");

// char matches a single character.
export const char = (c: string): Parser<string> =>
  bind(item, (x) => (x === c ? pure(x) : error(c)));

// str returns a Parser that matches on the provided string.
export const str = (st: string): Parser<string> =>
  st == ""
    ? pure("")
    : orFail(
        `expected ${st}`,
        bind(char(st[0]), (x) => bind(str(st.substring(1)), (y) => pure(x + y)))
      );

// identity is an parser that does the same as parser.
const identity = <T>(parser: Parser<T>): Parser<T> => {
  return (s: Stream) => {
    return parser(s);
  };
};

// either is successful if p1 or p2 are successful.
export const either =
  <A, B>(p1: Parser<A>, p2: Parser<B>): Parser<A | B> =>
  (input): Result<A | B> => {
    const left = p1(input);
    if (left.type == "outputvalue") {
      return left;
    }
    return p2(input);
  };

// alpha is a Parser that matches a single upper, or lower case character.
export const alpha = either(lower, upper);

// any succeeds if any of the given parsers succeed.
export const any = <T>(...ps: Parser<T>[]): Parser<T> =>
  ps.reduce((p1, p2) => either(p1, p2));

// see any
export const any3 = <A, B, C>(p1: Parser<A>, p2: Parser<B>, p3: Parser<C>) =>
  either(p1, either(p2, p3));

// see any
export const any4 = <A, B, C, D>(
  p1: Parser<A>,
  p2: Parser<B>,
  p3: Parser<C>,
  p4: Parser<D>
) => either(p1, either(p2, either(p3, p4)));

// see any
export const any5 = <A, B, C, D, E>(
  p1: Parser<A>,
  p2: Parser<B>,
  p3: Parser<C>,
  p4: Parser<D>,
  p5: Parser<E>
) => either(p1, either(p2, either(p3, either(p4, p5))));

// see any
export const any6 = <A, B, C, D, E, F>(
  p1: Parser<A>,
  p2: Parser<B>,
  p3: Parser<C>,
  p4: Parser<D>,
  p5: Parser<E>,
  p6: Parser<F>
) => either(p1, either(p2, either(p3, either(p4, either(p5, p6)))));

// optional returns a parser that attempts to use the supplied parser, but
// if it fails it doesn't return a parse error and instead allows the parsing to
// continue.
export const optional = <T>(parser: Parser<T>): Parser<T | null> =>
  either(parser, pure(null));

// Parses as many times as possible, but at least once.
export const many1 = <A>(p: Parser<A>): Parser<A[]> =>
  // Run the parser once initially and fail immediately if it's not possible.
  bind(p, (x) =>
    // Then parse as many times as possible.
    bind(many(p), (xs) =>
      // Combine all the values into a list.
      pure([x, ...xs])
    )
  );

// Parses as many times as possible, including zero.
export const many = <T>(parser: Parser<T>) =>
  // Either return at least one element from the parser, or return an empty
  // list.
  either(many1(parser), pure<T[]>([]));

// join1 runs the first parser and the separator many times. Requires at least
// one element.
export const join1 = <T, S>(parser: Parser<T>, separator: Parser<S>) =>
  // Parse the first element.
  bind(parser, (x) =>
    // Then parse the separator followed by another element, many times.
    bind(many(bind(separator, (_) => bind(parser, (x) => pure(x)))), (xs) =>
      pure([x].concat(xs))
    )
  );

// join runs the first parser and the separator many times.
export const join = <T, S>(parser: Parser<T>, separator: Parser<S>) =>
  // Either return at least one element from the parser, or return an empty
  // list.
  either(join1(parser, separator), pure<T[]>([]));

// oneOf matches a single character from any of the characters in the string.
export const oneOf = (str: string): Parser<string> =>
  any(...str.split("").map(char));

// If the parser succeeds, run it's matched value through the function.
export const map = <S, T>(parser: Parser<T>, f: (t: T) => S) =>
  bind(parser, (x) => pure(f(x)));

// line matches until either a newline character is encountered, or EOF.
export const line: Parser<string> = bind(
  many1(sat((c) => c !== "\n")),
  (chars) =>
    bind(
      // consume the newline, if it exists (could be EOF).
      optional(item),
      (_) => pure(chars.join(""))
    )
);

export const whitespace = char(" ");
export const newline = char("\n");

// spaces parses required whitespace (spaces and newlines)
export const spaces = many1(either(whitespace, newline));

// spc is a parser that allows optional leading and trailing whitespace.
export const spc = <T>(between: Parser<T>): Parser<T> =>
  bind(optional(spaces), (_) =>
    bind(between, (x) => bind(optional(spaces), (_) => pure(x)))
  );

// spc1 is a parser that requires leading and trailing whitespace.
export const spc1 = <T>(between: Parser<T>): Parser<T> =>
  bind(spaces, (_) => bind(between, (x) => bind(spaces, (_) => pure(x))));

// orFail raises a specific parse error if the parser is unsuccessful.
export const orFail = <A>(msg: string, p: Parser<A>): Parser<A> =>
  either(p, zero<A>(msg));

// lazy is a parser that takes a parser generator and generates the parser at
// parse-time rather than when constructing the parsers. This allows for
// recursive parsers to be defined.
export const lazy =
  <T>(g: () => Parser<T>): Parser<T> =>
  (input): Result<T> =>
    // Create this parser lazily at parse-time.
    g()(input);

// consumeAll raises a parse error if the parser doesn't consume all of its
// input.
export const consumeAll = <T>(parser: Parser<T>): Parser<T> => {
  return function (input) {
    const result = parser(input);

    if (
      result.type == "outputvalue" &&
      result.stream.idx < result.stream.src.length
    ) {
      return zero<T>("unexpected input")(result.stream);
    }

    return result;
  };
};

// Loc is a location in a source file.
type Loc = {
  col: number;
  line: number;
};

// Range is a span of locations in a source file.
export type Range = {
  begin: Loc;
  end: Loc;
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

export const printLine = (src: string, line: number) => src.split("\n")[line];

export const parseErrorDiagnostic = (err: ParseError) => {
  const lc = indexToLineCol(err.stream.src, err.stream.idx);
  return (
    `error at line ${lc.line} col ${lc.col}: ${err.error}\n` +
    `  ${printLine(err.stream.src, lc.line)}\n` +
    `  ${" ".repeat(lc.col)}^`
  );
};
