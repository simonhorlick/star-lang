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
  _: "outputvalue";
  stream: Stream;
  value: T;
}

// Parse error with its location.
export interface FatalParseError {
  _: "parseerror";
  stream: Stream;
  error: string;
}

export type Result<T> = OutputValue<T> | FatalParseError;

export type Parser<T> = (s: Stream) => Result<T>;

// pure is a parser that succeeds without consuming any of the input string, and
// returns the single result x.
export function pure<A>(x: A): Parser<A> {
  return (s: Stream): Result<A> => ({
    _: "outputvalue",
    stream: s,
    value: x,
  });
}

// bind allows sequencing/chaining of parsers. If the first parser succeeds, the
// resulting value is passed to f, however if the parser fails the error is
// returned immediately. This allows users to form chains of bind callbacks that
// behave naturally in the presence of parse errors:
//
//   bind(p1, (v1) => bind(p2, (v2) => ...))
//
export function bind<A, B>(p: Parser<A>, f: (v: A) => Parser<B>): Parser<B> {
  return (input: Stream): Result<B> => {
    const parsed = p(input);
    if (parsed._ == "outputvalue") {
      return f(parsed.value)(parsed.stream);
    } else {
      return parsed;
    }
  };
}

// seq sequences two parsers one after another and returns both of their
// results.
export function seq<P, Q>(p: Parser<P>, q: Parser<Q>): Parser<[P, Q]> {
  return bind(p, (x) => bind(q, (y) => pure([x, y])));
}

// seq3 is the same as seq. This is so typescript can infer the type arguments.
export function seq3<P, Q, R>(
  p: Parser<P>,
  q: Parser<Q>,
  r: Parser<R>
): Parser<[P, Q, R]> {
  return bind(p, (x) => bind(q, (y) => bind(r, (z) => pure([x, y, z]))));
}

// zero constructs a parser that always fails with the message err.
export function zero<T>(err: string): Parser<T> {
  return (s: Stream): Result<T> => ({
    _: "parseerror",
    stream: s,
    error: err,
  });
}

// error constructs a parser that always fails and returns an error message
// indicating what it expected.
export function error<T>(expected: string): Parser<T> {
  return (s: Stream): Result<T> => {
    // console.log(`expected "${expected}"; got "${s.src[s.idx]}"`);
    return {
      _: "parseerror",
      stream: s,
      error: `expected "${expected}"; got "${s.src[s.idx]}"`,
    };
  };
}

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
export const item: Parser<string> = (cs: Stream): Result<string> => {
  return cs.idx < cs.src.length
    ? {
        _: "outputvalue",
        stream: advance(1, cs),
        value: cs.src[cs.idx],
      }
    : {
        _: "parseerror",
        stream: cs,
        error: "EOF",
      };
};

// reads a single character then checks whether it satisfies the given
// predicate.
export function sat(p: (x: string) => boolean): Parser<string> {
  return bind(item, (x) => (p(x) ? pure(x) : zero<string>("not satisfied")));
}

export const digit = sat((x) => x >= "0" && x <= "9");
export const lower = sat((x) => x >= "a" && x <= "z");
export const upper = sat((x) => x >= "A" && x <= "Z");

// char matches a single character.
export function char(c: string): Parser<string> {
  return bind(item, (x) => (x === c ? pure(x) : error(c)));
}

// str returns a Parser that matches on the provided string.
export function str(st: string): Parser<string> {
  return st == ""
    ? pure("")
    : orFail(
        `expected ${st}`,
        bind(char(st[0]), (x) => bind(str(st.substring(1)), (y) => pure(x + y)))
      );
}

// until returns a Parser that fails if the provided parser succeeds and
// succeeds otherwise. This parser does not advance the stream. See `takeUntil`.
export const until =
  <T>(st: Parser<T>): Parser<string> =>
  (s: Stream): Result<string> => {
    const p1 = st(s);
    // The stream matches.
    if (p1._ == "outputvalue") {
      // Return failure, do not advance the stream.
      return {
        _: "parseerror",
        stream: s,
        error: `encountered match`,
      };
    } else {
      // No match so return success and advance by 1 character.
      return item(s);
    }
  };

export const takeUntil = <T>(p: Parser<T>) =>
  map(many(until(p)), (x: string[]) => x.join(""));

// identity is a parser that does the same as parser.
function identity<T>(parser: Parser<T>): Parser<T> {
  return (s: Stream) => {
    return parser(s);
  };
}

// either is successful if p1 or p2 are successful.
export function either<A, B>(p1: Parser<A>, p2: Parser<B>): Parser<A | B> {
  return (input): Result<A | B> => {
    const left = p1(input);
    if (left._ == "outputvalue") {
      return left;
    }
    return p2(input);
  };
}

// alpha is a Parser that matches a single upper, or lower case character.
export const alpha = either(lower, upper);

// any succeeds if any of the given parsers succeed.
export function any<T>(...ps: Parser<T>[]): Parser<T> {
  return ps.reduce((p1, p2) => either(p1, p2));
}

// see any
export function any3<A, B, C>(p1: Parser<A>, p2: Parser<B>, p3: Parser<C>) {
  return either(p1, either(p2, p3));
}

// see any
export function any4<A, B, C, D>(
  p1: Parser<A>,
  p2: Parser<B>,
  p3: Parser<C>,
  p4: Parser<D>
) {
  return either(p1, either(p2, either(p3, p4)));
}

// see any
export function any5<A, B, C, D, E>(
  p1: Parser<A>,
  p2: Parser<B>,
  p3: Parser<C>,
  p4: Parser<D>,
  p5: Parser<E>
) {
  return either(p1, either(p2, either(p3, either(p4, p5))));
}

// see any
export function any6<A, B, C, D, E, F>(
  p1: Parser<A>,
  p2: Parser<B>,
  p3: Parser<C>,
  p4: Parser<D>,
  p5: Parser<E>,
  p6: Parser<F>
) {
  return either(p1, either(p2, either(p3, either(p4, either(p5, p6)))));
}

// see any
export function any7<A, B, C, D, E, F, G>(
  p1: Parser<A>,
  p2: Parser<B>,
  p3: Parser<C>,
  p4: Parser<D>,
  p5: Parser<E>,
  p6: Parser<F>,
  p7: Parser<G>
) {
  return either(
    p1,
    either(p2, either(p3, either(p4, either(p5, either(p6, p7)))))
  );
}

// see any
export function any8<A, B, C, D, E, F, G, H>(
  p1: Parser<A>,
  p2: Parser<B>,
  p3: Parser<C>,
  p4: Parser<D>,
  p5: Parser<E>,
  p6: Parser<F>,
  p7: Parser<G>,
  p8: Parser<H>
) {
  return either(
    p1,
    either(p2, either(p3, either(p4, either(p5, either(p6, either(p7, p8))))))
  );
}

// see any
export function any9<A, B, C, D, E, F, G, H, I>(
  p1: Parser<A>,
  p2: Parser<B>,
  p3: Parser<C>,
  p4: Parser<D>,
  p5: Parser<E>,
  p6: Parser<F>,
  p7: Parser<G>,
  p8: Parser<H>,
  p9: Parser<I>
) {
  return either(
    p1,
    either(
      p2,
      either(p3, either(p4, either(p5, either(p6, either(p7, either(p8, p9))))))
    )
  );
}

// see any
export function any10<A, B, C, D, E, F, G, H, I, J>(
  p1: Parser<A>,
  p2: Parser<B>,
  p3: Parser<C>,
  p4: Parser<D>,
  p5: Parser<E>,
  p6: Parser<F>,
  p7: Parser<G>,
  p8: Parser<H>,
  p9: Parser<I>,
  p10: Parser<J>
) {
  return either(
    p1,
    either(
      p2,
      either(
        p3,
        either(
          p4,
          either(p5, either(p6, either(p7, either(p8, either(p9, p10)))))
        )
      )
    )
  );
}

// see any
export function any11<A, B, C, D, E, F, G, H, I, J, K>(
  p1: Parser<A>,
  p2: Parser<B>,
  p3: Parser<C>,
  p4: Parser<D>,
  p5: Parser<E>,
  p6: Parser<F>,
  p7: Parser<G>,
  p8: Parser<H>,
  p9: Parser<I>,
  p10: Parser<J>,
  p11: Parser<K>
) {
  return either(
    p1,
    either(
      p2,
      either(
        p3,
        either(
          p4,
          either(
            p5,
            either(p6, either(p7, either(p8, either(p9, either(p10, p11)))))
          )
        )
      )
    )
  );
}

// see any
export function any12<A, B, C, D, E, F, G, H, I, J, K, L>(
  p1: Parser<A>,
  p2: Parser<B>,
  p3: Parser<C>,
  p4: Parser<D>,
  p5: Parser<E>,
  p6: Parser<F>,
  p7: Parser<G>,
  p8: Parser<H>,
  p9: Parser<I>,
  p10: Parser<J>,
  p11: Parser<K>,
  p12: Parser<L>
) {
  return either(
    p1,
    either(
      p2,
      either(
        p3,
        either(
          p4,
          either(
            p5,
            either(
              p6,
              either(p7, either(p8, either(p9, either(p10, either(p11, p12)))))
            )
          )
        )
      )
    )
  );
}

export function any13<A, B, C, D, E, F, G, H, I, J, K, L, M>(
  p1: Parser<A>,
  p2: Parser<B>,
  p3: Parser<C>,
  p4: Parser<D>,
  p5: Parser<E>,
  p6: Parser<F>,
  p7: Parser<G>,
  p8: Parser<H>,
  p9: Parser<I>,
  p10: Parser<J>,
  p11: Parser<K>,
  p12: Parser<L>,
  p13: Parser<L>
) {
  return either(
    p1,
    either(
      p2,
      either(
        p3,
        either(
          p4,
          either(
            p5,
            either(
              p6,
              either(
                p7,
                either(
                  p8,
                  either(p9, either(p10, either(p11, either(p12, p13))))
                )
              )
            )
          )
        )
      )
    )
  );
}

// optional returns a parser that attempts to use the supplied parser, but
// if it fails it doesn't return a parse error and instead allows the parsing to
// continue.
export function optional<T>(parser: Parser<T>): Parser<T | null> {
  return either(parser, pure(null));
}

// Parses as many times as possible, but at least once.
export function many1<A>(p: Parser<A>): Parser<A[]> {
  return bind(p, (x) =>
    // Then parse as many times as possible.
    bind(many(p), (xs) =>
      // Combine all the values into a list.
      pure([x, ...xs])
    )
  );
}

// Parses as many times as possible, including zero.
export function many<T>(parser: Parser<T>) {
  return either(many1(parser), pure<T[]>([]));
}

// join1 runs the first parser and the separator many times. Requires at least
// one element.
export function join1<T, S>(parser: Parser<T>, separator: Parser<S>) {
  return bind(parser, (x) =>
    // Then parse the separator followed by another element, many times.
    bind(many(bind(separator, (_) => bind(parser, (x) => pure(x)))), (xs) =>
      pure([x].concat(xs))
    )
  );
}

// join runs the first parser and the separator many times.
export function join<T, S>(parser: Parser<T>, separator: Parser<S>) {
  return either(join1(parser, separator), pure<T[]>([]));
}

// oneOf matches a single character from any of the characters in the string.
export function oneOf(str: string): Parser<string> {
  return any(...str.split("").map(char));
}

// If the parser succeeds, run it's matched value through the function.
export function map<S, T>(parser: Parser<T>, f: (t: T) => S) {
  return bind(parser, (x) => pure(f(x)));
}

// skip the input while p is true.
export const skip = <T>(p: Parser<T>): Parser<T[]> => many(p);

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

// num parses an integer
export const num = map(many1(digit), (digits) =>
  Number.parseInt(digits.join(""))
);

export const whitespace = any(
  char(" "),
  char("\t"),
  char(String.fromCharCode(0x0a)) // line feed
);
export const newline = char("\n");

// spaces parses required whitespace (spaces and newlines)
export const spaces = many1(either(whitespace, newline));

// spc is a parser that allows optional leading and trailing whitespace.
export function spc<T>(between: Parser<T>): Parser<T> {
  return bind(optional(spaces), (_) =>
    bind(between, (x) => bind(optional(spaces), (_) => pure(x)))
  );
}

// lspc is a parser that allows optional leading whitespace.
export function lspc<T>(p: Parser<T>): Parser<T> {
  return bind(many(either(whitespace, newline)), (_) => p);
}

// spc1 is a parser that requires leading and trailing whitespace.
export function spc1<T>(between: Parser<T>): Parser<T> {
  return bind(spaces, (_) =>
    bind(between, (x) => bind(spaces, (_) => pure(x)))
  );
}

// orFail raises a specific parse error if the parser is unsuccessful.
function orFail<A>(msg: string, p: Parser<A>): Parser<A> {
  return either(p, zero<A>(msg));
}

// lazy is a parser that takes a parser generator and generates the parser at
// parse-time rather than when constructing the parsers. This allows for
// recursive parsers to be defined.
export function lazy<T>(g: () => Parser<T>): Parser<T> {
  return (input): Result<T> =>
    // Create this parser lazily at parse-time.
    g()(input);
}

// consumeAll raises a parse error if the parser doesn't consume all of its
// input.
export function consumeAll<T>(parser: Parser<T>): Parser<T> {
  return function (input) {
    const result = parser(input);

    if (
      result._ == "outputvalue" &&
      result.stream.idx < result.stream.src.length
    ) {
      return zero<T>("unexpected input")(result.stream);
    }

    return result;
  };
}

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

export const parseErrorDiagnostic = (err: FatalParseError) => {
  const lc = indexToLineCol(err.stream.src, err.stream.idx);
  return (
    `error at line ${lc.line} col ${lc.col}: ${err.error}\n` +
    `  ${printLine(err.stream.src, lc.line)}\n` +
    `  ${" ".repeat(lc.col)}^`
  );
};
