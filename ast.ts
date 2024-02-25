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
  char,
  either,
  front,
  last,
  lazy,
  many1,
  newline,
  optional,
  whitespace,
  join,
  join1,
  spaces,
  spc,
  spc1,
  any6,
  num,
  any10,
  error,
  skip,
  sat,
  zero,
  until,
  any11,
  lspc,
  any12,
} from "./parser";
import { pretty } from "./pretty";

// ParseError is a syntax node that allows partial parse trees to be
// constructed.
export type ParseError = {
  _: "err";
  msg: string;
};

export const ParseError = (msg: string): ParseError => ({
  _: "err",
  msg: msg,
});

// Identifier is a syntax node so that we can wrap it in origins and map it
// back to the original source location.
export type Identifier = {
  _: "id";
  name: string;
};

export const Identifier = (name: string): Identifier => ({
  _: "id",
  name: name,
});

// Π is the type of functions.
export type Pi = {
  _: "pi";
  from: Type;
  body: Type;
  name: string; // name of the binder
};

export const Pi = (name: string, from: Type, to: Type): Pi => ({
  _: "pi",
  from: from,
  body: to,
  name: name,
});

// Abs is a lambda abstraction.
export type Abs = {
  _: "lam";
  name: Origin | Identifier; // name of the binder
  body: Term; // the body of the abstraction
};

export const Abs = (name: string, body: Term): Abs => ({
  _: "lam",
  name: Identifier(name),
  body: body,
});

export const AbsI = (name: Origin | Identifier, body: Term): Abs => ({
  _: "lam",
  name: name,
  body: body,
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
  func: Term;
  arg: Term;
};

export const App = (left: Term, right: Term): App => ({
  _: "app",
  func: left,
  arg: right,
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

// A hole.
export type Hole = {
  _: "hole";
  id: number;
};

export const Hole = (id: number): Hole => ({
  _: "hole",
  id: id,
});

// ★ is the type of types.
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

// Runtime relevance.
export type Rel = {
  _: "rel";
  term: Term;
  uses: number;
};

export const Rel = (term: Term, uses: number): Rel => ({
  _: "rel",
  term: term,
  uses: uses,
});

// A keyword.
export type Key = {
  _: "key";
  key: string;
};

export const Key = (key: string): Key => ({
  _: "key",
  key: key,
});

// Mark certain ranges as syntactic, for example the "if" or "case" keywords.
export type Syntax = {
  _: "syn";
  syntax: Origin;
  child: Term;
};

export const Syntax = (syntax: Origin, child: Term): Syntax => ({
  _: "syn",
  syntax: syntax,
  child: child,
});

export type Term =
  | Abs
  | App
  | Var
  | Par
  | Ref
  | Ann
  | Pi
  | Star
  | Self
  | Case
  | Let
  | If
  | Origin
  | Identifier
  | Hole
  | IntLit
  | StringLit
  | Rel
  | Syntax
  | Key
  | ParseError;
export type Type = Term;

export type ASTNode =
  | Pkg
  | Com
  | Def
  | ADT
  | Space
  | Newline
  | Origin2
  | ParseError;

export type Argument = {
  name: string;
  type: Type;
};

export const Argument = (name: string, type: Type): Argument => ({
  name: name,
  type: type,
});

export type Constructor = {
  name: Origin | Identifier;
  args: Argument[];
};

export const Constructor = (
  name: Origin | Identifier,
  args: Argument[]
): Constructor => ({
  name: name,
  args: args,
});

export type ADT = {
  _: "adt";
  name: Origin | Identifier;
  params: Argument[];
  constructors: Constructor[];
};

export const ADT = (
  name: Origin | Identifier,
  params: Argument[],
  constructors: Constructor[]
): ADT => ({
  _: "adt",
  name: name,
  params: params,
  constructors: constructors,
});

type Branch = {
  constructor: Identifier | Origin;
  term: Term;
};

export const Branch = (
  constructor: Identifier | Origin,
  term: Term
): Branch => ({
  constructor: constructor,
  term: term,
});

export type Case = {
  _: "case";
  name: Term; // This should be a Par or a Ref.
  branches: Branch[];
};

export const Case = (name: Term, branches: Branch[]): Case => ({
  _: "case",
  name: name,
  branches: branches,
});

export type Let = {
  _: "let";
  name: Origin | Identifier;
  expr: Term;
  body: Term;
};

export const Let = (
  name: Origin | Identifier,
  expr: Term,
  body: Term
): Let => ({
  _: "let",
  name: name,
  expr: expr,
  body: body,
});

export type If = {
  _: "if";
  condition: Term;
  trueBranch: Term;
  falseBranch: Term;
};

export const If = (
  condition: Term,
  trueBranch: Term,
  falseBranch: Term
): If => ({
  _: "if",
  condition: condition,
  trueBranch: trueBranch,
  falseBranch: falseBranch,
});

// A top-level definition.
export type Def = {
  _: "def";
  name: string;
  term: Ann;
};

export const Def = (name: string, term: Ann): Def => ({
  _: "def",
  name: name,
  term: term,
});

// An integer literal
export type IntLit = { _: "int"; num: number };

// A string literal
export type StringLit = { _: "str"; str: string };

export type Pkg = { _: "pkg"; name: string };

export type Com = { _: "com"; text: string };

export type Space = { _: "sp" };
export type Newline = { _: "nl" };

export type File = {
  _: "file";
  content: ASTNode[];
};

// block is a parser that adds origin information into the parse tree. It can be
// disabled by setting origins to false in the stream.
export const block =
  <T extends Term>(parser: Parser<T>): Parser<Origin> =>
  (s: Stream): Result<Origin> => {
    const start = s.idx;
    const result = parser(s);

    if (result._ == "parseerror") {
      return result;
    }

    return pure(Origin(start, result.stream.idx, result.value))(result.stream);
  };

// block2 is a parser that adds origin information into the parse tree. It can be
// disabled by setting origins to false in the stream.
export const block2 =
  <T extends ASTNode>(parser: Parser<T>): Parser<Origin2> =>
  (s: Stream): Result<Origin2> => {
    const start = s.idx;
    const result = parser(s);

    if (result._ == "parseerror") {
      return result;
    }

    return pure(Origin2(start, result.stream.idx, result.value))(result.stream);
  };

// resync is a parser that advances the stream until the
// next sync character or keyword is observed.
export const resync = skip(
  until(either(str("func"), oneOf(`|()" `))) // until fails iff the nested parser is successful.
);

// skip forward and return a parse error in this position.
const resync2 = (msg: string): Parser<ParseError> =>
  map(resync, (skipped) => ParseError(`${msg}; got ${skipped.join("")}`));

// orFail returns A if the parser succeeds, or ParseError if the parser fails.
// Either way it returns successfully.
export const orFail = <A>(msg: string, p: Parser<A>): Parser<A | Term> =>
  either(p, block(resync2(msg)));

const reserved = new Set(["func", "import", "let", "case", "if"]);

// identifier parses a letter from the alphabet followed by letters, numbers and
// other allowed special characters.
export const identifier: Parser<string> = bind(
  bind(alpha, (a) =>
    bind(many(any(alpha, digit, oneOf("_."))), (b) =>
      pure(a + (b?.join("") ?? ""))
    )
  ),
  (ident: string) => {
    if (reserved.has(ident)) {
      return zero("reserved keyword");
    }
    return pure(ident);
  }
);

// identifier2 parses a letter from the alphabet followed by letters, numbers and
// other allowed special characters.
export const identifier2: Parser<Identifier | Term> = orFail(
  "expected identifier",
  bind(identifier, (id) => pure(Identifier(id)))
);

export type Origin = {
  _: "orig";
  start: number;
  end: number;
  child: Term;
};

export const Origin = (start: number, end: number, child: Term): Origin => ({
  _: "orig",
  start: start,
  end: end,
  child: child,
});

export type Origin2 = {
  _: "orig2";
  start: number;
  end: number;
  child: ASTNode;
};

export const Origin2 = (
  start: number,
  end: number,
  child: ASTNode
): Origin2 => ({
  _: "orig2",
  start: start,
  end: end,
  child: child,
});

export const keyword = (kw: string): Parser<Origin> =>
  block(map(str(kw), (x) => Key(x)));

// parsePackage parses a package declaration such as `package abc`.
export const parsePackage: Parser<ASTNode> = bind(str("package"), (_) =>
  bind(many1(whitespace), (_) =>
    block2(bind(identifier, (a) => pure({ _: "pkg", name: a } as Pkg)))
  )
);

// parseLineComment parses an end-of-line comment and stops either at the end of
// the line or EOF.
export const parseLineComment: Parser<ASTNode> = block2(
  bind(str("//"), (_) =>
    bind(line, (l) =>
      pure({
        _: "com",
        text: l,
      } as Com)
    )
  )
);

// reference parses a "variable" in the programming language.
export const reference: Parser<Term> = map(identifier, (result: string) =>
  Ref(result)
);

// par parses a "variable" in the programming language.
export const par: Parser<Term> = block(
  map(identifier, (result: string) => Par(result))
);

// parenthesis is a parser that requires an opening and closing parenthesis to
// surround the given parser.
export const parenthesis = <T>(between: Parser<T>): Parser<T | ParseError> =>
  bind(char("("), (_) =>
    bind(between, (x) =>
      either(
        bind(char(")"), (_) => pure(x)),
        pure(ParseError("missing close parenthesis"))
      )
    )
  );

export const arrow: (type: () => Parser<Type>) => (s: Stream) => Result<Pi> = (
  type
) =>
  bind(
    // (A->B)->C
    either(block(reference), parenthesis(lazy(type))),
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

/*export const type: Parser<Type> = any4(
  block(arrow(() => type)),
  block(parenthesis(lazy(() => type))),
  block(star),
  block(reference)
);*/

const logdbg = <T>(msg: string, p: Parser<T>): Parser<T> => {
  return (s: Stream): Result<T> => {
    console.log(`${msg}. next char is ${s.src.substring(s.idx)}`);
    return p(s);
  };
};

// pi parses a pi type `Πx:T t`.
export const pi = (term: () => Parser<Term>): Parser<Pi | ParseError> =>
  bind(
    char("Π"),
    (_) =>
      // bind(optional(spaces), (_) =>
      bind(identifier, (name) =>
        bind(
          char(":"),
          (_) =>
            // bind(optional(spaces), (_) =>
            bind(orFail("expected type", lazy(term)), (from) =>
              bind(
                orFail("expected spaces between type and body", spaces),
                (sp): Parser<Pi | ParseError> => {
                  if (!(sp instanceof Array) && sp._ == "err") {
                    return pure(Pi(name, from, sp));
                  }
                  return bind(orFail("expected term", lazy(term)), (body) =>
                    pure(Pi(name, from, body))
                  );
                }
              )
            )
          // )
        )
      )
    // )
  );

// abstraction parses a lambda abstraction `λx t`. The binder x is separated
// from the body by spaces.
export const abstraction = (term: () => Parser<Term>): Parser<Abs> =>
  bind(char("λ"), (_) =>
    bind(optional(spaces), (_) =>
      bind(block(identifier2), (name) =>
        bind(spaces, (_) =>
          bind(orFail("expected term", lazy(term)), (body) =>
            pure(AbsI(name, body))
          )
        )
      )
    )
  );

// application is a parser for function application `f(x)`; `f(x)(y)`; `f (x(t))`.
export const application = (term: () => Parser<Term>, lhs: Term): Parser<App> =>
  // f(x) or (some term)(x)
  bind(many(whitespace), (_) =>
    // args: greedily parse as many as we're able to
    bind(many1(parenthesis(spc(lazy(term)))), (ts) => {
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
          func: acc,
          arg: t,
        }),
        {
          _: "app",
          func: terms[0],
          arg: terms[1],
        }
      );

      return pure(expr);
    })
  );

// | true -> false
export const caseBranch: Parser<Branch> = bind(optional(spaces), (_) =>
  bind(str("|"), (_) =>
    bind(optional(spaces), (_) =>
      bind(block(identifier2), (id) =>
        bind(many(whitespace), (_) =>
          bind(either(str("->"), str("=>")), (_) =>
            bind(term, (t) => pure(Branch(id, t)))
          )
        )
      )
    )
  )
);

// case b of
// | true -> false
// | false -> true
export const caseStatement: Parser<Case | Term> = bind(
  keyword("case"),
  (scase) =>
    orFail(
      "case statment not well formed",
      bind(spc1(par), (id) =>
        bind(keyword("of"), (sof) =>
          bind(newline, (_) =>
            bind(many1(caseBranch), (branches) =>
              pure(Syntax(scase, Syntax(sof, Case(id, branches))))
            )
          )
        )
      )
    )
);

// let b = f(x) in ...
export const letStatement: Parser<Let | Term> = bind(keyword("let"), (slet) =>
  orFail(
    "let statment not well formed",
    bind(spc1(block(identifier2)), (id) =>
      bind(str("="), (_) =>
        bind(term, (expr) =>
          bind(lspc(keyword("in")), (sin) =>
            bind(term, (body) =>
              pure(Syntax(slet, Syntax(sin, Let(id, expr, body))))
            )
          )
        )
      )
    )
  )
);

// ifStatement parses an in-then-else statement of the form
// if <condition> then <true branch> else <false branch>.
export const ifStatement: Parser<If | Term> = bind(keyword("if"), (sif) =>
  orFail(
    "if statment not well formed",
    bind(spc(term), (condition) =>
      bind(keyword("then"), (sthen) =>
        bind(spc(term), (trueBranch) =>
          bind(keyword("else"), (selse) =>
            bind(spc(term), (falseBranch) =>
              pure(
                Syntax(
                  sif,
                  Syntax(
                    sthen,
                    Syntax(selse, If(condition, trueBranch, falseBranch))
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

export const annotation = (term: () => Parser<Term>): Parser<Ann> =>
  bind(parenthesis(lazy(term)), (body) =>
    bind(str(":"), (_) => bind(lazy(term), (typ) => pure(Ann(body, typ))))
  );

export const integerLiteral: Parser<IntLit> = map(num, (x) => ({
  _: "int",
  num: x,
}));

// Transforms a (successful) ParseError node into an actual failure.
const failOnParseError = (p: Parser<Term>): Parser<Term> =>
  bind(p, (x) => {
    const y = x._ == "orig" ? x.child : x;
    if (y._ == "err") {
      return zero(y.msg);
    } else {
      return pure(x);
    }
  });

// listLiteral parses a literal list constructor. Examples include:
// [] - an empty list
// [1] - a singleton list
// [1,2,3] - elements are delimited by commas
// [[],[],[]] - a list of lists
export const listLiteral: Parser<Term> =
  // opening bracket
  bind(str("["), (_) =>
    // elements
    bind(join(failOnParseError(term), spc(char(","))), (elements) =>
      // closing bracket
      bind(
        orFail("expected ]", str("]")),
        // The parser outputs terms to construct the list, for example,
        //  [] => nil(▨)
        //  [1,2] => cons(▨, 1, cons(▨, 2, nil(▨)))
        (_) =>
          pure(
            elements.reduceRight(
              // cons(▨, x, ...)
              // FIXME: What's the best way to number holes?
              (acc, curr) =>
                App(App(App(Ref("cons"), Hole(Math.random())), curr), acc),
              // nil(▨)
              App(Ref("nil"), Hole(Math.random()))
            )
          )
      )
    )
  );

// utf8 parses a string literal containing utf8 characters and escape
// sequences.
// TODO: Implement escape sequences.
export const utf8 = sat((c) => c != '"');

export const stringLiteral: Parser<Term> = bind(str('"'), (_) =>
  either(
    bind(many(utf8), (s) =>
      bind(str('"'), (_) => pure({ _: "str", str: s.join("") }))
    ),
    // if there's a parse error within the string, we need to skip forward to
    // the next sync character.
    bind(resync, (_) =>
      // if the next sync character is an end-of-string character then skip that
      // too.
      bind(optional(char(`"`)), (_) =>
        pure(ParseError("failed to parse string literal"))
      )
    )
  )
);

export const subterm: Parser<Term> = bind(
  any12(
    // parenthesis `(T)`
    parenthesis(spc(lazy(() => term))),
    // pi `Πx:A t`
    pi(() => term),
    // abstraction `λx t`
    abstraction(() => term),
    // a case destructuring `case x of ...`
    caseStatement,
    // a let statement `let x = ...`
    letStatement,
    // an if-then-else block
    ifStatement,
    // the type of types `*`
    star,
    // a reference for example `t`
    reference,
    // a list literal, for example `[1,2,3]`
    listLiteral,
    // an integer literal, for example `123`
    integerLiteral,
    // a string literal, for example `"abc"`
    stringLiteral,
    // if nothing parses then skip past these characters and present a
    // ParseError AST node.
    resync2("expected term")
  ),
  (lhs) =>
    // A term may be followed by a type annotation, for example `(f(x)):Y`.
    bind(
      either(
        bind(lspc(str(":")), (_) =>
          bind(
            lazy(() => term),
            (typ) => pure(Ann(lhs, typ))
          )
        ),
        // A term followed by another term is a function application, for
        // example `g(x)(y)(z)`.
        either(
          application(() => term, lhs),
          pure(lhs)
        )
      ),
      (t) => pure(t)
    )
);

// term is a parser for terms in the programming language - i.e. the expressions
// that can be evaluated.
export const term: Parser<Term> =
  // Parse the actual term. Consume any leading, but not trailing, whitespace as
  // if the next parser is requiring leading whitespace it'll already have been
  // consumed.
  bind(block(lspc(subterm)), (lhs) =>
    // A term may be followed by an arrow - making it a pi type.
    either(
      bind(str("->"), (_) =>
        bind(
          lazy(() => term),
          (to) => pure(Pi("", lhs, to))
        )
      ),

      // If it's not, just return the term.
      pure(lhs)
    )
  );

export const type: Parser<Type> = term;

// definition parses a top-level function definition, for example
// `func id: A->A = λx.x`.
export const definition: Parser<ParseError | Def> = bind(
  keyword("func"),
  (sfunc) =>
    bind(orFail("expected space after func", many1(whitespace)), (_) =>
      bind(identifier, (name) =>
        bind(many(whitespace), (_) =>
          bind(orFail("expected :", char(":")), (_) =>
            bind(orFail("expected type", type), (typ) =>
              bind(orFail("expected =", lspc(char("="))), (_) =>
                bind(orFail("expected term", term), (tm) =>
                  pure(Def(name, Ann(Syntax(sfunc, tm), typ)))
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
  (args) => {
    if (Array.isArray(args)) {
      return pure(args);
    } else {
      return error(args.msg);
    }
  }
);

// name(arg1 ArgType1, ..., ArgN ArgTypeN)
export const constructor: Parser<Constructor> = bind(
  block(identifier2),
  (name) =>
    bind(many(whitespace), (_) =>
      bind(optional(argumentList), (args) =>
        pure(Constructor(name, args || []))
      )
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
  many(
    any6(
      parseWhitespace,
      parseNewline,
      parsePackage,
      definition,
      adt,
      parseLineComment
    )
  ),
  (r) => ({ _: "file", content: r })
);

export const identifier2str = (id: Term): string => {
  switch (id._) {
    case "id":
      return id.name;
    case "orig":
      return identifier2str(id.child);
    default:
      throw `expected identifier; got ${id._}`;
  }
};

// strip removes origins and syntax nodes from the term tree.
export function strip(t: Term): Term {
  switch (t._) {
    case "var":
      return t;
    case "lam":
      return Abs(identifier2str(t.name), strip(t.body));
    case "self":
      return Self(t.name, strip(t.body));
    case "app":
      return App(strip(t.func), strip(t.arg));
    case "ann":
      return Ann(strip(t.term), strip(t.typ));
    case "pi":
      return Pi(t.name, strip(t.from), strip(t.body));
    case "par":
    case "star":
    case "ref":
    case "id":
    case "hole":
    case "int":
    case "str":
    case "key":
    case "err":
      return t;
    case "orig":
    case "syn":
      return strip(t.child);
    case "case":
      return Case(
        strip(t.name),
        t.branches.map((b) =>
          Branch(strip(b.constructor) as Identifier, strip(b.term))
        )
      );
    case "let":
      return Let(strip(t.name) as Identifier, strip(t.expr), strip(t.body));
    case "if":
      return If(strip(t.condition), strip(t.trueBranch), strip(t.falseBranch));
    case "rel":
      throw "strip: unexpected rel";
  }
}

export function stripAST(t: ASTNode): ASTNode {
  switch (t._) {
    case "adt":
      return ADT(
        t.name,
        t.params.map((p) => Argument(p.name, strip(p.type))),
        t.constructors.map((c) =>
          Constructor(
            c.name,
            c.args.map((p) => Argument(p.name, strip(p.type)))
          )
        )
      );
    case "com":
      return t;
    case "def":
      return Def(t.name, strip(t.term) as Ann);
    case "nl":
      return t;
    case "orig2":
      return t.child;
    case "pkg":
      return t;
    case "sp":
      return t;
    case "err":
      return t;
  }
}

// serialise outputs the term tree in the same syntax as the typescript
// implementation. This is useful for quickly generating code for a term to be
// used in tests.
export function serialise(t: Term, d: number = 0): string {
  switch (t._) {
    case "var":
      return `Var("${t.name}",${t.index})`;
    case "lam":
      return `Abs("${identifier2str(t.name)}", ${serialise(t.body, d + 1)})`;
    case "self":
      return `Self("${t.name}", ${serialise(t.body, d + 1)})`;
    case "app":
      return `App(${serialise(t.func, d + 1)}, ${serialise(t.arg, d + 1)})`;
    case "ann":
      return `Ann(${serialise(t.term, d + 1)}, ${serialise(t.typ, d + 1)})`;
    case "pi":
      return `Pi("${t.name}", ${serialise(t.from, d + 1)}, ${serialise(
        t.body,
        d + 1
      )})`;
    case "par":
      return `Par("${t.name}")`;
    case "star":
      return `Star()`;
    case "ref":
      return `Ref("${t.name}")`;
    case "id":
      return `Identifier("${t.name}")`;
    case "key":
      return `Keyword("${t.key}")`;
    case "orig":
      return `Origin(${t.start}, ${t.end}, ${serialise(t.child, d + 1)})`;
    case "syn":
      return `Syntax(${serialise(t.syntax, d + 1)}, ${serialise(
        t.child,
        d + 1
      )}`;
    case "rel":
      return `Rel(${serialise(t.term, d + 1)}, ${t.uses})`;
    case "case":
      return `Case(${serialise(t.name, d + 1)},[${t.branches
        .map(
          (b) =>
            `Branch(${serialise(b.constructor, d + 1)}, ${serialise(
              b.term,
              d + 1
            )})`
        )
        .join(",")}])`;
    case "let":
      return `Let(${serialise(t.name)}, ${serialise(
        t.expr,
        d + 1
      )}, ${serialise(t.body, d + 1)})`;

    case "if":
      return `If(${serialise(t.condition)}, ${serialise(
        t.trueBranch
      )}, ${serialise(t.falseBranch)})`;
    case "hole":
      return `Hole()`;
    case "int":
      return `IntLit(${t.num})`;
    case "str":
      return `StringLit("${t.str}")`;
    case "err":
      return `ParseError(${t.msg})`;
  }
}
