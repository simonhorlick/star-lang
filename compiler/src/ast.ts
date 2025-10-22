import {
  Parser,
  bind,
  many,
  pure,
  Stream,
  Result,
  str,
  line,
  map,
  char,
  many1,
  newline,
  optional,
  whitespace,
  join,
  join1,
  spaces,
  spc,
  any6,
  error,
  lspc,
} from "./parser";
import {
  Ann,
  block,
  Expression,
  expression,
  Identifier,
  identifier,
  identifier2,
  keyword,
  Label,
  orFail,
  Origin,
  parenthesis,
  strip,
  Syntax,
} from "./pratt";
import { Ann as Ann2 } from "./sugar";

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
  type: Expression;
};

export const Argument = (name: string, type: Expression): Argument => ({
  name: name,
  type: type,
});

export type Constructor = {
  name: Origin | Identifier;
  args: Argument[];
  typ: Expression | null;
};

export const Constructor = (
  name: Origin | Identifier,
  args: Argument[],
  typ: Expression | null
): Constructor => ({
  name: name,
  args: args,
  typ: typ,
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

// A desugared top-level definition.
export type Def2 = {
  _: "def";
  name: string;
  term: Ann2;
  start?: number;
  end?: number;
};

export const Def2 = (
  name: string,
  term: Ann2,
  start: number | undefined,
  end: number | undefined
): Def2 => ({
  _: "def",
  name: name,
  term: term,
  start: start,
  end: end,
});

export type Pkg = { _: "pkg"; name: string };

export type Com = { _: "com"; text: string };

export type Space = { _: "sp" };
export type Newline = { _: "nl" };

export type File = {
  _: "file";
  content: ASTNode[];
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

// An Origin for ASTNodes
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

// Wrap the label with an Origin so we can know what it refers to.
export const label = (
  name: string,
  p: Parser<Expression>
): Parser<Expression> => block(map(p, (t) => Label(name, t)));

const term = lspc(expression(0));
const type = term;

// definition parses a top-level function definition, for example
// `func id: A->A = λx.x`.
export const definition: Parser<ParseError | ASTNode> = block2(
  bind(keyword("func"), (sfunc) =>
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

const annotation2: Parser<Expression> = bind(optional(spaces), (_) =>
  bind(str(":"), (_) => type)
);

// parse an ADT constructor with an optional type annotation, for example
// `name(arg1 ArgType1, ..., ArgN ArgTypeN):Type`
export const constructor: Parser<Constructor> = bind(
  block(identifier2),
  (name) =>
    bind(many(whitespace), (_) =>
      bind(optional(argumentList), (args) =>
        bind(optional(annotation2), (typ) =>
          pure(Constructor(name, args || [], typ))
        )
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

export function stripAST(t: ASTNode): ASTNode {
  switch (t._) {
    case "adt":
      return ADT(
        t.name,
        t.params.map((p) => Argument(p.name, strip(p.type))),
        t.constructors.map((c) =>
          Constructor(
            c.name,
            c.args.map((p) => Argument(p.name, strip(p.type))),
            c.typ ? strip(c.typ) : null
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
      return stripAST(t.child);
    case "pkg":
      return t;
    case "sp":
      return t;
    case "err":
      return t;
  }
}
