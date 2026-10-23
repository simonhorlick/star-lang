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

// Unwrap the tooling nodes (origins, syntax and labels) around an expression.
const unwrap = (e: Expression): Expression =>
  e._ == "orig" || e._ == "syn" || e._ == "label" ? unwrap(e.child) : e;

// typeArguments returns the arguments of a type constructor application, so
// for Vect(A, succ(n)) it returns [A, succ(n)].
export const typeArguments = (t: Expression): Expression[] => {
  const u = unwrap(t);
  return u._ == "app" ? typeArguments(u.func).concat([u.arg]) : [];
};

export type Classification = {
  // For each header variable of the type, whether it is an index.
  isIndex: boolean[];
  // The header variables that are parameters, in order.
  parameters: Argument[];
  // The header variables that are indices, in order.
  indices: Argument[];
};

// classifyParams splits the header variables of a type into parameters and
// indices. A header variable is a parameter when every constructor's return
// type has exactly that variable in its position, i.e. it is fixed across the
// whole type and is in scope for every constructor. Otherwise it is an index,
// which each constructor must supply a value for in its return type. For
// example, in
//
//   type Equal(A *, a A, b A) = refl : Equal(A, a, a)
//
// A and a are parameters and b is an index, and in
//
//   type Vect(A *, sz Nat) = vnil : Vect(A, zero) | vext(n Nat, head A, tail Vect(A, n)) : Vect(A, succ(n))
//
// A is a parameter and sz is an index. A constructor without an explicit
// return type returns the type applied to all of its header variables, so a
// type where no constructor has a return type has only parameters.
export const classifyParams = (adt: ADT): Classification => {
  const isIndex = adt.params.map(
    (param, i) =>
      !adt.constructors.every((con) => {
        // A constructor argument with the same name shadows the header
        // variable, so any use of the name in the return type refers to the
        // argument rather than the header variable.
        if (con.args.some((arg) => arg.name == param.name)) {
          return false;
        }
        if (con.typ === null) {
          return true;
        }
        const args = typeArguments(con.typ);
        if (i >= args.length) {
          return false;
        }
        const arg = unwrap(args[i]);
        return (arg._ == "ref" || arg._ == "par") && arg.name == param.name;
      })
  );
  return {
    isIndex: isIndex,
    parameters: adt.params.filter((_, i) => !isIndex[i]),
    indices: adt.params.filter((_, i) => isIndex[i]),
  };
};

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
