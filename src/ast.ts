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

// // Identifier is a syntax node so that we can wrap it in origins and map it
// // back to the original source location.
// export type Identifier = {
//   _: "id";
//   name: string;
// };

// export const Identifier = (name: string): Identifier => ({
//   _: "id",
//   name: name,
// });

// // Π is the type of functions.
// export type Pi = {
//   _: "pi";
//   from: Type;
//   body: Type;
//   name: string; // name of the binder
// };

// export const Pi = (name: string, from: Type, to: Type): Pi => ({
//   _: "pi",
//   from: from,
//   body: to,
//   name: name,
// });

// // Abs is a lambda abstraction.
// export type Abs = {
//   _: "lam";
//   name: Origin | Identifier; // name of the binder
//   body: Term; // the body of the abstraction
// };

// export const Abs = (name: string, body: Term): Abs => ({
//   _: "lam",
//   name: Identifier(name),
//   body: body,
// });

// export const AbsI = (name: Origin | Identifier, body: Term): Abs => ({
//   _: "lam",
//   name: name,
//   body: body,
// });

// // Self is a way of abstracting out the value currently being typechecked so
// // that it can be used within the body.
// export type Self = {
//   _: "self";
//   name: string; // name of the binder
//   body: Term; // the body of the abstraction
// };

// export const Self = (name: string, body: Term): Self => ({
//   _: "self",
//   name: name,
//   body: body,
// });

// // App is a function application.
// export type App = {
//   _: "app";
//   func: Term;
//   arg: Term;
// };

// export const App = (left: Term, right: Term): App => ({
//   _: "app",
//   func: left,
//   arg: right,
// });

// // A bound variable.
// export type Var = {
//   _: "var";

//   // The variable name for pretty printing.
//   name: string;

//   // The de Bruijn index of this node. The number index stands for “the variable
//   // bound by the index’th enclosing λ.”
//   index: number;
// };

// export const Var = (name: string, index: number): Var => ({
//   _: "var",
//   name: name,
//   index: index,
// });

// // A bound variable that has not yet been resolved to a debruijin index.
// export type Par = {
//   _: "par";

//   // The variable name.
//   name: string;
// };

// export const Par = (name: string): Par => ({
//   _: "par",
//   name: name,
// });

// // A reference.
// export type Ref = {
//   _: "ref";

//   // The name of the definition being referenced.
//   name: string;
// };

// export const Ref = (name: string): Ref => ({
//   _: "ref",
//   name: name,
// });

// // A hole.
// export type Hole = {
//   _: "hole";
//   id: number;
// };

// export const Hole = (id: number): Hole => ({
//   _: "hole",
//   id: id,
// });

// // ★ is the type of types.
// export type Star = {
//   _: "star";
// };

// export const Star = (): Star => ({
//   _: "star",
// });

// // A type annotation.
// export type Ann = {
//   _: "ann";

//   // The term this annotation applies to.
//   term: Term;

//   // The annotated type.
//   typ: Type;
// };

// export const Ann = (term: Term, type: Type): Ann => ({
//   _: "ann",
//   term: term,
//   typ: type,
// });

// // Runtime relevance.
// export type Rel = {
//   _: "rel";
//   term: Term;
//   uses: number;
// };

// export const Rel = (term: Term, uses: number): Rel => ({
//   _: "rel",
//   term: term,
//   uses: uses,
// });

// // A keyword.
// export type Key = {
//   _: "key";
//   key: string;
// };

// export const Key = (key: string): Key => ({
//   _: "key",
//   key: key,
// });

// // Mark certain ranges as syntactic, for example the "if" or "case" keywords.
// export type Syntax = {
//   _: "syn";
//   syntax: Origin;
//   child: Term;
// };

// export const Syntax = (syntax: Origin, child: Term): Syntax => ({
//   _: "syn",
//   syntax: syntax,
//   child: child,
// });

// // A Label is a way of annotating terms with a string. This allows us to
// // determine which branch of an if statement a node belongs to, for example.
// export type Label = {
//   _: "label";
//   label: string;
//   child: Term;
// };

// export const Label = (label: string, child: Term): Label => ({
//   _: "label",
//   label,
//   child,
// });

// export type Term =
//   | Abs
//   | App
//   | Var
//   | Par
//   | Ref
//   | Ann
//   | Pi
//   | Star
//   | Self
//   | Case
//   | Let
//   | If
//   | Origin
//   | Identifier
//   | Hole
//   | IntLit
//   | StringLit
//   | Rel
//   | Syntax
//   | Key
//   | Label
//   | ParseError;
// export type Type = Term;

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

// type Branch = {
//   constructor: Identifier | Origin;
//   term: Term;
// };

// export const Branch = (
//   constructor: Identifier | Origin,
//   term: Term
// ): Branch => ({
//   constructor: constructor,
//   term: term,
// });

// export type Case = {
//   _: "case";
//   name: Term; // This should be a Par or a Ref.
//   branches: Branch[];
// };

// export const Case = (name: Term, branches: Branch[]): Case => ({
//   _: "case",
//   name: name,
//   branches: branches,
// });

// export type Let = {
//   _: "let";
//   name: Origin | Identifier;
//   expr: Term;
//   body: Term;
// };

// export const Let = (
//   name: Origin | Identifier,
//   expr: Term,
//   body: Term
// ): Let => ({
//   _: "let",
//   name: name,
//   expr: expr,
//   body: body,
// });

// export type If = {
//   _: "if";
//   condition: Term;
//   trueBranch: Term;
//   falseBranch: Term;
// };

// export const If = (
//   condition: Term,
//   trueBranch: Term,
//   falseBranch: Term
// ): If => ({
//   _: "if",
//   condition: condition,
//   trueBranch: trueBranch,
//   falseBranch: falseBranch,
// });

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
};

export const Def2 = (name: string, term: Ann2): Def2 => ({
  _: "def",
  name: name,
  term: term,
});

// // An integer literal
// export type IntLit = { _: "int"; num: number };

// // A string literal
// export type StringLit = { _: "str"; str: string };

export type Pkg = { _: "pkg"; name: string };

export type Com = { _: "com"; text: string };

export type Space = { _: "sp" };
export type Newline = { _: "nl" };

export type File = {
  _: "file";
  content: ASTNode[];
};

// // block is a parser that adds origin information into the parse tree. It can be
// // disabled by setting origins to false in the stream.
// export const block =
//   <T extends Term>(parser: Parser<T>): Parser<Origin> =>
//   (s: Stream): Result<Origin> => {
//     const start = s.idx;
//     const result = parser(s);

//     if (result._ == "parseerror") {
//       return result;
//     }

//     return pure(Origin(start, result.stream.idx, result.value))(result.stream);
//   };

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

// const reserved = new Set([
//   "func",
//   "import",
//   "let",
//   "case",
//   "of",
//   "if",
//   "then",
//   "else",
// ]);

// // resync is a parser that advances the stream until the
// // next sync character or keyword is observed.
// export const resync = skip(
//   until(
//     any(...Array.from(reserved.values()).map((v) => str(v)), oneOf(`|()" `))
//   ) // until fails iff the nested parser is successful.
// );

// // skip forward and return a parse error in this position.
// const resync2 = (msg: string): Parser<ParseError> =>
//   map(resync, (skipped) => ParseError(`${msg}; got ${skipped.join("")}`));

// // orFail returns A if the parser succeeds, or ParseError if the parser fails.
// // Either way it returns successfully.
// export const orFail = <A>(msg: string, p: Parser<A>): Parser<A | Term> =>
//   either(p, block(resync2(msg)));

// // identifier parses a letter from the alphabet followed by letters, numbers and
// // other allowed special characters.
// export const identifier: Parser<string> = bind(
//   bind(alpha, (a) =>
//     bind(many(any(alpha, digit, oneOf("_."))), (b) =>
//       pure(a + (b?.join("") ?? ""))
//     )
//   ),
//   (ident: string) => {
//     if (reserved.has(ident)) {
//       return zero("reserved keyword");
//     }
//     return pure(ident);
//   }
// );

// // identifier2 parses a letter from the alphabet followed by letters, numbers and
// // other allowed special characters.
// export const identifier2: Parser<Identifier | Term> = orFail(
//   "expected identifier",
//   bind(identifier, (id) => pure(Identifier(id)))
// );

// export type Origin = {
//   _: "orig";
//   start: number;
//   end: number;
//   child: Term;
// };

// export const Origin = (start: number, end: number, child: Term): Origin => ({
//   _: "orig",
//   start: start,
//   end: end,
//   child: child,
// });

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

// export const keyword = (kw: string): Parser<Origin> =>
//   block(map(str(kw), (x) => Key(x)));

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

// // Transforms a (successful) ParseError node into an actual failure.
// const failOnParseError = (p: Parser<Term>): Parser<Term> =>
//   bind(p, (x) => {
//     const y = x._ == "orig" ? x.child : x;
//     if (y._ == "err") {
//       return zero(y.msg);
//     } else {
//       return pure(x);
//     }
//   });

const term = lspc(expression(0));
const type = term;

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
      return t.child;
    case "pkg":
      return t;
    case "sp":
      return t;
    case "err":
      return t;
  }
}
