import { describe, expect, test } from "vitest";
import {
  char,
  parseErrorDiagnostic,
  Stream,
  Result,
  Parser,
  either,
  spc,
  str,
  map,
  any,
  bind,
  join,
  pure,
  error,
  optional,
  many,
  spaces,
  skip,
  until,
  oneOf,
  whitespace,
  spc1,
  newline,
  many1,
  lspc,
  any3,
  s,
  alpha,
  digit,
  zero,
  num,
} from "./parser";

// Abs is a lambda abstraction.
export type Abs = {
  _: "lam";
  name: Origin | Identifier; // name of the binder
  body: Expression; // the body of the abstraction
};

export const Abs = (name: string, body: Expression): Abs => ({
  _: "lam",
  name: Identifier(name),
  body: body,
});

export const AbsI = (name: Origin | Identifier, body: Expression): Abs => ({
  _: "lam",
  name: name,
  body: body,
});

export type IntPlus = {
  _: "add";
  lhs: Expression;
  rhs: Expression;
};

export const IntPlus = (lhs: Expression, rhs: Expression): IntPlus => ({
  _: "add",
  lhs: lhs,
  rhs: rhs,
});

export type IntSub = {
  _: "sub";
  lhs: Expression;
  rhs: Expression;
};

export const IntSub = (lhs: Expression, rhs: Expression): IntSub => ({
  _: "sub",
  lhs: lhs,
  rhs: rhs,
});

export const IntNeg = (exp: Expression): IntNeg => ({
  _: "neg",
  exp: exp,
});

export type IntMul = {
  _: "mul";
  lhs: Expression;
  rhs: Expression;
};

export const IntMul = (lhs: Expression, rhs: Expression): IntMul => ({
  _: "mul",
  lhs: lhs,
  rhs: rhs,
});

export type IntDiv = {
  _: "div";
  lhs: Expression;
  rhs: Expression;
};

export const IntDiv = (lhs: Expression, rhs: Expression): IntDiv => ({
  _: "div",
  lhs: lhs,
  rhs: rhs,
});

export type Idx = {
  _: "idx";
  arr: Expression;
  idx: Expression;
};

export const Idx = (arr: Expression, idx: Expression): Idx => ({
  _: "idx",
  arr: arr,
  idx: idx,
});

// Boolean and.
export type And = {
  _: "and";
  lhs: Expression;
  rhs: Expression;
};

export const And = (lhs: Expression, rhs: Expression): And => ({
  _: "and",
  lhs: lhs,
  rhs: rhs,
});

// Boolean or.
export type Or = {
  _: "or";
  lhs: Expression;
  rhs: Expression;
};

export const Or = (lhs: Expression, rhs: Expression): Or => ({
  _: "or",
  lhs: lhs,
  rhs: rhs,
});

export type Eq = {
  _: "eq";
  lhs: Expression;
  rhs: Expression;
};

export const Eq = (lhs: Expression, rhs: Expression): Eq => ({
  _: "eq",
  lhs: lhs,
  rhs: rhs,
});

export type Neq = {
  _: "neq";
  lhs: Expression;
  rhs: Expression;
};

export const Neq = (lhs: Expression, rhs: Expression): Neq => ({
  _: "neq",
  lhs: lhs,
  rhs: rhs,
});

export type Gt = {
  _: "gt";
  lhs: Expression;
  rhs: Expression;
};

export const Gt = (lhs: Expression, rhs: Expression): Gt => ({
  _: "gt",
  lhs: lhs,
  rhs: rhs,
});

export type Lt = {
  _: "lt";
  lhs: Expression;
  rhs: Expression;
};

export const Lt = (lhs: Expression, rhs: Expression): Lt => ({
  _: "lt",
  lhs: lhs,
  rhs: rhs,
});

export type Gte = {
  _: "gte";
  lhs: Expression;
  rhs: Expression;
};

export const Gte = (lhs: Expression, rhs: Expression): Gte => ({
  _: "gte",
  lhs: lhs,
  rhs: rhs,
});

export type Lte = {
  _: "lte";
  lhs: Expression;
  rhs: Expression;
};

export const Lte = (lhs: Expression, rhs: Expression): Lte => ({
  _: "lte",
  lhs: lhs,
  rhs: rhs,
});

export type App = {
  _: "app";
  func: Expression;
  arg: Expression;
};

export const App = (func: Expression, arg: Expression): App => ({
  _: "app",
  func: func,
  arg: arg,
});

export type IntNeg = {
  _: "neg";
  exp: Expression;
};

// List concatenation operator.
export type Cat = {
  _: "cat";
  lhs: Expression;
  rhs: Expression;
};

export const Cat = (lhs: Expression, rhs: Expression): Cat => ({
  _: "cat",
  lhs: lhs,
  rhs: rhs,
});

// Function composition operator `f . g`.
export type Comp = {
  _: "comp";
  lhs: Expression;
  rhs: Expression;
};

export const Comp = (lhs: Expression, rhs: Expression): Comp => ({
  _: "comp",
  lhs: lhs,
  rhs: rhs,
});

// Π is the type of functions.
export type Pi = {
  _: "pi";
  from: Expression;
  body: Expression;
  name: string; // name of the binder
};

export const Pi = (name: string, from: Expression, to: Expression): Pi => ({
  _: "pi",
  from: from,
  body: to,
  name: name,
});

// ★ is the type of types.
export type Star = {
  _: "star";
};

export const Star = (): Star => ({
  _: "star",
});

// Π is the type of functions.
export type Ann = {
  _: "ann";
  term: Expression;
  type: Expression;
};

export const Ann = (term: Expression, type: Expression): Ann => ({
  _: "ann",
  term: term,
  type: type,
});

// An element of a cons-list.
export type Cons = {
  _: "cons";
  head: Expression;
  tail: Expression;
};

export const Cons = (term: Expression, next: Expression): Cons => ({
  _: "cons",
  head: term,
  tail: next,
});

// An empty cons-list.
export type Nil = {
  _: "nil";
};

export const Nil = (): Nil => ({
  _: "nil",
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

type Branch = {
  constructor: Identifier | Origin;
  term: Expression;
};

export const Branch = (
  constructor: Identifier | Origin,
  term: Expression
): Branch => ({
  constructor: constructor,
  term: term,
});

export type Case = {
  _: "case";
  name: Expression; // This should be a Par or a Ref.
  branches: Branch[];
};

export const Case = (name: Expression, branches: Branch[]): Case => ({
  _: "case",
  name: name,
  branches: branches,
});

export type Let = {
  _: "let";
  name: Origin | Identifier;
  expr: Expression;
  body: Expression;
};

export const Let = (
  name: Origin | Identifier,
  expr: Expression,
  body: Expression
): Let => ({
  _: "let",
  name: name,
  expr: expr,
  body: body,
});

export type If = {
  _: "if";
  condition: Expression;
  trueBranch: Expression;
  falseBranch: Expression;
};

export const If = (
  condition: Expression,
  trueBranch: Expression,
  falseBranch: Expression
): If => ({
  _: "if",
  condition: condition,
  trueBranch: trueBranch,
  falseBranch: falseBranch,
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
  child: Expression;
};

export const Syntax = (syntax: Origin, child: Expression): Syntax => ({
  _: "syn",
  syntax: syntax,
  child: child,
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

// An integer literal
export type IntLit = { _: "int"; num: number };

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

// A Label is a way of annotating terms with a string. This allows us to
// determine which branch of an if statement a node belongs to, for example.
export type Label = {
  _: "label";
  label: string;
  child: Expression;
};

export const Label = (label: string, child: Expression): Label => ({
  _: "label",
  label,
  child,
});

// Self is a way of abstracting out the value currently being typechecked so
// that it can be used within the body.
export type Self = {
  _: "self";
  name: string; // name of the binder
  body: Expression; // the body of the abstraction
};

export const Self = (name: string, body: Expression): Self => ({
  _: "self",
  name: name,
  body: body,
});

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

export type Expression =
  | IntLit
  | IntPlus
  | IntSub
  | IntMul
  | IntDiv
  | IntNeg
  | Comp
  | App
  | Ref
  | Abs
  | Pi
  | Ann
  | Idx
  | Cat
  | Gt
  | Lt
  | Gte
  | Lte
  | Eq
  | Neq
  | And
  | Or
  | Cons
  | Nil
  | ParseError
  | Origin
  | Identifier
  | Key
  | Syntax
  | Case
  | If
  | Let
  | Par
  | Label
  | Self
  | Star;

const reserved = new Set([
  "func",
  "import",
  "let",
  "case",
  "of",
  "if",
  "then",
  "else",
]);

// block is a parser that adds origin information into the parse tree. It can be
// disabled by setting origins to false in the stream.
export const block =
  <T extends Expression>(parser: Parser<T>): Parser<Origin> =>
  (s: Stream): Result<Origin> => {
    const start = s.idx;
    const result = parser(s);

    if (result._ == "parseerror") {
      return result;
    }

    return pure(Origin(start, result.stream.idx, result.value))(result.stream);
  };

// resync is a parser that advances the stream until the
// next sync character or keyword is observed.
export const resync = skip(
  until(
    any(...Array.from(reserved.values()).map((v) => str(v)), oneOf(`|()" `))
  ) // until fails iff the nested parser is successful.
);

// skip forward and return a parse error in this position.
const resync2 = (msg: string): Parser<ParseError> =>
  map(resync, (skipped) => ParseError(`${msg}; got ${skipped.join("")}`));

// orFail returns A if the parser succeeds, or ParseError if the parser fails.
// Either way it returns successfully.
export const orFail = <A>(msg: string, p: Parser<A>): Parser<A | Expression> =>
  either(p, block(resync2(msg)));

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
export const identifier2: Parser<Identifier | Expression> = orFail(
  "expected identifier",
  bind(identifier, (id) => pure(Identifier(id)))
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

export const reference: Parser<Expression> = block(
  map(identifier, (result: string) => Ref(result))
);

// type-of-types `*`
export const star: Parser<Star> = map(char("*"), (_) => Star());

// par parses a "variable" in the programming language.
export const par: Parser<Expression> = block(
  map(identifier, (result: string) => Par(result))
);

const opParser: Parser<string> = spc(
  any(
    str("++"),
    str("->"),
    str(">="),
    str("<="),
    str("=="),
    str("!="),
    str("&&"),
    str("||"),
    char(">"),
    char("<"),
    char("+"),
    char("-"),
    char("*"),
    char("/"),
    char("."),
    char("("),
    char(":"),
    char("[")
  )
);

const getBindingPower = (op: string): [number, number] => {
  if (op == "+" || op == "-") {
    return [1, 2];
  } else if (op == "*" || op == "/") {
    return [3, 4];
  } else if (op == "(") {
    return [5, 6];
  } else if (op == ".") {
    return [8, 7];
  } else if (op == "->") {
    return [10, 9];
  } else if (op == ":") {
    return [11, 12];
  } else if (op == "[") {
    return [13, 14];
  } else if (op == "++") {
    return [15, 16];
  } else if (op == ">" || op == "<" || op == ">=" || op == "<=") {
    return [17, 18];
  } else if (op == "==" || op == "!=") {
    return [19, 20];
  } else if (op == "||") {
    return [21, 22];
  } else if (op == "&&") {
    return [23, 24];
  } else {
    throw new Error("unknown operator");
  }
};

// listLiteral parses a literal list constructor. Examples include:
// [] - an empty list
// [1] - a singleton list
// [1,2,3] - elements are delimited by commas
// [[],[],[]] - a list of lists
export const listLiteral: Parser<Expression> =
  // opening bracket
  bind(char("["), (_) =>
    // elements
    bind(join(expression(0), spc(char(","))), (elements) =>
      // closing bracket
      bind(
        orFail("expected ]", char("]")),
        // The parser outputs terms to construct the list, for example,
        //  [] => nil()
        //  [1,2] => cons(1, cons(2, nil()))
        (_) => pure(elements.reduceRight((acc, curr) => Cons(curr, acc), Nil()))
      )
    )
  );

export type Origin = {
  _: "orig";
  start: number;
  end: number;
  child: Expression;
};

export const Origin = (
  start: number,
  end: number,
  child: Expression
): Origin => ({
  _: "orig",
  start: start,
  end: end,
  child: child,
});

// | true -> false
export const caseBranch: Parser<Branch> = bind(optional(spaces), (_) =>
  bind(str("|"), (_) =>
    bind(optional(spaces), (_) =>
      bind(block(identifier2), (id) =>
        bind(many(whitespace), (_) =>
          bind(either(str("->"), str("=>")), (_) =>
            bind(lspc(expression(0)), (t) => pure(Branch(id, t)))
          )
        )
      )
    )
  )
);

export const keyword = (kw: string): Parser<Origin> =>
  block(map(str(kw), (x) => Key(x)));

// case b of
// | true -> false
// | false -> true
export const caseStatement: Parser<Case | Expression> = bind(
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
export const letStatement: Parser<Let | Expression> = bind(
  keyword("let"),
  (slet) =>
    orFail(
      "let statment not well formed",
      bind(spc1(block(identifier2)), (id) =>
        bind(str("="), (_) =>
          bind(expression(0), (expr) =>
            bind(lspc(keyword("in")), (sin) =>
              bind(lspc(expression(0)), (body) =>
                pure(Syntax(slet, Syntax(sin, Let(id, expr, body))))
              )
            )
          )
        )
      )
    )
);

// Wrap the label with an Origin so we can know what it refers to.
export const label = (
  name: string,
  p: Parser<Expression>
): Parser<Expression> => block(map(p, (t) => Label(name, t)));

// ifStatement parses an in-then-else statement of the form
// if <condition> then <true branch> else <false branch>.
export const ifStatement: Parser<If | Expression> = bind(
  spc(keyword("if")),
  (sif) =>
    orFail(
      "if statment not well formed",
      bind(label("if-condition", expression(0)), (condition) =>
        bind(spc(keyword("then")), (sthen) =>
          bind(label("if-true", expression(0)), (trueBranch) =>
            bind(spc(keyword("else")), (selse) =>
              bind(label("if-false", expression(0)), (falseBranch) =>
                pure(
                  Syntax(
                    sif,
                    Syntax(
                      sthen,
                      Syntax(
                        selse,
                        // Annotate the condition as a Bool. This is necessary
                        // to ensure any error nodes for condition have the
                        // right type so that the tooling can suggest useful
                        // completions.
                        If(Ann(condition, Ref("Bool")), trueBranch, falseBranch)
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

// pi parses a pi type `Πx:T t`.
export const pi: Parser<Pi | ParseError> = bind(
  char("Π"),
  (_) =>
    bind(identifier, (name) =>
      bind(
        char(":"),
        (_) =>
          bind(orFail("expected type", lspc(expression(0))), (from) =>
            bind(
              orFail("expected spaces between type and body", spaces),
              (sp): Parser<Pi | ParseError> => {
                if (!(sp instanceof Array) && sp._ == "err") {
                  return pure(Pi(name, from, sp));
                }
                return bind(
                  orFail("expected term", lspc(expression(0))),
                  (body) => pure(Pi(name, from, body))
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
export const abstraction: Parser<Abs> = bind(char("λ"), (_) =>
  bind(optional(spaces), (_) =>
    bind(block(identifier2), (name) =>
      bind(spaces, (_) =>
        bind(orFail("expected term", expression(0)), (body) =>
          pure(AbsI(name, body))
        )
      )
    )
  )
);

export const identifier2str = (id: Expression): string => {
  switch (id._) {
    case "id":
      return id.name;
    case "orig":
      return identifier2str(id.child);
    default:
      throw `expected identifier; got ${id._}`;
  }
};

// self parses a self type `ιx t`. The binder x is separated
// from the body by spaces.
export const self: Parser<Expression> = bind(char("ι"), (_) =>
  bind(optional(spaces), (_) =>
    bind(block(identifier2), (name) =>
      bind(spaces, (_) =>
        bind(orFail("expected term", expression(0)), (body) =>
          pure(Self(identifier2str(name), body))
        )
      )
    )
  )
);

export const integerLiteral: Parser<IntLit> = map(num, (x) => ({
  _: "int",
  num: x,
}));

// expression parses terms and operators into an unambiguous tree.
export const expression =
  (min: number): Parser<Expression> =>
  (s: Stream): Result<Expression> => {
    // An expression consists of an integer literal, optionally followed by
    // operators and literals.
    // The job of this function is to parse the expression tree while
    // maintaining correct precedence.
    // It is an implementation of the standard Pratt parsing algorithm.

    // Handle parentheses.
    let paren = char("(")(s);
    if (paren._ != "parseerror") {
      const ex = lspc(expression(0))(paren.stream);
      if (ex._ == "parseerror") {
        return ex;
      }
      let closeparen = char(")")(ex.stream);
      if (closeparen._ == "parseerror") {
        return closeparen;
      }
      return {
        _: "outputvalue",
        value: ex.value,
        stream: closeparen.stream,
      };
    }

    let neg = char("-")(s);
    if (neg._ != "parseerror") {
      const ex = expression(0)(neg.stream);
      if (ex._ == "parseerror") {
        return ex;
      }
      return {
        _: "outputvalue",
        value: IntNeg(ex.value),
        stream: ex.stream,
      };
    }

    // Peek for an opening square bracket.
    let lst = char("[")(s);
    if (lst._ != "parseerror") {
      // resume parsing from the `[`.
      return listLiteral(s);
    }

    // a case destructuring `case x of ...`
    let cse = str("case")(s);
    if (cse._ != "parseerror") {
      return caseStatement(s);
    }

    // a let statement `let x = ... in ...`
    let lt = str("let")(s);
    if (lt._ != "parseerror") {
      return letStatement(s);
    }

    // if-then-else statement `if x then y else z`
    let cond = str("if")(s);
    if (cond._ != "parseerror") {
      return ifStatement(s);
    }

    // TODO: remove from user-facing syntax
    // pi `Πx:A t`
    let p = str("Π")(s);
    if (p._ != "parseerror") {
      return pi(s);
    }

    // TODO: remove from user-facing syntax
    // abstraction `λx t`
    let abs = str("λ")(s);
    if (abs._ != "parseerror") {
      return abstraction(s);
    }

    // TODO: remove from user-facing syntax
    // self-type `ιx t`
    let slf = str("ι")(s);
    if (slf._ != "parseerror") {
      return self(s);
    }

    let acc: Result<Expression> = any3(star, integerLiteral, reference)(s);
    if (acc._ == "parseerror") {
      return acc;
    }

    // Now parse many `op a op b op c ...`
    while (true) {
      // Peek the next operator, if there is one.
      const op = opParser(acc.stream);
      if (op._ == "parseerror") {
        break;
      }
      const [leftBindingPower, rightBindingPower] = getBindingPower(op.value);

      // Consider the following expression `1 + 2 * 3`. The parse tree is built
      // from left-to-right starting with `1`. The next operator is `+` which
      // has a left binding power of 1 so we continue parsing the `2*3` with a
      // minimum binding power of 1.
      //
      //     +
      //    / \
      //   1   ?
      //
      // There are two possibilities to construct the parse tree. The first is
      // that the `2*3` is added in the place of the question mark. The second
      // is that the `2` is added in the place of the question mark and the `*3`
      // is added at the root of the tree, corresponding to the following
      // expressions:
      //
      //     +
      //    / \
      //   1   *                corresponding to 1+(2*3)
      //      / \
      //     2   3
      //
      //       *
      //      / \
      //     +   3              corresponding to (1+2)*3
      //    / \
      //   1   2
      //
      // Because the minimum binding power is 1, when we reach the `*` we know
      // that we can add it at this point in the tree. If the binding power
      // would be less, we would have to add the 2 and recurse back up to add
      // the rest of the expression.

      if (min < leftBindingPower) {
        // Special case for parsing function application using commas to
        // separate arguments.
        if (op.value == "(") {
          const args = appArgumentList(acc.value)(acc.stream);
          if (args._ == "parseerror") {
            return args;
          }
          acc = {
            _: "outputvalue",
            value: args.value,
            stream: args.stream,
          };
          // Continue parsing further operators at this level.
          continue;
        }

        // Continue parsing, setting the binding power appropriately.
        const rhs = lspc(expression(rightBindingPower))(op.stream);
        if (rhs._ == "parseerror") {
          return rhs;
        }
        if (op.value == "+") {
          acc = {
            _: "outputvalue",
            value: IntPlus(acc.value, rhs.value),
            stream: rhs.stream,
          };
        } else if (op.value == "-") {
          acc = {
            _: "outputvalue",
            value: IntSub(acc.value, rhs.value),
            stream: rhs.stream,
          };
        } else if (op.value == "*") {
          acc = {
            _: "outputvalue",
            value: IntMul(acc.value, rhs.value),
            stream: rhs.stream,
          };
        } else if (op.value == "/") {
          acc = {
            _: "outputvalue",
            value: IntDiv(acc.value, rhs.value),
            stream: rhs.stream,
          };
        } else if (op.value == "&&") {
          acc = {
            _: "outputvalue",
            value: And(acc.value, rhs.value),
            stream: rhs.stream,
          };
        } else if (op.value == "||") {
          acc = {
            _: "outputvalue",
            value: Or(acc.value, rhs.value),
            stream: rhs.stream,
          };
        } else if (op.value == "==") {
          acc = {
            _: "outputvalue",
            value: Eq(acc.value, rhs.value),
            stream: rhs.stream,
          };
        } else if (op.value == "!=") {
          acc = {
            _: "outputvalue",
            value: Neq(acc.value, rhs.value),
            stream: rhs.stream,
          };
        } else if (op.value == ">") {
          acc = {
            _: "outputvalue",
            value: Gt(acc.value, rhs.value),
            stream: rhs.stream,
          };
        } else if (op.value == "<") {
          acc = {
            _: "outputvalue",
            value: Lt(acc.value, rhs.value),
            stream: rhs.stream,
          };
        } else if (op.value == ">=") {
          acc = {
            _: "outputvalue",
            value: Gte(acc.value, rhs.value),
            stream: rhs.stream,
          };
        } else if (op.value == "<=") {
          acc = {
            _: "outputvalue",
            value: Lte(acc.value, rhs.value),
            stream: rhs.stream,
          };
        } else if (op.value == ".") {
          acc = {
            _: "outputvalue",
            value: Comp(acc.value, rhs.value),
            stream: rhs.stream,
          };
        } else if (op.value == "(") {
          // Function application `f(x)` is parsed as an infix `(` followed by a
          // closing `)`.
          let closeparen = char(")")(rhs.stream);
          if (closeparen._ == "parseerror") {
            return closeparen;
          }
          acc = {
            _: "outputvalue",
            value: App(acc.value, rhs.value),
            stream: closeparen.stream,
          };
        } else if (op.value == "[") {
          // List indexing operator `a[i]` is parsed as an infix `[` followed by
          // a closing `]`.
          let closeparen = char("]")(rhs.stream);
          if (closeparen._ == "parseerror") {
            return closeparen;
          }
          acc = {
            _: "outputvalue",
            value: Idx(acc.value, rhs.value),
            stream: closeparen.stream,
          };
        } else if (op.value == "->") {
          acc = {
            _: "outputvalue",
            value: Pi("", acc.value, rhs.value),
            stream: rhs.stream,
          };
        } else if (op.value == "++") {
          acc = {
            _: "outputvalue",
            value: Cat(acc.value, rhs.value),
            stream: rhs.stream,
          };
        } else if (op.value == ":") {
          acc = {
            _: "outputvalue",
            value: Ann(acc.value, rhs.value),
            stream: rhs.stream,
          };
        }
      } else {
        break;
      }
    }

    return acc;
  };

// parses an argument list to an application, for example: `(x,y,z)`.
// This parses to a tree of App terms.
const appArgumentList = (lhs: Expression): Parser<Expression> =>
  spc(
    parenthesis(
      spc(
        map(join(expression(0), spc(char(","))), (args) =>
          // Application is left-associative, so form the following tree of
          // applications, i.e. f(x)(y) == (f(x))(y):
          //      ap
          //     /  \
          //    ap   y
          //   /  \
          //  f    x
          args.reduce((acc, curr) => App(acc, curr), lhs)
        )
      )
    )
  );

// strip removes origins and syntax nodes from the term tree.
export function strip(t: Expression): Expression {
  switch (t._) {
    // case "var":
    //   return t;
    case "lam":
      return Abs(identifier2str(t.name), strip(t.body));
    case "self":
      return Self(t.name, strip(t.body));
    case "app":
      return App(strip(t.func), strip(t.arg));
    case "ann":
      return Ann(strip(t.term), strip(t.type));
    case "pi":
      return Pi(t.name, strip(t.from), strip(t.body));
    case "par":
    case "star":
    case "ref":
    case "id":
    // case "hole":
    case "int":
    // case "str":
    case "key":
    case "err":
      return t;
    case "orig":
    case "syn":
    case "label":
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
    // case "rel":
    //   throw "strip: unexpected rel";
    case "neg":
      return IntNeg(strip(t.exp));
    case "add":
      return IntPlus(strip(t.lhs), strip(t.rhs));
    case "sub":
      return IntSub(strip(t.lhs), strip(t.rhs));
    case "mul":
      return IntMul(strip(t.lhs), strip(t.rhs));
    case "div":
      return IntDiv(strip(t.lhs), strip(t.rhs));
    case "eq":
      return Eq(strip(t.lhs), strip(t.rhs));
    case "neq":
      return Neq(strip(t.lhs), strip(t.rhs));
    case "gt":
      return Gt(strip(t.lhs), strip(t.rhs));
    case "gte":
      return Gte(strip(t.lhs), strip(t.rhs));
    case "lt":
      return Lt(strip(t.lhs), strip(t.rhs));
    case "lte":
      return Lte(strip(t.lhs), strip(t.rhs));
    case "comp":
      return Comp(strip(t.lhs), strip(t.rhs));
    case "idx":
      return Idx(strip(t.arr), strip(t.idx));
    case "cat":
      return Cat(strip(t.lhs), strip(t.rhs));
    case "and":
      return And(strip(t.lhs), strip(t.rhs));
    case "or":
      return Or(strip(t.lhs), strip(t.rhs));
    case "cons":
      return Cons(strip(t.head), strip(t.tail));
    case "nil":
      return Nil();
    // default:
    //   throw `strip: not handled ${t._}`;
  }
}

// serialise outputs the term tree in the same syntax as the typescript
// implementation. This is useful for quickly generating code for a term to be
// used in tests.
export function serialise(t: Expression): string {
  switch (t._) {
    case "ref":
      return `Ref("${t.name}")`;
    case "int":
      return `IntLit(${t.num})`;
    case "err":
      return `ParseError(${t.msg})`;
    case "neg":
      return `IntNeg(${serialise(t.exp)})`;
    case "add":
      return `IntPlus(${serialise(t.lhs)}, ${serialise(t.rhs)})`;
    case "sub":
      return `IntSub(${serialise(t.lhs)}, ${serialise(t.rhs)})`;
    case "mul":
      return `IntMul(${serialise(t.lhs)}, ${serialise(t.rhs)})`;
    case "div":
      return `IntDiv(${serialise(t.lhs)}, ${serialise(t.rhs)})`;
    case "comp":
      return `Comp(${serialise(t.lhs)}, ${serialise(t.rhs)})`;
    case "app":
      return `App(${serialise(t.func)}, ${serialise(t.arg)})`;
    case "pi":
      return `Pi("${t.name}", ${serialise(t.from)}, ${serialise(t.body)})`;
    case "ann":
      return `Ann(${serialise(t.term)}, ${serialise(t.type)})`;
    case "idx":
      return `Idx(${serialise(t.arr)}, ${serialise(t.idx)})`;
    case "cat":
      return `Cat(${serialise(t.lhs)}, ${serialise(t.rhs)})`;
    case "gt":
      return `Gt(${serialise(t.lhs)}, ${serialise(t.rhs)})`;
    case "lt":
      return `Lt(${serialise(t.lhs)}, ${serialise(t.rhs)})`;
    case "gte":
      return `Gte(${serialise(t.lhs)}, ${serialise(t.rhs)})`;
    case "lte":
      return `Lte(${serialise(t.lhs)}, ${serialise(t.rhs)})`;
    case "eq":
      return `Eq(${serialise(t.lhs)}, ${serialise(t.rhs)})`;
    case "neq":
      return `Neq(${serialise(t.lhs)}, ${serialise(t.rhs)})`;
    case "and":
      return `And(${serialise(t.lhs)}, ${serialise(t.rhs)})`;
    case "or":
      return `Or(${serialise(t.lhs)}, ${serialise(t.rhs)})`;
    case "cons":
      return `Cons(${serialise(t.head)}, ${serialise(t.tail)})`;
    case "nil":
      return `Nil()`;
    case "lam":
      return `Abs("${identifier2str(t.name)}", ${serialise(t.body)})`;
    case "orig":
      return `Orig(${t.start}, ${t.end}, ${serialise(t.child)})`;
    case "id":
      return `Id(${t.name})`;
    case "key":
      return `Key(${t.key})`;
    case "syn":
      return `Syntax(${serialise(t.syntax)})`;
    case "case":
      return `Case(${serialise(t.name)},[${t.branches
        .map((b) => `Branch(${serialise(b.constructor)}, ${serialise(b.term)})`)
        .join(",")}])`;
    case "let":
      return `Let(${serialise(t.name)}, ${serialise(t.expr)}, ${serialise(
        t.body
      )})`;

    case "if":
      return `If(${serialise(t.condition)}, ${serialise(
        t.trueBranch
      )}, ${serialise(t.falseBranch)})`;
    case "par":
      return `Par(${t.name})`;
    case "label":
      return `Label(${t.label}, ${serialise(t.child)})`;
    case "self":
      return `Self(${t.name}, ${serialise(t.body)})`;
    case "star":
      return `Star()`;
    // default:
    //   throw new Error(`unhandled node: ${t._}`);
  }
}
