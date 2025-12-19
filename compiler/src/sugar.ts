import { ADT } from "./ast";
import { addTermToCtx, Context } from "./context";
import { identifier2str, type Expression } from "./pratt";

// Abs is a lambda abstraction.
export type Abs = {
  _: "lam";
  name: Origin | Identifier; // name of the binder
  body: CTerm; // the body of the abstraction
};

export const Abs = (name: string, body: CTerm): Abs => ({
  _: "lam",
  name: Identifier(name),
  body: body,
});

export const AbsI = (name: Origin | Identifier, body: CTerm): Abs => ({
  _: "lam",
  name: name,
  body: body,
});

export type Idx = {
  _: "idx";
  arr: CTerm;
  idx: CTerm;
};

export const Idx = (arr: CTerm, idx: CTerm): Idx => ({
  _: "idx",
  arr: arr,
  idx: idx,
});

export type App = {
  _: "app";
  func: CTerm;
  arg: CTerm;
};

export const App = (func: CTerm, arg: CTerm): App => ({
  _: "app",
  func: func,
  arg: arg,
});

// Π is the type of functions.
export type Pi = {
  _: "pi";
  from: CTerm;
  body: CTerm;
  name: string; // name of the binder
};

export const Pi = (name: string, from: CTerm, to: CTerm): Pi => ({
  _: "pi",
  from: from,
  body: to,
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

// Π is the type of functions.
export type Ann = {
  _: "ann";
  term: CTerm;
  type: CTerm;
};

export const Ann = (term: CTerm, type: CTerm): Ann => ({
  _: "ann",
  term: term,
  type: type,
});

// An element of a cons-list.
export type Cons = {
  _: "cons";
  head: CTerm;
  tail: CTerm;
};

export const Cons = (term: CTerm, next: CTerm): Cons => ({
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
  term: CTerm;
};

export const Branch = (
  constructor: Identifier | Origin,
  term: CTerm
): Branch => ({
  constructor: constructor,
  term: term,
});

export type Case = {
  _: "case";
  name: CTerm; // This should be a Par or a Ref.
  branches: Branch[];
};

export const Case = (name: CTerm, branches: Branch[]): Case => ({
  _: "case",
  name: name,
  branches: branches,
});

export type Let = {
  _: "let";
  name: Origin | Identifier;
  expr: CTerm;
  body: CTerm;
};

export const Let = (
  name: Origin | Identifier,
  expr: CTerm,
  body: CTerm
): Let => ({
  _: "let",
  name: name,
  expr: expr,
  body: body,
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
  child: CTerm;
};

export const Syntax = (syntax: Origin, child: CTerm): Syntax => ({
  _: "syn",
  syntax: syntax,
  child: child,
});

// An integer literal
export type IntLit = { _: "int"; num: number };

export const IntLit = (x: number): IntLit => ({
  _: "int",
  num: x,
});

// A string literal
export type StringLit = { _: "str"; str: string };

export const StringLit = (x: string): StringLit => ({
  _: "str",
  str: x,
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

// A Label is a way of annotating terms with a string. This allows us to
// determine which branch of an if statement a node belongs to, for example.
export type Label = {
  _: "label";
  label: string;
  child: CTerm;
};

export const Label = (label: string, child: CTerm): Label => ({
  _: "label",
  label,
  child,
});

// Self is a way of abstracting out the value currently being typechecked so
// that it can be used within the body.
export type Self = {
  _: "self";
  name: string; // name of the binder
  body: CTerm; // the body of the abstraction
};

export const Self = (name: string, body: CTerm): Self => ({
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

export type Origin = {
  _: "orig";
  start: number;
  end: number;
  child: CTerm;
};

export const Origin = (start: number, end: number, child: CTerm): Origin => ({
  _: "orig",
  start: start,
  end: end,
  child: child,
});

export type CTerm =
  | Var
  | IntLit
  | StringLit
  | App
  | Ref
  | Abs
  | Pi
  | Ann
  | ParseError
  | Origin
  | Identifier
  | Key
  | Syntax
  | Case
  | Let
  | Label
  | Self
  | Star
  | Hole;

// Transform expression nodes into native code, i.e. function applications of
// standard library functions. For example `x > y` becomes `gt(x,y)`.
export const desugarExpression = (expression: Expression): CTerm => {
  switch (expression._) {
    case "ref":
      return Ref(expression.name);
    case "int":
      return IntLit(expression.num);
    case "err":
      return ParseError(expression.msg);
    case "app":
      return App(
        desugarExpression(expression.func),
        desugarExpression(expression.arg)
      );
    case "pi":
      return Pi(
        expression.name,
        desugarExpression(expression.from),
        desugarExpression(expression.body)
      );
    case "ann":
      return Ann(
        desugarExpression(expression.term),
        desugarExpression(expression.type)
      );
    case "neg":
      return App(Ref("neg"), desugarExpression(expression.exp));
    case "add":
      return App(
        App(Ref("add"), desugarExpression(expression.lhs)),
        desugarExpression(expression.rhs)
      );
    case "sub":
      return App(
        App(Ref("sub"), desugarExpression(expression.lhs)),
        desugarExpression(expression.rhs)
      );
    case "mul":
      return App(
        App(Ref("mul"), desugarExpression(expression.lhs)),
        desugarExpression(expression.rhs)
      );
    case "div":
      return App(
        App(Ref("div"), desugarExpression(expression.lhs)),
        desugarExpression(expression.rhs)
      );
    case "idx":
      return App(
        App(Ref("idx"), desugarExpression(expression.idx)),
        desugarExpression(expression.arr)
      );
    case "cat":
      return App(
        App(Ref("append"), desugarExpression(expression.lhs)),
        desugarExpression(expression.rhs)
      );
    case "gt":
      return App(
        App(Ref("gt"), desugarExpression(expression.lhs)),
        desugarExpression(expression.rhs)
      );
    case "lt":
      return App(
        App(Ref("lt"), desugarExpression(expression.lhs)),
        desugarExpression(expression.rhs)
      );
    case "gte":
      return App(
        App(Ref("gte"), desugarExpression(expression.lhs)),
        desugarExpression(expression.rhs)
      );
    case "lte":
      return App(
        App(Ref("lte"), desugarExpression(expression.lhs)),
        desugarExpression(expression.rhs)
      );
    case "eq":
      return App(
        App(Ref("eq"), desugarExpression(expression.lhs)),
        desugarExpression(expression.rhs)
      );
    case "neq":
      return App(
        App(Ref("neq"), desugarExpression(expression.lhs)),
        desugarExpression(expression.rhs)
      );
    case "and":
      return App(
        App(Ref("and"), desugarExpression(expression.lhs)),
        desugarExpression(expression.rhs)
      );
    case "or":
      return App(
        App(Ref("or"), desugarExpression(expression.lhs)),
        desugarExpression(expression.rhs)
      );
    case "cons":
      return App(
        App(
          App(Ref("cons"), Hole(Math.random())),
          desugarExpression(expression.head)
        ),
        desugarExpression(expression.tail)
      );
    case "nil":
      return App(Ref("nil"), Hole(Math.random()));
    case "comp":
      // Should this be a function? Or just compose directly?
      return App(
        App(Ref("comp"), desugarExpression(expression.lhs)),
        desugarExpression(expression.rhs)
      );
    case "var":
      return Var(expression.name, expression.index);
    case "str":
      return StringLit(expression.str);
    case "lam":
      return AbsI(
        desugarExpression(expression.name) as Origin | Identifier,
        desugarExpression(expression.body)
      );
    case "orig":
      return Origin(
        expression.start,
        expression.end,
        desugarExpression(expression.child)
      );
    case "id":
      return Identifier(expression.name);
    case "key":
      return Key(expression.key);
    case "syn":
      return Syntax(
        desugarExpression(expression.syntax) as Origin,
        desugarExpression(expression.child)
      );
    case "case":
      return Case(
        desugarExpression(expression.name),
        expression.branches.map((c) =>
          Branch(
            desugarExpression(c.constructor) as Origin | Identifier,
            desugarExpression(c.term)
          )
        )
      );
    case "if":
      // If statements are desugared in `fixupRefs`.
      throw new Error(`unexpected if`);
    case "let":
      return Let(
        desugarExpression(expression.name) as Origin | Identifier,
        desugarExpression(expression.expr),
        desugarExpression(expression.body)
      );
    case "par":
      throw new Error(`unexpected par`);
    case "label":
      return Label(expression.label, desugarExpression(expression.child));
    case "self":
      return Self(expression.name, desugarExpression(expression.body));
    case "star":
      return Star();
    case "hole":
      return Hole(expression.id);
  }
};

// strip removes origins and syntax nodes from the term tree.
export function strip(t: CTerm): CTerm {
  switch (t._) {
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
    case "star":
    case "ref":
    case "id":
    case "int":
    case "str":
    case "key":
    case "err":
    case "var":
    case "hole":
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
  }
}

// Fix Ref nodes that should reference the context instead.
export const fixupRefs = (
  t: CTerm,
  ann: CTerm | undefined,
  adts: Map<string, ADT>,
  ctx: Context
): CTerm => {
  switch (t._) {
    case "ann":
      const desugaredType = fixupRefs(t.type, undefined, adts, ctx);
      return Ann(fixupRefs(t.term, desugaredType, adts, ctx), desugaredType);
    case "app":
      return App(
        fixupRefs(t.func, undefined, adts, ctx),
        fixupRefs(t.arg, undefined, adts, ctx)
      );
    case "lam":
      // The type in this context is not important so just set it as *.
      return AbsI(
        t.name,
        fixupRefs(
          t.body,
          undefined,
          adts,
          addTermToCtx(ctx, identifier2str(t.name), Star())
        )
      );
    case "pi":
      return Pi(
        t.name,
        fixupRefs(t.from, undefined, adts, ctx),
        fixupRefs(t.body, undefined, adts, addTermToCtx(ctx, t.name, Star()))
      );
    case "self":
      return Self(
        t.name,
        fixupRefs(t.body, undefined, adts, addTermToCtx(ctx, t.name, Star()))
      );
    case "case":
      // We can't desugar case expressions at this point because we need to
      // infer the type of the term we're destructuring. This can only happen
      // while we're typechecking.
      return Case(
        fixupRefs(t.name, undefined, adts, ctx),
        t.branches.map((b) =>
          Branch(b.constructor, fixupRefs(b.term, undefined, adts, ctx))
        )
      );
    case "let":
      // the type of the newly created bound variable is required when adding it
      // to the context, so we must defer processing this let statement to the
      // typechecking stage.
      return Let(
        t.name,
        fixupRefs(t.expr, undefined, adts, ctx),
        fixupRefs(
          t.body,
          undefined,
          adts,
          addTermToCtx(ctx, identifier2str(t.name), Star())
        )
      );

    case "ref": {
      // At this point we're still unsure whether this node is a Var or a Ref.
      // So look it up first and if a Var exists then use that.
      for (let i = 0; i < ctx.length; i++) {
        const binding = ctx[ctx.length - i - 1];
        if (binding.name == t.name) {
          return Var(binding.name, i);
        }
      }
      return t;
    }
    case "int": {
      let term: CTerm = Ref("zero");
      for (let i = 0; i < t.num; i++) {
        term = App(Ref("succ"), term);
      }
      return term;
    }
    case "orig":
      return Origin(t.start, t.end, fixupRefs(t.child, ann, adts, ctx));
    case "syn":
      return Syntax(t.syntax, fixupRefs(t.child, ann, adts, ctx));
    case "label":
      return Label(t.label, fixupRefs(t.child, ann, adts, ctx));
    case "star":
    case "var":
    case "id":
    case "key":
    case "hole":
    case "str":
    case "err":
      return t;
  }
};
