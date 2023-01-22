// check implements a typechecker for this language
import { Context, Term, Type, App, Abs, Var, Ann, Pi, Def, Star } from "./ast";

var _ = require("lodash");

export const typeEq = (A: Type, B: Type) => _.isEqual(A, B);

export const addTermToCtx = (
  ctx: Context,
  name: string,
  type: Type
): Context => [...ctx, { type: "bind", name: name, typ: type }];

export const lookupType = (
  ctx: Context,
  index: number,
  name: string | undefined = undefined
): Type => {
  if (index >= ctx.length) {
    throw `variable ${name} not found in context`;
  }
  let x = ctx[ctx.length - index - 1];
  if (x.type == "bind") {
    // for debugging.
    if (name && x.name != name) {
      throw `name mismatch: got ${name}; expected ${x.name}`;
    }
    return x.typ;
  } else {
    throw `could not find variable binding for ${index}`;
  }
};

type TypecheckError = {
  _: "typecheckerror";
  msg: string;
};

const TypecheckError = (msg: string): TypecheckError => ({
  _: "typecheckerror",
  msg: msg,
});

interface Result {
  _: "result";
  term: Term;
  type: Type;
}

const Result = (term: Term, type: Term): Result => ({
  _: "result",
  term: term,
  type: type,
});

// infer the type of a term. This produces an annotated version of the term
// whose type can always be checked.
export const infer = (ctx: Context, term: Term): Result | TypecheckError =>
  tc(ctx, term);

// check that the given term has the expected type.
export const check = (
  ctx: Context,
  tm: Term,
  ty: Term
): Result | TypecheckError => {
  switch (ty._) {
    case "ann":
      return check(ctx, tm, ty.term);
    default:
      return tc(ctx, tm, ty);
  }
};

// Make sure that the term is a "type" (i.e. that it has type 'Type')
export const checkStar = (ctx: Context, term: Term): Result | TypecheckError =>
  tc(ctx, term, Star());

// check a term, producing an elaborated term where all of the type annotations
// have been filled in. The second argument is undefined in inference mode and
// an expected type (must be in whnf) in checking mode.
export const tc = (
  ctx: Context,
  term: Term,
  type?: Term // this is undefined in inference mode.
): Result | TypecheckError => {
  switch (term._) {
    case "pi": {
      // Γ ⊢ A <= ★
      // Γ,x:A ⊢ B <= ★
      // ----------------
      // Γ ⊢ Πx:A. B => ★
      let elA = check(ctx, term.from, Star());
      if (elA._ == "typecheckerror") {
        return elA;
      }
      let elB = check(addTermToCtx(ctx, "x", term.from), term.to, Star());
      if (elB._ == "typecheckerror") {
        return elB;
      }
      return Result(Pi(elA.term, elB.term), Star());
    }
    case "star":
      // ----------------
      // Γ ⊢ ★ => ★
      return Result(Star(), Star());
    case "var":
      // Look up its type in the context.
      if (term.index >= ctx.length) {
        return TypecheckError("undefined variable " + term.name);
      }
      return Result(term, lookupType(ctx, term.index, term.name));
    case "lam":
      // Γ,x:A ⊢ a <= B
      // ----------------
      // Γ ⊢ λx.a <= Πx:A. B
      if (type == undefined) {
        // infer the type of a lambda expression, when an annotation on the
        // binder is present
        if (term.argtype == undefined) {
          return TypecheckError("lambda requires annotation");
        }
        let atyA = checkStar(ctx, term.argtype);
        if (atyA._ == "typecheckerror") {
          return atyA;
        }
        // infer the type of the body of the lambda expression
        let inferred = infer(
          addTermToCtx(ctx, term.name, atyA.term),
          term.body
        );
        if (inferred._ == "typecheckerror") {
          return inferred;
        }
        let ebody = inferred.term;
        let atyB = inferred.type;
        return Result(Abs(term.name, ebody, term.argtype), Pi(atyA.term, atyB));
      }
      // checking mode.
      if (type._ != "pi") {
        return TypecheckError("expected pi type");
      }
      // we add the bound variable x:A to the context (assuming that x has type
      // A) then using that context we check the body has type B.
      let ebody = check(
        addTermToCtx(ctx, term.name, type.from),
        term.body,
        type.to
      );
      if (ebody._ == "typecheckerror") {
        return ebody;
      }
      return Result(
        Abs(term.name, Ann(ebody.term, ebody.type), term.argtype),
        type
      );
    case "app": {
      let t1 = term.left;
      let t2 = term.right;
      let t1T = infer(ctx, t1);
      if (t1T._ == "typecheckerror") {
        return t1T;
      }
      let et1 = t1T.term;
      let ty1 = t1T.type;
      if (ty1._ != "pi") {
        return TypecheckError("expected pi type");
      }
      let tyA = ty1.from;
      let tyB = ty1.to;
      let arg = check(ctx, t2, tyA);
      if (arg._ == "typecheckerror") {
        return arg;
      }
      let et2 = arg.term;
      // Substitute the argument in the pi type with the elaborated argument to
      // the app inside of tyB.
      return Result(App(et1, et2), substTop(et2, tyB));
    }
    case "ann": {
      let typ = checkStar(ctx, term.typ);
      if (typ._ == "typecheckerror") {
        return typ;
      }
      // check the annotated type matches the computed type.
      let ty = check(ctx, term.term, term.typ);
      if (ty._ == "typecheckerror") {
        return ty;
      }
      return Result(ty.term, ty.type);
    }
    case "ref":
      throw "ref not implemented";
  }
};

// Shifting renumbers the indices of the free variables in a term.
export function shift(d: number, c: number, t: Term): Term {
  switch (t._) {
    case "var":
      return t.index >= c ? Var(t.name, t.index + d) : t;
    case "lam":
      return Abs(t.name, shift(d, c + 1, t.body));
    case "app":
      return App(shift(d, c, t.left), shift(d, c, t.right));
    case "ann":
      return Ann(shift(d, c, t.term), t.typ);
    case "pi":
      return Pi(shift(d, c, t.from), shift(d, c + 1, t.to));
    case "star":
    case "ref":
      return t;
  }
}

// Given a term t, find all Vars with index j and replace them with the term s.
export function subst(j: number, s: Term, c: number, t: Term): Term {
  switch (t._) {
    case "var":
      // Substitute in the term s, renumbering any free variables so the
      // expression is consistent.
      return t.index == j + c ? shift(c, 0, s) : t;
    case "lam":
      return Abs(t.name, subst(j, s, c + 1, t.body));
    case "app":
      return App(subst(j, s, c, t.left), subst(j, s, c, t.right));
    case "ann":
      return Ann(subst(j, s, c, t.term), t.typ);
    case "pi":
      return Pi(subst(j, s, c, t.from), subst(j, s, c + 1, t.to));
    case "star":
    case "ref":
      return t;
  }
}

// The term being substituted for the bound variable is first shifted up by one, then the
// substitution is made, and then the whole result is shifted down by one to account for the
// fact that the bound variable has been used up.
export function substTop(s: Term, t: Term): Term {
  return shift(-1, 0, subst(0, shift(1, 0, s), 0, t));
}

export function isValue(term: Term): boolean {
  return term._ == "lam";
}

// Big-step evaluation for the given term.
export function evaluate(defs: Def[], term: Term): Term {
  switch (term._) {
    case "app":
      let e1 = evaluate(defs, term.left);
      let e2 = evaluate(defs, term.right);
      if (e1._ == "lam" && isValue(e2)) {
        return substTop(e2, e1.body);
      }
      return App(e1, e2);
    case "lam":
      return term;
    // throw "cannot reduce Abs";
    case "var":
      throw "cannot reduce Var";
    case "ann": // ignored at runtime
      return evaluate(defs, term.term);
    case "ref":
      const match = defs.filter((d) => d.name == term.name);
      if (match.length == 0) {
        return term;
      }
      return evaluate(defs, match[0].term);
    case "pi":
      throw "can't eval pi";
    case "star":
      throw "can't eval star";
  }
}
