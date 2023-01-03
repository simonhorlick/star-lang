// check implements a typechecker for this language
import { Context, Term, Type } from "./ast";
import { Arrow, Star } from "./evaluation";
import { pretty, prettyT } from "./pretty";

var _ = require("lodash");

export const typeEq = (A: Type, B: Type) => _.isEqual(A, B);

export const lookupType = (ctx: Context, index: number) => {
  let x = ctx[ctx.length - index - 1];
  return x.type == "bind" ? x.typ : Star();
};

export const GetType = (ctx: Context, term: Term): Type => {
  console.log(
    `Γ = ${ctx
      .map((v) => `${v.name}:${v.type == "bind" ? prettyT(v.typ) : "★"}`)
      .join(",")}; term = ${pretty(term)}`
  );

  switch (term._) {
    case "lam":
      // This is the definition of T-Abs:
      //    Γ,x:T1 ⊢ t2:T2
      // ------------------- T-Abs
      // Γ ⊢ λx:T1. t2:T1→T2
      // Append the bound variable to the context.
      let newCtx: Context = [
        ...ctx,
        { type: "bind", name: term.name, typ: term.bindType },
      ];
      const T1 = term.bindType;
      const T2 = GetType(newCtx, term.body);
      return Arrow(T1, T2);
    case "var":
      // Look up its type in the context.
      return lookupType(ctx, term.index);
    case "app":
      // the type of an abstraction t1 will be an arrow T11->T12, so if we're
      // applying t1(t2) we're going to get T12.
      // Γ ⊢ t1:T11→T12    Γ ⊢ t2:T11
      // ---------------------------- T-App
      //        Γ ⊢ t1(t2):T12
      const t1 = term.left;
      let t1Type = GetType(ctx, t1);
      if (t1Type._ == "arrow") {
        return t1Type.to;
      } else {
        throw "cannot get type for " + t1Type._;
      }
    default:
      throw "cannot get type for " + term._;
  }
};

export const Check = (ctx: Context, term: Term): Array<{ msg: string }> => {
  console.log(
    `Γ = ${ctx
      .map((v) => `${v.name}:${v.type == "bind" ? prettyT(v.typ) : "★"}`)
      .join(",")}; term = ${pretty(term)}`
  );

  switch (term._) {
    case "app":
      // In the term f(x), when applying x:X to f:A->B, ensure X == A.
      let x = term.right;
      let f = term.left;
      let fType = GetType(ctx, f);
      if (fType._ == "arrow") {
        const xType = GetType(ctx, x);
        if (!typeEq(fType.from, xType)) {
          return [
            {
              msg: `expected ${prettyT(fType.from)}; ${prettyT(xType)}`,
            },
          ];
        } else {
          return []; // ok
        }
      } else {
        return [{ msg: `expected arrow type` }];
      }
    case "lam": {
      let newCtx: Context = [
        ...ctx,
        { type: "bind", name: term.name, typ: term.bindType },
      ];
      return Check(newCtx, term.body);
    }
    case "all": {
      let newCtx: Context = [...ctx, { type: "tbind", name: term.name }];
      return Check(newCtx, term.body);
    }
    case "var":
      // A variable can be of any type, but it must exist in the context.
      if (term.index < ctx.length) {
        return [];
      } else {
        return [{ msg: `undefined variable ${term.name}` }];
      }
    case "ann": {
      // Check the annotated type matches the computed type.
      const type = GetType(ctx, term.term);
      if (!typeEq(term.typ, type)) {
        return [
          {
            msg: `expected ${prettyT(term.typ)}; got ${prettyT(type)}`,
          },
        ];
      } else {
        return []; // ok
      }
    }
    case "ref":
      throw "unexpected ref";
  }
};
