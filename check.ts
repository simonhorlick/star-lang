// check implements a typechecker for this language
import { Context, Term, Type } from "./ast";
import { All, Arrow, Star, typeShift, typeSubstTop } from "./evaluation";
import { pretty, prettyT } from "./pretty";

var _ = require("lodash");

export const typeEq = (A: Type, B: Type) => _.isEqual(A, B);

export const lookupType = (ctx: Context, index: number) => {
  let x = ctx[ctx.length - index - 1];
  return x.type == "bind" ? x.typ : Star();
};

type TypecheckError = {
  _: "typecheckerror";
  msg: string;
};

const TypecheckError = (msg: string): TypecheckError => ({
  _: "typecheckerror",
  msg: msg,
});

export const GetType = (ctx: Context, term: Term): Type | TypecheckError => {
  console.log(
    `Γ = ${ctx
      .map((v) => `${v.name}:${v.type == "bind" ? prettyT(v.typ) : "★"}`)
      .join(",")}; term = ${pretty(term)}`
  );

  // FIXME: This needs to follow the inversion lemmas rather than the
  // definitions.

  switch (term._) {
    case "var":
      // Look up its type in the context.
      if (term.index >= ctx.length) {
        return TypecheckError("undefined variable " + term.name);
      }
      return lookupType(ctx, term.index);
    case "lam": {
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
      if (T2._ == "typecheckerror") {
        return T2;
      }
      return Arrow(T1, typeShift(-1, T2));
    }
    case "app": {
      // the type of an abstraction t1 will be an arrow T11->T12, so if we're
      // applying t1(t2) we're going to get T12.
      // Γ ⊢ t1:T11→T12    Γ ⊢ t2:T11
      // ---------------------------- T-App
      //        Γ ⊢ t1(t2):T12
      const t1 = term.left;
      const t2 = term.right;
      let tyT1 = GetType(ctx, t1);
      let tyT2 = GetType(ctx, t2);
      if (tyT1._ == "typecheckerror") {
        return tyT1;
      }
      if (tyT2._ == "typecheckerror") {
        return tyT2;
      }
      if (tyT1._ == "arrow") {
        let tyT11 = tyT1.from;
        let tyT12 = tyT1.to;
        if (typeEq(tyT2, tyT11)) {
          return tyT12;
        } else {
          return TypecheckError("parameter type mismatch");
        }
      } else {
        return TypecheckError("expected arrow type");
      }
    }
    case "tabs": {
      //   Γ,X ⊢ t2:T2
      // --------------- T-TAbs
      // Γ ⊢ ΛX.t2:∀X.T2
      // Append the bound variable to the context.
      let newCtx: Context = [...ctx, { type: "tbind", name: term.name }];
      const T2 = GetType(newCtx, term.body);
      if (T2._ == "typecheckerror") {
        return T2;
      }
      return All(term.name, T2);
    }
    case "tapp": {
      let tyT1 = GetType(ctx, term.left);
      let tyT2 = term.right;
      if (tyT1._ == "typecheckerror") {
        return tyT1;
      }
      if (tyT1._ == "all") {
        let tyT12 = tyT1.to;
        return typeSubstTop(tyT2, tyT12);
      } else {
        return TypecheckError("expected All");
      }
    }
    case "ann": {
      let computed = GetType(ctx, term.term);
      let annotated = term.typ;
      if (computed._ == "typecheckerror") {
        return computed;
      }
      if (!typeEq(computed, annotated)) {
        return TypecheckError(
          `expected ${prettyT(annotated)}; got ${prettyT(computed)}`
        );
      }
      return computed;
    }
    case "ref":
      throw "unexpected ref";
  }
};
