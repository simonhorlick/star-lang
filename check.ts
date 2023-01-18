// check implements a typechecker for this language
import {
  Context,
  Kind,
  Term,
  Type,
  App,
  Abs,
  Var,
  Ann,
  Pi,
  Def,
  Star,
  TypeVariableBinding,
  VariableBinding,
} from "./ast";

import { pretty, prettyT, printCtx } from "./pretty";

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
      throw "name mismatch";
    }
    return x.typ;
  } else {
    throw `could not find variable binding for ${index}`;
  }
};

export const lookupKind = (
  ctx: Context,
  index: number,
  name: string | undefined = undefined
) => {
  if (index >= ctx.length) {
    throw `type ${name} not found in context`;
  }
  let x = ctx[ctx.length - index - 1];
  if (x.type == "tbind") {
    // for debugging.
    if (name && x.name != name) {
      throw "name mismatch";
    }
    return x.kind;
  } else {
    throw `could not find type variable binding for ${index}`;
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

export const GetKind = (ctx: Context, type: Type): Kind | TypecheckError => {
  switch (type._) {
    case "pi": {
      let kfrom = GetKind(ctx, type.from);
      if (kfrom._ == "typecheckerror") {
        return kfrom;
      }
      if (kfrom._ != "star") {
        return TypecheckError("star kind expected");
      }
      let kto = GetKind(ctx, type.to);
      if (kto._ == "typecheckerror") {
        return kto;
      }
      if (kto._ != "star") {
        return TypecheckError("star kind expected");
      }
      return Star();
    }
    case "ref": {
      const match = ctx.filter((d) => d.type == "tbind" && d.name == type.name);
      if (match.length == 0) {
        return TypecheckError("type not found: " + type.name);
      }
      return (match[0] as TypeVariableBinding).kind;
    }
    case "var":
      return lookupKind(ctx, type.index);
  }
};

export const GetType = (ctx: Context, term: Term): Type | TypecheckError => {
  console.log(`Γ = [${printCtx(ctx)}]; term = ${pretty(term, true)}`);
  switch (term._) {
    case "var":
      // Look up its type in the context.
      if (term.index >= ctx.length) {
        return TypecheckError("undefined variable " + term.name);
      }
      return lookupType(ctx, term.index, term.name);
    case "lam": {
      throw "can't get type of a lam";
      //   // This is the definition of T-Abs:
      //   //   Γ ⊢ T1::★   Γ,x:T1 ⊢ t2:T2
      //   // ---------------------------- T-Abs
      //   //     Γ ⊢ (λx:T1. t2):T1→T2
      //   let T1 = term.bindType;
      //   let kindT1 = GetKind(ctx, T1);
      //   if (kindT1._ == "typecheckerror") {
      //     return kindT1;
      //   }

      //   if (kindT1._ != "star") {
      //     return TypecheckError("argument to λ must have kind ★");
      //   }

      //   // Append the bound variable to the context.
      //   let newCtx = addTermToCtx(ctx, term.name, T1);
      //   const T2 = GetType(newCtx, term.body);
      //   if (T2._ == "typecheckerror") {
      //     return T2;
      //   }
      //   // We just added x:T1 to the context while calculating the type of T2, so
      //   // shift everything back down again here.
      //   return Pi(T1, T2);
    }
    case "app": {
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
      if (tyT1._ != "pi") {
        return TypecheckError("expected pi type");
      }

      // Ensure the type of the term we're applying to the arrow matches the
      // from type.
      let tyT11 = tyT1.from;
      let tyT12 = tyT1.to;
      if (!typeEq(tyT2, tyT11)) {
        return TypecheckError(
          `parameter type mismatch: while trying to apply parameter of type ${prettyT(
            tyT2,
            false
          )} to a function of type ${prettyT(tyT1, false)}`
        );
      }
      return tyT12;
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

// Shifting renumbers the indices of the free variables in a term.
export function termShift(d: number, c: number, t: Term): Term {
  switch (t._) {
    case "var":
      return t.index >= c ? Var(t.name, t.index + d) : t;
    case "lam":
      return Abs(t.name, termShift(d, c + 1, t.body));
    case "app":
      return App(termShift(d, c, t.left), termShift(d, c, t.right));
    case "ann":
    case "ref":
      return t;
  }
}

// Given a term t, find all Vars with index j and replace them with the term s.
export function termSubst(j: number, s: Term, c: number, t: Term): Term {
  switch (t._) {
    case "var":
      // Substitute in the term s, renumbering any free variables so the
      // expression is consistent.
      return t.index == j + c ? termShift(c, 0, s) : t;
    case "lam":
      return Abs(t.name, termSubst(j, s, c + 1, t.body));
    case "app":
      return App(termSubst(j, s, c, t.left), termSubst(j, s, c, t.right));
    case "ann":
      return Ann(termSubst(j, s, c, t.term), t.typ);
    case "ref":
      return t;
  }
}

// The term being substituted for the bound variable is first shifted up by one, then the
// substitution is made, and then the whole result is shifted down by one to account for the
// fact that the bound variable has been used up.
export function termSubstTop(s: Term, t: Term): Term {
  return termShift(-1, 0, termSubst(0, termShift(1, 0, s), 0, t));
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
      if (term.left._ == "lam" && isValue(term.right)) {
        return termSubstTop(term.right, term.left.body);
      }
      return App(e1, e2);
    case "lam":
      throw "cannot reduce Abs";
    case "var":
      throw "cannot reduce Var";
    case "ann": // ignored at runtime
      return evaluate(defs, term.term);
    case "ref":
      const match = defs.filter((d) => d.name == term.name);
      if (match.length == 0) {
        return term;
      }
      return match[0].term;
  }
}
