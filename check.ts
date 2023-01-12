// check implements a typechecker for this language
import { Binding, Context, Kind, Term, Type, VariableBinding } from "./ast";
import {
  All,
  Arrow,
  Star,
  typeShift,
  typeSubstTop,
  KArrow,
} from "./evaluation";
import { pretty, prettyK, prettyT, printCtx } from "./pretty";

var _ = require("lodash");

export const typeEq = (A: Type, B: Type) => _.isEqual(A, B);
export const kindEq = (A: Kind, B: Kind) => _.isEqual(A, B);

export const addTermToCtx = (
  ctx: Context,
  name: string,
  type: Type
): Context => [...ctx, { type: "bind", name: name, typ: type }];
export const addTypeToCtx = (
  ctx: Context,
  name: string,
  kind: Kind
): Context => [...ctx, { type: "tbind", name: name, kind: kind }];

// Shift any type variables that occur inside the types in variable
// bindings.
function bindingshift(d: number, bind: VariableBinding): VariableBinding {
  return { type: "bind", name: bind.name, typ: typeShift(d, bind.typ) };
}

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

    // We need to shift the type variables to ensure they still point
    // at the correct type in the context.
    let shifted = bindingshift(index + 1, x);
    return shifted.typ;
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
    case "arrow": {
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
    case "all":
      //  Γ,X::K1 ⊢ T2::★
      // ------------------ K-All
      // Γ ⊢ (∀X::K1.T2)::★
      let tyT2 = type.to;
      let knK1 = type.kind;
      let newCtx = addTypeToCtx(ctx, type.name, knK1);
      let kindT2 = GetKind(newCtx, tyT2);
      if (kindT2._ == "typecheckerror") {
        return kindT2;
      }
      if (kindT2._ != "star") {
        return TypecheckError("star kind expected");
      }
      return Star();
    case "ers":
      return Star();
    case "ref":
      throw "not implemented";
    case "var":
      return lookupKind(ctx, type.index);
  }
};

export const GetType = (ctx: Context, term: Term): Type | TypecheckError => {
  console.log(`Γ = [${printCtx(ctx)}]; term = ${pretty(term, false)}`);

  // FIXME: This needs to follow the inversion lemmas rather than the
  // definitions.

  switch (term._) {
    case "var":
      // Look up its type in the context.
      if (term.index >= ctx.length) {
        return TypecheckError("undefined variable " + term.name);
      }
      return lookupType(ctx, term.index, term.name);
    case "lam": {
      // This is the definition of T-Abs:
      //   Γ ⊢ T1::★   Γ,x:T1 ⊢ t2:T2
      // ---------------------------- T-Abs
      //     Γ ⊢ (λx:T1. t2):T1→T2
      let T1 = term.bindType;
      let kindT1 = GetKind(ctx, T1);
      if (kindT1._ == "typecheckerror") {
        return kindT1;
      }

      if (kindT1._ != "star") {
        return TypecheckError("argument to λ must have kind ★");
      }

      // Append the bound variable to the context.
      let newCtx = addTermToCtx(ctx, term.name, T1);
      const T2 = GetType(newCtx, term.body);
      if (T2._ == "typecheckerror") {
        return T2;
      }
      // Why is this shifted in the book?
      return Arrow(T1, typeShift(-1, T2));
      // return Arrow(T1, T2);
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
      let simplifyT1 = simplifyty(ctx, tyT1);
      if (simplifyT1._ != "arrow") {
        return TypecheckError("expected arrow type");
      }

      // Ensure the type of the term we're applying to the arrow matches the
      // from type.
      let tyT11 = simplifyT1.from;
      let tyT12 = simplifyT1.to;
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
    case "tabs": {
      //       Γ,X::K1 ⊢ t2:T2
      // -------------------------- T-TAbs
      // Γ ⊢ (ΛX::K1. t2):∀X::K1.T2

      // Append the bound type variable to the context.
      let newCtx = addTypeToCtx(ctx, term.name, term.kind);
      const T2 = GetType(newCtx, term.body);
      if (T2._ == "typecheckerror") {
        return T2;
      }
      return All(term.name, T2, term.kind);
    }
    case "tapp": {
      // Γ ⊢ t1:∀X::K11.T12
      // Γ ⊢ T2::K11
      // --------------------- T-TApp
      // Γ ⊢ t1(T2) : [X/T]T12
      let tyT1 = GetType(ctx, term.left);
      let tyT2 = term.right;
      if (tyT1._ == "typecheckerror") {
        return tyT1;
      }
      if (tyT1._ != "all") {
        return TypecheckError("expected All");
      }
      let kindT2 = GetKind(ctx, tyT2);
      if (kindT2._ == "typecheckerror") {
        return kindT2;
      }
      if (!kindEq(tyT1.kind, kindT2)) {
      }
      let tyT12 = tyT1.to;
      return typeSubstTop(tyT2, tyT12);
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

// reduces the type
function simplifyty(ctx: Context, t: Type): Type {
  switch (t._) {
    case "all":
    case "arrow":
    case "ers":
    case "ref":
    case "var":
      return t;
    // TODO: Add TyApp(TyAbs) = typeSubstTop
  }
}
