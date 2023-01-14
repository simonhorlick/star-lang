// check implements a typechecker for this language
import {
  Context,
  Kind,
  Term,
  Type,
  TypeVariableBinding,
  VariableBinding,
  App,
  Abs,
  Var,
  Ref,
  Ann,
  Arrow,
  TAbs,
  All,
  TApp,
  Def,
  TTApp,
  TTAbs,
  Star,
  KArrow,
} from "./ast";

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
    case "ref": {
      const match = ctx.filter((d) => d.type == "tbind" && d.name == type.name);
      if (match.length == 0) {
        return TypecheckError("type not found: " + type.name);
      }
      return (match[0] as TypeVariableBinding).kind;
    }
    case "var":
      return lookupKind(ctx, type.index);
    case "ttabs": {
      let tyT2 = type.body;
      let knK1 = type.kind;
      let newCtx = addTypeToCtx(ctx, type.name, knK1);

      let knK2 = GetKind(newCtx, tyT2);
      if (knK2._ == "typecheckerror") {
        return knK2;
      }

      return KArrow(knK1, knK2);
    }
    case "ttapp": {
      // Note that the implementation here is identical to that of tapp in
      // GetType, but with kinds instead of types.

      // Γ ⊢ T1::K11⇒K12   Γ ⊢ T2::K11
      // ---------------------------- K-App
      //        Γ ⊢ T1(T2)::K12
      const T1 = type.left;
      const T2 = type.right;
      let kindT1 = GetKind(ctx, T1);
      let kindT2 = GetKind(ctx, T2);
      if (kindT1._ == "typecheckerror") {
        return kindT1;
      }
      if (kindT2._ == "typecheckerror") {
        return kindT2;
      }
      if (kindT1._ != "karrow") {
        return TypecheckError("expected arrow kind");
      }

      // Ensure the kind of the type we're applying to the arrow matches the
      // from kind.
      let kindT11 = kindT1.from;
      let kindT12 = kindT1.to;
      if (!kindEq(kindT2, kindT11)) {
        return TypecheckError(
          `parameter kind mismatch: while trying to apply parameter of kind ${prettyK(
            kindT2
          )} to a function of kind ${prettyK(kindT1)}`
        );
      }
      return kindT12;
    }
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
      let styT1 = simplifyty(ctx, tyT1);
      if (styT1._ != "all") {
        return TypecheckError("expected All");
      }
      let kindT2 = GetKind(ctx, tyT2);
      if (kindT2._ == "typecheckerror") {
        return kindT2;
      }
      if (!kindEq(styT1.kind, kindT2)) {
      }
      let tyT12 = styT1.to;
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
export function simplifyty(ctx: Context, t: Type): Type {
  let simplified: Type;
  switch (t._) {
    case "all":
      return All(t.name, simplifyty(ctx, t.to), t.kind);
    case "arrow":
      return Arrow(simplifyty(ctx, t.from), simplifyty(ctx, t.to));
    case "ref":
      return t;
    case "var":
      return t;
    case "ttabs":
      return t;
    case "ttapp":
      simplified = TTApp(simplifyty(ctx, t.left), t.right);

      // Q-AppAbs
      // (λX:K11.T12)T2 ≡ [X/T2]T12
      if (simplified.left._ == "ttabs") {
        let tyT12 = simplified.left.body;
        let tyT2 = simplified.right;
        return typeSubstTop(tyT2, tyT12);
      }
      return simplified;
  }
}

// Shifting renumbers the indices of the free variables in a term.
export function termShift(d: number, t: Term): Term {
  // The shifting function below takes a “cutoff” parameter c that controls which variables should
  // be shifted.
  const walk = (d: number, c: number, t: Term): Term => {
    switch (t._) {
      case "var":
        if (t.index >= c) {
          return Var(t.name, t.index + d);
        } else {
          return Var(t.name, t.index);
        }
      case "lam":
        return Abs(t.name, walk(d, c + 1, t.body), t.bindType);
      case "app":
        return App(walk(d, c, t.left), walk(d, c, t.right));
      case "ann":
      case "ref":
      case "tabs":
      case "tapp":
        return t;
    }
  };
  return walk(d, 0, t);
}

// Given a term t, find all Vars with index j and replace them with the term s.
export function termSubst(j: number, s: Term, t: Term): Term {
  const walk = (j: number, s: Term, c: number, t: Term): Term => {
    switch (t._) {
      case "var":
        if (t.index == j + c) {
          // Substitute in the term s, renumbering any free variables so the
          // expression is consistent.
          return termShift(c, s);
        } else {
          return Var(t.name, t.index);
        }
      case "lam":
        return Abs(t.name, walk(j, s, c + 1, t.body), t.bindType);
      case "app":
        return App(walk(j, s, c, t.left), walk(j, s, c, t.right));
      case "tabs":
        return TAbs(t.name, walk(j, s, c + 1, t.body), t.kind);
      case "tapp":
        return TApp(walk(j, s, c, t.left), t.right);
      case "ann":
        return Ann(walk(j, s, c, t.term), t.typ);
      case "ref":
        return t;
    }
  };
  return walk(j, s, 0, t);
}

// The term being substituted for the bound variable is first shifted up by one, then the
// substitution is made, and then the whole result is shifted down by one to account for the
// fact that the bound variable has been used up.
export function termSubstTop(s: Term, t: Term): Term {
  return termShift(-1, termSubst(0, termShift(1, s), t));
}

function typeShiftAbove(d: number, c: number, tyT: Type): Type {
  const walk = (c: number, ty: Type): Type => {
    switch (ty._) {
      case "var":
        if (ty.index >= c) {
          return Var(ty.name, ty.index + d);
        } else {
          return Var(ty.name, ty.index);
        }
      case "arrow":
        return Arrow(walk(c, ty.from), walk(c, ty.to));
      case "all":
        return All(ty.name, walk(c + 1, ty.to), ty.kind);
      case "ttabs":
        return TTAbs(ty.name, walk(c + 1, ty.body), ty.kind);
      case "ttapp":
        return TTApp(walk(c, ty.left), walk(c, ty.right));
      case "ref":
        return ty;
    }
  };
  return walk(c, tyT);
}

export function typeSubst(tyS: Type, j: number, tyT: Type): Type {
  const walk = (c: number, t: Type): Type => {
    switch (t._) {
      case "arrow":
        return Arrow(walk(c, t.from), walk(c, t.to));
      case "var":
        return t.index == c ? typeShift(c, tyS) : Var(t.name, t.index);
      case "all":
        return All(t.name, walk(c + 1, t.to), t.kind);
      case "ttabs":
        return TTAbs(t.name, walk(c + 1, t.body), t.kind);
      case "ttapp":
        return TTApp(walk(c, t.left), walk(c, t.right));
      case "ref":
        return t;
    }
  };
  return walk(j, tyT);
}

// Perform the substitution of a type into a term, see E-TappTabs.
export function tytermSubst(tyS: Type, j: number, t: Term): Term {
  const walk = (c: number, t: Term): Term => {
    switch (t._) {
      case "var":
        return Var(t.name, t.index);
      case "lam":
        // We use c+1 in typeSubst so the type may reference this abstraction.
        return Abs(
          t.name,
          walk(c + 1, t.body),
          typeSubst(tyS, c + 1, t.bindType)
        );
      case "app":
        return App(walk(c, t.left), walk(c, t.right));
      case "tabs":
        return TAbs(t.name, walk(c + 1, t.body), t.kind);
      case "tapp":
        return TApp(walk(c, t.left), typeSubst(tyS, c, t.right));
      case "ann":
        throw "not implemented";
      case "ref":
        return Ref(t.name);
    }
  };
  return walk(j, t);
}

// Increment any Var nodes that refer to free variables in the given type.
export function typeShift(d: number, tyT: Type): Type {
  return typeShiftAbove(d, 0, tyT);
}

function tytermSubstTop(tyS: Type, t: Term): Term {
  return termShift(-1, tytermSubst(typeShift(1, tyS), 0, t));
}

export function typeSubstTop(tyS: Type, tyT: Type): Type {
  return typeShift(-1, typeSubst(typeShift(1, tyS), 0, tyT));
}

export function isValue(term: Term): boolean {
  return term._ == "lam" || term._ == "tabs";
}

// Evaluate this term by a single step. When applied to a term that is not yet a value, it yields
// the next step of evaluation for that term. When applied to a value an exception is thrown.
export function reduceOnce(defs: Def[], term: Term): Term {
  switch (term._) {
    case "app":
      if (term.left._ == "lam" && isValue(term.right)) {
        // E-AppAbs
        // (λx:T11.t12)v2 → [x/v2]t12
        let t12 = term.left.body;
        let v2 = term.right;
        return termSubstTop(v2, t12);
      } else if (isValue(term.left)) {
        // E-App2
        return App(term.left, reduceOnce(defs, term.right));
      } else {
        // E-App1
        return App(reduceOnce(defs, term.left), term.right);
      }
    case "tapp":
      if (term.left._ == "tabs") {
        // (ΛX.t12)(T2) → [X/T2]t12    E-TappTabs

        let t11 = term.left.body;
        let tyT2 = term.right;

        return tytermSubstTop(tyT2, t11);
      } else {
        //     t1 → t1'
        // ---------------- E-TApp
        // t1(T2) → t1'(T2)
        let t1 = term.left;
        let tyT2 = term.right;
        let t1p = reduceOnce(defs, t1);
        return TApp(t1p, tyT2);
      }
    case "tabs":
      throw "cannot reduce TAbs";
    case "lam":
      throw "cannot reduce Abs";
    case "var":
      throw "cannot reduce Var";
    case "ann": // ignored at runtime
      return reduceOnce(defs, term.term);
    case "ref":
      const match = defs.filter((d) => d.name == term.name);
      if (match.length == 0) {
        return term;
      }
      return match[0].term;
  }
}
