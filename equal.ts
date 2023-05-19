import { App, Context, Def, Normal, Self, Term } from "./ast";
import { TypecheckError, identifier, lookupType, substTop } from "./check";

// Compute the weak head normal form for a term.
export const whnf = (
  unfold: boolean,
  ctx: Context,
  defs: Map<string, Def>,
  t: Term,
  selfTerm: Term | undefined
): Normal | TypecheckError => {
  switch (t._) {
    case "ref":
      if (!unfold) return t;
      const match = defs.get(t.name);
      if (match == undefined) {
        return TypecheckError(`whnf: reference not found: ${t.name}`, 0, 0);
      }
      return whnf(false, ctx, defs, match.term, selfTerm);
    case "app": {
      let nf = whnf(unfold, ctx, defs, t.left, selfTerm);
      if (nf._ == "typecheckerror") {
        return nf;
      }
      if (nf._ == "lam") {
        return whnf(
          unfold,
          ctx,
          defs,
          substTop(t.right, nf.body, identifier(nf.name)),
          selfTerm
        );
      }
      return App(nf, t.right);
    }
    case "ann":
      return whnf(unfold, ctx, defs, t.term, selfTerm);
    case "par":
      throw "whnf: unexpected Par";
    case "self":
      // eliminate self
      if (selfTerm == undefined) {
        // This can happen if we're checking a type definition, i.e. Nat:*.
        const nf = whnf(unfold, ctx, defs, t.body, selfTerm);
        if (nf._ == "typecheckerror") {
          return nf;
        }
        return Self(t.name, nf);
      }
      return whnf(
        unfold,
        ctx,
        defs,
        substTop(selfTerm, t.body, t.name),
        selfTerm
      );
    case "var":
      return lookupType(ctx, t.index, t.name);
    case "lam":
    case "pi":
    case "star":
    case "id":
    case "hole":
      return t;
    case "case":
      return t;
    //throw "whnf: unexpected case";
    case "if":
      return t;
    case "orig": // remove origins
      return whnf(unfold, ctx, defs, t.child, selfTerm);
  }
};

export const equate = (t1: Term, t2: Term): boolean => {
  return false;
};

// equate t1 t2 = do
//     nf1 <- reduce t1  -- full reduction, not just weak head reduction
//     nf2 <- reduce t2
//     Unbound.aeq nf1 nf2
