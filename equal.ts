import { App, Context, Def, Self, Term, identifier2str } from "./ast";
import { TypecheckError, substTop } from "./check";

// Compute the weak head normal form for a term.
export const whnf = (
  unfold: boolean,
  ctx: Context,
  defs: Map<string, Def>,
  t: Term
): Term => {
  switch (t._) {
    case "ref":
      if (!unfold) return t;
      const match = defs.get(t.name);
      if (match == undefined) {
        throw TypecheckError(`whnf: reference not found: ${t.name}`, 0, 0);
      }
      return whnf(false, ctx, defs, match.term);
    case "app": {
      let nf = whnf(unfold, ctx, defs, t.left);
      if (nf._ == "lam") {
        return whnf(
          unfold,
          ctx,
          defs,
          substTop(t.right, nf.body, identifier2str(nf.name))
        );
      }
      return App(nf, t.right);
    }
    case "ann":
      return whnf(unfold, ctx, defs, t.term);
    case "par":
      throw "whnf: unexpected Par";
    case "rel":
      throw "whnf: unexpected Rel";
    case "self":
      return Self(t.name, whnf(unfold, ctx, defs, t.body));
    case "var":
      //throw "this looks wrong";
      //return lookupType(ctx, t.index, t.name);
      return t;
    case "lam":
    case "pi":
    case "star":
    case "id":
    case "hole":
    case "int":
    case "str":
    case "let":
      return t;
    case "case":
      return t;
    //throw "whnf: unexpected case";
    case "if":
      return t;
    case "orig": // remove origins
      return whnf(unfold, ctx, defs, t.child);
    case "err":
      // return successfully
      return t;
    // throw "whnf: unexpected parse error";
  }
};
