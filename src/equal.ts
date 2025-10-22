import { Def2 } from "./ast";
import { TypecheckError } from "./typecheck";
import { Context } from "./context";
import { substTop } from "./substitution";
import { printCtx } from "./pretty";
import { CTerm } from "./sugar";
import { identifier2str } from "./pratt";

// Reduce this term to weak head normal form.
export const reduce = (
  unfold: boolean,
  ctx: Context,
  defs: Map<string, Def2>,
  t: CTerm
): CTerm => {
  switch (t._) {
    case "ref": {
      if (!unfold) {
        return t;
      }
      const match = defs.get(t.name);
      if (match == undefined) {
        throw TypecheckError(
          `reference not found: ${t.name}; ctx is ${printCtx(ctx)}`,
          0,
          0
        );
      }
      return reduce(false, ctx, defs, match.term);
    }
    case "app": {
      let func = reduce(unfold, ctx, defs, t.func);
      if (func._ == "lam") {
        return reduce(
          unfold,
          ctx,
          defs,
          substTop(t.arg, func.body, identifier2str(func.name))
        );
      }
      return t;
    }
    case "ann": {
      return reduce(unfold, ctx, defs, t.term);
    }
    case "orig": {
      // remove origins
      return reduce(unfold, ctx, defs, t.child);
    }
    case "syn": {
      // remove syntax nodes
      return reduce(unfold, ctx, defs, t.child);
    }
    case "let": {
      throw "TODO - reduce let";
    }
    case "label": {
      // remove labels
      return reduce(unfold, ctx, defs, t.child);
    }
    default: {
      return t;
    }
  }
};
