// check implements a typechecker for this language
import { Context, Term } from "./ast";

export const Check = (ctx: Context, term: Term) => {
  // TODO: Read all the top-level types and keep them in the context (gamma).
  // TODO: Check each top-level definition is well-typed w.r.t. the context.

  // TODO: Check if this name is already used (i.e. shadowing) and disallow.

  return false;
};
