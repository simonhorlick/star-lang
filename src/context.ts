import { Star, Term, Type, identifier2str } from "./ast";
import { printCtx } from "./pretty";
import { shift } from "./substitution";

export type VariableBinding = { type: "bind"; name: string; typ: Type };

export type Binding = VariableBinding;

export type Context = Binding[];

export const ctxContains = (name: string, ctx: Context) =>
  ctx.find((b) => b.name == name) != undefined;

export const addTermToCtx = (
  ctx: Context,
  name: string,
  type: Type
): Context => {
  // if (name != "" && name != "P" && ctxContains(name, ctx)) {
  //   console.log(
  //     `warning: variable ${name} shadows existing variable; context is ${printCtx(
  //       ctx
  //     )}`
  //   );
  // }
  dbgCheckIndices(ctx, 0, type);
  return [...ctx, { type: "bind", name: name, typ: type }];
};

export const dbgCheckIndices = (ctx: Context, depth: number, t: Term): Term => {
  // check the names of Var terms match what's in the context.
  switch (t._) {
    case "var":
      if (t.index >= ctx.length) {
        throw `variable ${t.name} not found in context`;
      }
      let x = ctx[ctx.length - t.index - 1];
      // For debugging - this can only happen if the wrong index is used in a
      // hand-crafted expression.
      if (t.name && x.name && x.name != t.name) {
        throw `name mismatch: looking up ${t.index} got ${x.name}; expected ${
          t.name
        }. ctx is ${printCtx(ctx, true)}`;
      }
      return t;
    case "lam":
      dbgCheckIndices(
        addTermToCtx(ctx, identifier2str(t.name), Star()),
        depth + 1,
        t.body
      );
      return t;
    case "self":
      dbgCheckIndices(addTermToCtx(ctx, t.name, Star()), depth + 1, t.body);
      return t;
    case "app":
      dbgCheckIndices(ctx, depth, t.func);
      dbgCheckIndices(ctx, depth, t.arg);
      return t;
    case "ann":
      dbgCheckIndices(ctx, depth, t.term);
      dbgCheckIndices(ctx, depth, t.typ);
      return t;
    case "pi":
      dbgCheckIndices(ctx, depth, t.from);
      dbgCheckIndices(addTermToCtx(ctx, t.name, Star()), depth + 1, t.body);
      return t;
    case "star":
    case "ref":
    case "id":
    case "key":
    case "par":
    case "hole":
    case "int":
    case "str":
    case "err":
      return t;
    case "case":
      // FIXME: Improve the types here.
      throw "dbgCheckIndices: unexpected case";
    case "let":
      throw "dbgCheckIndices: unexpected let";
    case "rel":
      throw "dbgCheckIndices: unexpected rel";
    case "if":
      throw "dbgCheckIndices: unexpected if";
    case "orig":
    case "syn":
      dbgCheckIndices(ctx, depth, t.child);
      return t;
  }
};

export const lookupType = (
  ctx: Context,
  index: number,
  name: string | undefined = undefined
): Type => {
  if (index >= ctx.length) {
    throw `variable ${name} not found in context`;
  }
  let x = ctx[ctx.length - index - 1];
  // For debugging - this can only happen if the wrong index is used in a
  // hand-crafted expression.
  if (name && x.name != name) {
    throw `name mismatch: looking up ${name}@${index}; got ${
      x.name
    }@${index}. ctx is ${printCtx(ctx)}`;
  }
  // Shift the indices referenced in this type to take into account the actual
  // context length. When this type was added to the context all variables are
  // offset from 0, but when looking up the entry in position i, the absolute
  // offsets of all variables in this entry are offset by i.
  // For example, if the context is [(A *), (a A@0)] then the returned type
  // for a@0 is A@1, not A@0.
  return shift(index + 1, 0, x.typ);
};
