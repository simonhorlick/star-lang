import {
  Ann,
  Star,
  Pi,
  Self,
  Context,
  Type,
  Term,
  App,
  Abs,
  Var,
  Def,
} from "./ast";
import { addTermToCtx, TypecheckError } from "./check";
import { indexToLineCol, printLine } from "./parser";
import { pretty } from "./pretty";

export const typecheckErrorDiagnostic = (src: string, err: TypecheckError) => {
  const startlc = indexToLineCol(src, err.start);
  const endlc = indexToLineCol(src, err.end);
  return (
    `typecheck error at line ${startlc.line} col ${startlc.col}: ${err.msg}\n` +
    `  ${printLine(src, startlc.line)}\n` +
    `  ${" ".repeat(startlc.col)}${"^".repeat(
      Math.max(0, endlc.col - startlc.col)
    )}`
  );
};

export const inspect = (tm: Term, ty: Type, defs: Def[]) => {
  const spans = new Map<
    { start: number; end: number },
    { term: Term; type: Type; ctx: Context }
  >();

  const traverse = (
    t: Term,
    ty: Type,
    start: number | undefined,
    end: number | undefined,
    ctx: Context,
    defs: Def[]
  ): Term => {
    if (t._ != "orig") {
      try {
        console.log(`traverse ${t._} (${pretty(t)}) has type ${pretty(ty)}`);
      } catch (e) {
        console.error(e);
      }
    }

    switch (t._) {
      case "ann":
        return Ann(
          traverse(t.term, t.typ, undefined, undefined, ctx, defs),
          traverse(t.typ, Star(), undefined, undefined, ctx, defs)
        );
      case "app":
        // for applications we add a span for the function indicating its
        // function type and a span for the argument so we can inspect the
        // argument type
        return App(
          traverse(t.left, ty, undefined, undefined, ctx, defs),
          traverse(t.right, ty, undefined, undefined, ctx, defs)
        );
      case "lam":
        // the type of a lambda abstraction is a pi type.
        const typ = ty as Pi;
        if (start != undefined && end != undefined) {
          spans.set(
            { start: start, end: end },
            { term: t, type: typ.from, ctx: ctx }
          );
        }
        return Abs(
          t.name,
          traverse(
            t.body,
            typ.to,
            undefined,
            undefined,
            addTermToCtx(ctx, t.name, typ.from),
            defs
          )
        );
      case "par":
        throw "unexpected par";
      case "pi":
        return Pi(
          t.name,
          traverse(t.from, ty, undefined, undefined, ctx, defs),
          traverse(
            t.to,
            ty,
            undefined,
            undefined,
            addTermToCtx(ctx, t.name, t.from),
            defs
          )
        );
      case "self":
        return Self(
          t.name,
          traverse(
            t.body,
            ty,
            undefined,
            undefined,
            addTermToCtx(ctx, t.name, Star()),
            defs
          )
        );
      case "case":
        throw "unexpected case";
      case "ref":
        const ref = defs.find((d) => d.name == t.name)!;
        // TODO: Add reference information.
        if (start != undefined && end != undefined) {
          spans.set(
            { start: start, end: end },
            { term: t, type: ref.typ, ctx: ctx }
          );
        }
        return t;
      case "star":
        return t;
      case "var":
        for (let i = 0; i < ctx.length; i++) {
          const binding = ctx[ctx.length - i - 1];
          if (binding.name == t.name) {
            if (start != undefined && end != undefined) {
              spans.set(
                { start: start, end: end },
                { term: t, type: binding.typ, ctx: ctx }
              );
            }
            return Var(binding.name, i);
          }
        }
        return t;
      case "orig":
        return traverse(t.child, ty, t.start, t.end, ctx, defs);
    }
  };

  traverse(tm, ty, undefined, undefined, [], defs);
  console.log("added spans");
  return spans;
};
