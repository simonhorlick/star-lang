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
  ADT,
  ASTNode,
  AbsI,
  Origin,
  Identifier,
  Let,
} from "./ast";
import {
  addTermToCtx,
  identifier,
  infer,
  logFull,
  serialise,
  shift,
  strip,
  TypecheckError,
} from "./check";
import { whnf } from "./equal";
import { indexToLineCol, printLine } from "./parser";
import { pretty, printCtx } from "./pretty";

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

export const inspectASTNodes = (n: ASTNode) => {
  const spans = new Map<
    { start: number; end: number },
    { term: ASTNode; type: Type | undefined; ctx: Context }
  >();

  const f = (n: ASTNode, start: number, end: number): void => {
    switch (n._) {
      case "adt":
        return;
      case "com":
        spans.set(
          { start: start, end: end },
          { term: n, type: undefined, ctx: [] }
        );
        return;
      case "def":
        return;
      case "pkg":
        spans.set(
          { start: start, end: end },
          { term: n, type: undefined, ctx: [] }
        );
        return;
      case "nl":
      case "sp":
        return;
      case "orig2":
        return f(n.child, n.start, n.end);
    }
  };
  f(n, 0, 0);
  return spans;
};

export const inspect = (def: Def, defs: Map<string, Def>) => {
  const spans = new Map<
    { start: number; end: number },
    { term: Term; type: Type; ctx: Context }
  >();

  const traverse = (
    t: Term,
    ty: Type | undefined,
    start: number | undefined,
    end: number | undefined,
    ctx: Context,
    defs: Map<string, Def>
  ): Term => {
    // if (t._ != "orig") {
    //   try {
    //     console.log(
    //       `traverse ${t._} (${pretty(t)}) has type ${
    //         ty ? pretty(ty) : "none"
    //       }; ctx=${printCtx(ctx)}`
    //     );
    //     console.log(serialise(strip(t)));
    //   } catch (e) {
    //     console.error(e);
    //   }
    // }

    switch (t._) {
      case "ann":
        return traverse(t.term, t.typ, undefined, undefined, ctx, defs);
      case "app":
        // for applications we add a span for the function indicating its
        // function type and a span for the argument so we can inspect the
        // argument type
        return App(
          traverse(t.left, undefined, undefined, undefined, ctx, defs),
          traverse(t.right, undefined, undefined, undefined, ctx, defs)
        );
      case "lam":
        // the type of a lambda abstraction is a pi type.
        if (ty == undefined) {
          throw "inspect: type not present";
        }
        const typ = whnf(true, [], defs, ty, t);
        if (typ._ == "typecheckerror") {
          return t;
        }
        if (typ._ != "pi") {
          throw "inspect: expected pi";
        }
        if (start != undefined && end != undefined) {
          spans.set(
            { start: start, end: end },
            { term: t, type: typ, ctx: ctx }
          );
        }
        return AbsI(
          traverse(t.name, typ.from, undefined, undefined, ctx, defs) as
            | Origin
            | Identifier,
          traverse(
            t.body,
            typ.to,
            undefined,
            undefined,
            addTermToCtx(ctx, identifier(t.name), typ.from),
            defs
          )
        );
      case "par":
        throw "inspect: unexpected par";
      case "let":
        throw "inspect: unexpected let";
      case "pi":
        return Pi(
          t.name,
          traverse(t.from, undefined, undefined, undefined, ctx, defs),
          traverse(
            t.to,
            undefined,
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
            undefined,
            undefined,
            undefined,
            addTermToCtx(ctx, t.name, Star()),
            defs
          )
        );
      case "case":
        throw "inspect: unexpected case";
      case "if":
        throw "inspect: unexpected if";
      case "ref":
        // TODO: For defs like true, the type is the expanded version. We
        // usually want a pi type so we can find the types of the arguments,
        // however it doesn't make sense to say true has a pi type when it's
        // obviously a Bool.
        // The fix is to keep it as a ref - we can always follow refs here in
        // inspect to get the pi type.
        const ref = defs.get(t.name)!;
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
      case "id":
        if (start != undefined && end != undefined && ty != undefined) {
          spans.set(
            { start: start, end: end },
            { term: t, type: ty, ctx: ctx }
          );
        }
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
      case "hole":
        return t;
      case "int":
        return t;
      case "str":
        return t;
      case "err":
        return t;
    }
  };

  traverse(def.term, def.typ, undefined, undefined, [], defs);
  traverse(def.typ, undefined, undefined, undefined, [], defs);
  return spans;
};
