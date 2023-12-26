import {
  Ann,
  Star,
  Pi,
  Self,
  Context,
  Type,
  Term,
  App,
  Var,
  Def,
  ASTNode,
  AbsI,
  Origin,
  Identifier,
  Hole,
  identifier2str,
  File,
} from "../ast";
import { addTermToCtx, TypecheckError } from "../check";
import { whnf } from "../equal";
import { indexToLineCol, printLine } from "../parser";
import { pretty, printCtx } from "../pretty";

export const printMultilineDiagnostic = (
  src: string,
  err: TypecheckError
): string => {
  const lc = indexToLineCol(src, err.start);
  const ec = indexToLineCol(src, err.end);

  let msg = `at line ${lc.line} col ${lc.col}: ${err.msg}\n`;
  for (let i = lc.line; i <= ec.line; i++) {
    const line = printLine(src, i);
    msg += `${line}\n`;
    if (i == lc.line) {
      msg += `${" ".repeat(lc.col)}^`;
      if (ec.line > lc.line) {
        msg += `${"-".repeat(Math.max(0, line.length - lc.col - 1))}\n`;
      } else {
        msg += `${"-".repeat(Math.max(0, ec.col - lc.col - 1))}\n`;
      }
    } else if (i == ec.line) {
      msg += `${"-".repeat(ec.col)}^\n`;
    } else {
      msg += `${"-".repeat(line.length)}\n`;
    }
  }

  return msg;
};

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

// pre-order traversal of the term tree - visit the node itself, followed by
// any child nodes.
export const foldTree = <A>(
  f: (acc: A, curr: Term) => A, // returns the new accumulator
  init: A, // initial value of the accumulator
  t: Term // the starting term
): A => {
  const x = f(init, t);
  switch (t._) {
    case "app": {
      const left = foldTree(f, x, t.left);
      const rght = foldTree(f, left, t.right);
      return rght;
    }
    case "lam": {
      const curr = foldTree(f, x, t.name);
      const body = foldTree(f, curr, t.body);
      return body;
    }
    case "ann": {
      const tm = foldTree(f, x, t.term);
      const typ = foldTree(f, tm, t.typ);
      return typ;
    }
    case "case": {
      const name = foldTree(f, x, t.name);
      let prev = name;
      for (const b of t.branches) {
        const ctr = foldTree(f, prev, b.constructor);
        prev = foldTree(f, ctr, b.term);
      }
      return prev;
    }
    case "if": {
      const cond = foldTree(f, x, t.condition);
      const fls = foldTree(f, cond, t.falseBranch);
      const tru = foldTree(f, fls, t.trueBranch);
      return tru;
    }
    case "let": {
      const name = foldTree(f, x, t.name);
      const expr = foldTree(f, name, t.expr);
      const body = foldTree(f, expr, t.body);
      return body;
    }
    case "orig": {
      return foldTree(f, x, t.child);
    }
    case "pi": {
      const frm = foldTree(f, x, t.from);
      const to = foldTree(f, frm, t.to);
      return to;
    }
    case "rel": {
      return foldTree(f, x, t.term);
    }
    case "self": {
      return foldTree(f, x, t.body);
    }
    case "id":
    case "int":
    case "par":
    case "hole":
    case "err":
    case "star":
    case "ref":
    case "str":
    case "var": {
      return x;
    }
  }
};

export type TermAndCtx = {
  term: Term;
  start?: number;
  end?: number;
};

// pre-order traversal of the term tree - visit the node itself, followed by
// any child nodes.
export const foldTreeCtx = <A>(
  f: (acc: A, curr: TermAndCtx) => A, // returns the new accumulator
  init: A, // initial value of the accumulator
  initVal: Term // the starting term
): A => {
  const doFold = (
    init: A, // initial value of the accumulator
    ctx: TermAndCtx // the starting term
  ): A => {
    const x = f(init, ctx);
    const t = ctx.term;
    switch (t._) {
      case "app": {
        const left = doFold(x, {
          term: t.left,
          start: ctx.start,
          end: ctx.end,
        });
        const rght = doFold(left, {
          term: t.right,
          start: ctx.start,
          end: ctx.end,
        });
        return rght;
      }
      case "lam": {
        const curr = doFold(x, {
          term: t.name,
          start: ctx.start,
          end: ctx.end,
        });
        const body = doFold(curr, {
          term: t.body,
          start: ctx.start,
          end: ctx.end,
        });
        return body;
      }
      case "ann": {
        const tm = doFold(x, {
          term: t.term,
          start: ctx.start,
          end: ctx.end,
        });
        const typ = doFold(tm, {
          term: t.typ,
          start: ctx.start,
          end: ctx.end,
        });
        return typ;
      }
      case "case": {
        const name = doFold(x, {
          term: t.name,
          start: ctx.start,
          end: ctx.end,
        });
        let prev = name;
        for (const b of t.branches) {
          const ctr = doFold(prev, {
            term: b.constructor,
            start: ctx.start,
            end: ctx.end,
          });
          prev = doFold(ctr, {
            term: b.term,
            start: ctx.start,
            end: ctx.end,
          });
        }
        return prev;
      }
      case "if": {
        const cond = doFold(x, {
          term: t.condition,
          start: ctx.start,
          end: ctx.end,
        });
        const fls = doFold(cond, {
          term: t.falseBranch,
          start: ctx.start,
          end: ctx.end,
        });
        const tru = doFold(fls, {
          term: t.trueBranch,
          start: ctx.start,
          end: ctx.end,
        });
        return tru;
      }
      case "let": {
        const name = doFold(x, {
          term: t.name,
          start: ctx.start,
          end: ctx.end,
        });
        const expr = doFold(name, {
          term: t.expr,
          start: ctx.start,
          end: ctx.end,
        });
        const body = doFold(expr, {
          term: t.body,
          start: ctx.start,
          end: ctx.end,
        });
        return body;
      }
      case "orig": {
        return doFold(x, { term: t.child, start: t.start, end: t.end });
      }
      case "pi": {
        const frm = doFold(x, {
          term: t.from,
          start: ctx.start,
          end: ctx.end,
        });
        const to = doFold(frm, {
          term: t.to,
          start: ctx.start,
          end: ctx.end,
        });
        return to;
      }
      case "rel": {
        return doFold(x, { term: t.term, start: ctx.start, end: ctx.end });
      }
      case "self": {
        return doFold(x, { term: t.body, start: ctx.start, end: ctx.end });
      }
      case "id":
      case "int":
      case "par":
      case "hole":
      case "err":
      case "star":
      case "ref":
      case "str":
      case "var": {
        return x;
      }
    }
  };
  return doFold(init, { term: initVal, start: undefined, end: undefined });
};

export const inspect = (
  def: Def,
  defs: Map<string, Def>,
  offset: number | undefined = undefined
) => {
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
      case "ann": {
        return Ann(
          traverse(t.term, t.typ, undefined, undefined, ctx, defs),
          traverse(t.typ, undefined, undefined, undefined, ctx, defs)
        );
      }
      case "app": {
        // for applications we add a span for the function indicating its
        // function type and a span for the argument so we can inspect the
        // argument type
        return App(
          traverse(t.left, undefined, undefined, undefined, ctx, defs),
          traverse(t.right, undefined, undefined, undefined, ctx, defs)
        );
      }
      case "lam": {
        // the type of a lambda abstraction is a pi type.
        if (ty == undefined) {
          // this can happen if a lambda is part of a type in an annotation.
          // throw "inspect: type not present";
          return t;
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
            addTermToCtx(ctx, identifier2str(t.name), typ.from),
            defs
          )
        );
      }
      case "par": {
        throw "inspect: unexpected par";
      }
      case "let": {
        throw "inspect: unexpected let";
      }
      case "pi": {
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
      }
      case "self": {
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
      }
      case "case": {
        throw "inspect: unexpected case";
      }
      case "if": {
        throw "inspect: unexpected if";
      }
      case "ref": {
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
            { term: t, type: ref.term.typ, ctx: ctx }
          );
        }
        return t;
      }
      case "star": {
        return t;
      }
      case "id": {
        if (start != undefined && end != undefined && ty != undefined) {
          spans.set(
            { start: start, end: end },
            { term: t, type: ty, ctx: ctx }
          );
        }
        return t;
      }
      case "var": {
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
      }
      case "orig": {
        // If an offset is specified, only traverse into nodes that overlap
        // that offset.
        if (offset != undefined && offset >= t.start && offset < t.end) {
          return traverse(t.child, ty, t.start, t.end, ctx, defs);
        } else if (offset == undefined) {
          return traverse(t.child, ty, t.start, t.end, ctx, defs);
        } else {
          return t;
        }
      }
      case "rel": {
        return traverse(t.term, ty, undefined, undefined, ctx, defs);
      }
      case "hole": {
        return t;
      }
      case "int": {
        return t;
      }
      case "str": {
        return t;
      }
      case "err": {
        if (start != undefined && end != undefined) {
          spans.set(
            { start: start, end: end },
            { term: t, type: ty == undefined ? Hole(0) : ty, ctx: ctx }
          );
        }
        return t;
      }
    }
  };

  traverse(def.term, undefined, undefined, undefined, [], defs);
  return spans;
};

export type HoverInfo = {
  msg: string;
};

export type CompletionInfo = {
  label: string;
  kind: number;
  sortText: string;
};

export type Range = { start: number; end: number };

export const printDiagnostic = (src: string, err: TypecheckError) => {
  const lc = indexToLineCol(src, err.start);
  const ec = indexToLineCol(src, err.end);
  const line = printLine(src, lc.line);
  return (
    `at line ${lc.line} col ${lc.col}: ${err.msg}\n` +
    `  ${line}\n` +
    `  ${" ".repeat(lc.col)}^`
  );
};

export const hover = (
  src: string,
  f: File,
  defs: Map<string, Def>,
  offset: number | undefined
): Map<Range, HoverInfo> => {
  let hoverInfo = new Map<Range, HoverInfo>();

  for (const node of f.content) {
    if (node._ == "def") {
      const def = node;
      const spans = inspect(def, defs, offset);
      for (const [k, v] of spans) {
        switch (v.term._) {
          case "lam":
            break;
          default:
            hoverInfo.set(
              { start: k.start, end: k.end },
              { msg: `${v.term._}(${pretty(v.type)})` }
            );
        }
        const msg = `${k.start}-${k.end} is a ${v.term._} with type ${pretty(
          v.type
        )}; ctx at this location is ${printCtx(v.ctx)}`;
        console.debug(
          printDiagnostic(src, TypecheckError(msg, k.start, k.end))
        );
        // console.log(
        //   `[{ start: ${k.start}, end: ${k.end} }, { msg: "${`${
        //     v.term._
        //   }(${pretty(v.type)})`}" }],`
        // );
      }
    } else {
      const spans = inspectASTNodes(node);
      for (const [k, v] of spans) {
        hoverInfo.set({ start: k.start, end: k.end }, { msg: "" });

        const msg = `${k.start}-${k.end} is a ${v.term._}`;
        console.debug(
          printDiagnostic(src, TypecheckError(msg, k.start, k.end))
        );
      }
    }
  }

  return hoverInfo;
};

export const hoverMessage = (
  src: string,
  f: File,
  defs: Map<string, Def>,
  offset: number
): { range: { start: number; end: number }; msg: string } | null => {
  const hoverInfo = hover(src, f, defs, offset);

  // const overlappingSpans = [...hoverInfo].filter(
  //   ([k, v]) => k.start <= offset && k.end > offset
  // );
  const overlappingSpans = [...hoverInfo];

  // find the shortest node that overlaps this offset
  overlappingSpans.sort(([a], [b]) => a.end - a.start - (b.end - b.start));

  // console.log(`the following nodes overlap ${offset}:`);
  for (const span of overlappingSpans) {
    console.log(`  span(${span[0].start}-${span[0].end}): ${span[1].msg}`);
  }

  if (overlappingSpans.length == 0) {
    return null;
  }

  return { range: overlappingSpans[0][0], msg: overlappingSpans[0][1].msg };
};

export const complete = (
  src: string,
  f: File,
  defs: Map<string, Def>,
  offset: number
): CompletionInfo[] => {
  let completionList: CompletionInfo[] = [];

  for (const node of f.content) {
    if (node._ == "def") {
      const def = node;

      // const spans = inspect(def, defs, offset);
      const spans = inspect(def, defs);

      for (const [k, v] of spans) {
        console.log(
          printMultilineDiagnostic(
            src,
            TypecheckError(
              `${v.term._}: ${printCtx(v.ctx)} ${pretty(v.term)}`,
              k.start,
              k.end
            )
          )
        );

        if (!(k.start <= offset && k.end > offset)) {
          continue;
        }

        for (const binding of v.ctx) {
          completionList.push({
            label: binding.name,
            kind: 1,
            sortText: "0",
          });
        }
      }
    }
  }

  return completionList;
};
