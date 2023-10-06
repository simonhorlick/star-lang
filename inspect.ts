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
import { File } from "./ast";
import { printDiagnostic, printMultilineDiagnostic } from "./inspect_test";

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
  f: (acc: A, curr: Term) => A,
  init: A,
  t: Term
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
        if (offset != undefined && offset >= t.start && offset < t.end) {
          return traverse(t.child, ty, t.start, t.end, ctx, defs);
        } else {
          return t;
        }
      case "rel":
        return traverse(t.term, ty, undefined, undefined, ctx, defs);
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

export type HoverInfo = {
  msg: string;
};

export type CompletionInfo = {
  label: string;
  kind: number;
  sortText: string;
};

export type Range = { start: number; end: number };

export const hover = (
  src: string,
  f: File,
  defs: Map<string, Def>
): Map<Range, HoverInfo> => {
  let hoverInfo = new Map<Range, HoverInfo>();

  for (const node of f.content) {
    if (node._ == "def") {
      const def = node;
      const spans = inspect(def, defs);
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
        // const msg = `${k.start}-${k.end} is a ${v.term._} with type ${pretty(
        //   v.type
        // )}; ctx at this location is ${printCtx(v.ctx)}`;
        // console.debug(
        //   printDiagnostic(src, TypecheckError(msg, k.start, k.end))
        // );
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

        // const msg = `${k.start}-${k.end} is a ${v.term._}`;
        // console.debug(
        //   printDiagnostic(src, TypecheckError(msg, k.start, k.end))
        // );
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
  const hoverInfo = hover(src, f, defs);

  const overlappingSpans = [...hoverInfo].filter(
    ([k, v]) => k.start <= offset && k.end > offset
  );

  // find the shortest node that overlaps this offset
  overlappingSpans.sort(([a], [b]) => a.end - a.start - (b.end - b.start));

  console.log(`the following nodes overlap ${offset}:`);
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
  let completionInfo = new Map<Range, CompletionInfo>();

  for (const node of f.content) {
    if (node._ == "def") {
      const def = node;
      console.log(`inspecting ${def.name}`);

      const spans = inspect(def, defs, offset);

      // type Ctx = {
      //   start: number;
      //   end: number;
      //   spans: Map<Range, CompletionInfo>;
      // };

      // FIXME: This is wrong, we don't want to fold the whole tree - we want
      // to quickly find out what's at a certain offset, by trimming subtrees
      // as we traverse. How do we find out what's in the context at that
      // offset?

      // const spans = foldTree<Ctx>(
      //   (acc, curr) => {
      //     // if (acc.start != 0 && acc.end != 0) {
      //     console.log(
      //       printDiagnostic(
      //         src,
      //         TypecheckError(
      //           `${acc.start}-${acc.end}: ${curr._}: ${pretty(curr)}`,
      //           acc.start,
      //           acc.end
      //         )
      //       )
      //     );
      //     // }

      //     if (curr._ == "orig") {
      //       return { spans: acc.spans, start: curr.start, end: curr.end };
      //     } else if (curr._ == "lam") {
      //       let copy = new Map(acc.spans);
      //       if (acc.start != 0 && acc.end != 0) {
      //         copy.set(
      //           { start: acc.start, end: acc.end },
      //           {
      //             label: `${identifier(curr.name)}`,
      //             kind: 1,
      //             sortText: "0",
      //           }
      //         );
      //       }
      //       return { spans: copy, start: 0, end: 0 };
      //     } else {
      //       // console.log(`${acc.start}-${acc.end}: ${curr._}: ${pretty(curr)}`);
      //       return { spans: acc.spans, start: 0, end: 0 };
      //     }
      //   },
      //   { start: 0, end: 0, spans: new Map<Range, CompletionInfo>() },
      //   def.term
      // );

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

        completionInfo.set(k, {
          label: `${pretty(v.term)}`,
          kind: 1,
          sortText: "0",
        });
      }
    }
  }

  const overlappingSpans = [...completionInfo].filter(
    ([k, v]) => k.start <= offset && k.end > offset
  );

  console.log(`the following nodes overlap ${offset}:`);
  for (const span of overlappingSpans) {
    console.log(`  span(${span[0].start}-${span[0].end}): ${span[1].label}`);
  }

  let completionList: CompletionInfo[] = [];

  for (const span of overlappingSpans) {
    completionList.push(span[1]);
  }

  return completionList;
};
