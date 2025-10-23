import { TypecheckError, equate } from "./typecheck";
import { reduce } from "./equal";
import { indexToLineCol, printLine } from "./parser";
import { pretty, printCtx } from "./pretty";
import { Context, addTermToCtx } from "./context";
import { substTop } from "./substitution";
import { BuildResult } from "./build";
import { ASTNode, Def2 } from "./ast";
import {
  AbsI,
  Ann,
  App,
  Case,
  CTerm,
  Identifier,
  Let,
  Origin,
  Pi,
  Ref,
  Self,
  Star,
  Var,
} from "./sugar";
import { identifier2str } from "./pratt";

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

export const errorDiagnostic = (
  src: string,
  err: TypecheckError,
  category: string,
  uri: string | undefined
) => {
  const startlc = indexToLineCol(src, err.start);
  const endlc = indexToLineCol(src, err.end);

  const loc = uri ? uri : `<file>`;

  return (
    `${loc}:${startlc.line + 1}:${startlc.col + 1} ${category} error: ${
      err.msg
    }\n` +
    `  ${printLine(src, startlc.line)}\n` +
    `  ${" ".repeat(startlc.col)}${"^".repeat(
      Math.max(0, endlc.col - startlc.col)
    )}`
  );
};

export const typecheckErrorDiagnostic = (src: string, err: TypecheckError) =>
  errorDiagnostic(src, err, "typecheck", undefined);

export const parseErrorDiagnostic = (
  src: string,
  err: TypecheckError,
  uri: string
) => errorDiagnostic(src, err, "parse", uri);

export const inspectASTNodes = (n: ASTNode) => {
  const spans = new Map<
    { start: number; end: number },
    { term: ASTNode; type: CTerm | undefined; ctx: Context }
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

export type TermAndCtx = {
  term: CTerm;
  start?: number;
  end?: number;
};

// pre-order traversal of the term tree - visit the node itself, followed by
// any child nodes.
export const foldTreeCtx = <A>(
  f: (acc: A, curr: TermAndCtx) => A, // returns the new accumulator
  init: A, // initial value of the accumulator
  initVal: CTerm // the starting term
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
          term: t.func,
          start: ctx.start,
          end: ctx.end,
        });
        const rght = doFold(left, {
          term: t.arg,
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
          term: t.type,
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
      case "syn": {
        const syn = doFold(x, {
          term: t.syntax,
          start: ctx.start,
          end: ctx.end,
        });
        const child = doFold(syn, {
          term: t.child,
          start: ctx.start,
          end: ctx.end,
        });
        return child;
      }
      case "pi": {
        const frm = doFold(x, {
          term: t.from,
          start: ctx.start,
          end: ctx.end,
        });
        const to = doFold(frm, {
          term: t.body,
          start: ctx.start,
          end: ctx.end,
        });
        return to;
      }
      case "label": {
        return doFold(x, { term: t.child, start: ctx.start, end: ctx.end });
      }
      case "self": {
        return doFold(x, { term: t.body, start: ctx.start, end: ctx.end });
      }
      case "id":
      case "key":
      case "int":
      case "hole":
      case "err":
      case "star":
      case "ref":
      case "str":
      case "var":
        return x;

        throw new Error(`unimplemented`);
    }
  };
  return doFold(init, { term: initVal, start: undefined, end: undefined });
};

export type Span = {
  start: number;
  end: number;
  term: CTerm;
  type?: CTerm;
  ctx: Context;
};

export const inspect = (
  def: Def2,
  defs: Map<string, Def2>,
  offset: number | undefined = undefined
) => {
  const spans: Span[] = [];

  const traverse = (
    t: CTerm,
    ty: CTerm | undefined,
    start: number | undefined,
    end: number | undefined,
    ctx: Context,
    defs: Map<string, Def2>
  ): CTerm => {
    switch (t._) {
      case "ann": {
        return Ann(
          // Pass the origins through the annotation. This is useful for
          // annotations generated by the typechecker.
          traverse(t.term, t.type, start, end, ctx, defs),
          traverse(t.type, undefined, undefined, undefined, ctx, defs)
        );
      }
      case "app": {
        // for applications we add a span for the function indicating its
        // function type and a span for the argument so we can inspect the
        // argument type
        return App(
          traverse(t.func, undefined, undefined, undefined, ctx, defs),
          traverse(t.arg, undefined, undefined, undefined, ctx, defs)
        );
      }
      case "lam": {
        // the type of a lambda abstraction is a pi type.
        if (ty == undefined) {
          // this can happen if a lambda is part of a type in an annotation.
          // throw "inspect: type not present";
          return t;
        }
        let typ = reduce(true, [], defs, ty);

        // If an expression has a self-type then the term we're checking must be
        // substituted into the type before we can continue.
        typ = typ._ == "self" ? substTop(t, typ.body, typ.name) : typ;

        if (typ._ != "pi") {
          throw "inspect: expected pi";
        }
        if (start != undefined && end != undefined) {
          spans.push({ start: start, end: end, term: t, type: typ, ctx: ctx });
        }
        return AbsI(
          traverse(t.name, typ.from, undefined, undefined, ctx, defs) as
            | Origin
            | Identifier,
          traverse(
            t.body,
            typ.body,
            undefined,
            undefined,
            addTermToCtx(ctx, identifier2str(t.name), typ.from),
            defs
          )
        );
      }
      // case "par": {
      //   throw "inspect: unexpected par";
      // }
      case "let": {
        // FIXME: Need to add the type of the expression as an annotation so we can use it here.
        return Let(
          traverse(t.name, undefined, undefined, undefined, ctx, defs) as
            | Origin
            | Identifier,
          traverse(t.expr, undefined, undefined, undefined, ctx, defs),
          traverse(
            t.body,
            undefined,
            undefined,
            undefined,
            addTermToCtx(ctx, identifier2str(t.name), Ref("TODO")),
            defs
          )
        );
      }
      case "pi": {
        return Pi(
          t.name,
          traverse(t.from, undefined, undefined, undefined, ctx, defs),
          traverse(
            t.body,
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
        return Case(
          traverse(t.name, undefined, undefined, undefined, ctx, defs),
          t.branches.map((b) => {
            traverse(b.constructor, undefined, undefined, undefined, ctx, defs);
            // FIXME: This won't include the desugared parameters for each branch
            traverse(b.term, undefined, undefined, undefined, ctx, defs);
            return b;
          })
        );
      }
      // case "if": {
      //   throw "inspect: unexpected if";
      // }
      case "ref": {
        // TODO: For defs like true, the type is the expanded version. We
        // usually want a pi type so we can find the types of the arguments,
        // however it doesn't make sense to say true has a pi type when it's
        // obviously a Bool.
        // The fix is to keep it as a ref - we can always follow refs here in
        // inspect to get the pi type.
        const ref = defs.get(t.name);
        if (start != undefined && end != undefined) {
          if (ref) {
            spans.push({
              start: start,
              end: end,
              term: t,
              type: ref.term.type,
              ctx: ctx,
            });
          } else if (start != undefined && end != undefined) {
            // Undefined reference - use the expected type if available.
            spans.push({
              start: start,
              end: end,
              term: t,
              type: ty,
              ctx: ctx,
            });
          }
        }
        return t;
      }
      case "star": {
        return t;
      }
      case "id": {
        if (start != undefined && end != undefined && ty != undefined) {
          spans.push({ start: start, end: end, term: t, type: ty, ctx: ctx });
        }
        return t;
      }
      case "key": {
        if (start != undefined && end != undefined && ty != undefined) {
          spans.push({ start: start, end: end, term: t, type: ty, ctx: ctx });
        }
        return t;
      }
      case "var": {
        for (let i = 0; i < ctx.length; i++) {
          const binding = ctx[ctx.length - i - 1];
          if (binding.name == t.name) {
            if (start != undefined && end != undefined) {
              spans.push({
                start: start,
                end: end,
                term: t,
                type: binding.typ,
                ctx: ctx,
              });
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
      case "syn": {
        return traverse(t.child, ty, undefined, undefined, ctx, defs);
      }
      // case "rel": {
      //   return traverse(t.term, ty, undefined, undefined, ctx, defs);
      // }
      case "label": {
        if (start != undefined && end != undefined) {
          spans.push({
            start: start,
            end: end,
            term: t,
            type: ty,
            ctx: ctx,
          });
        }

        return traverse(t.child, ty, undefined, undefined, ctx, defs);
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
          spans.push({
            start: start,
            end: end,
            term: t,
            type: ty,
            ctx: ctx,
          });
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
  detail?: string;
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
  defs: Map<string, Def2>,
  nondefs: ASTNode[],
  offset: number | undefined
): Array<Range & HoverInfo> => {
  let hoverInfo = new Array<Range & HoverInfo>();

  // Process definitions
  for (const [_, def] of defs) {
    const spans = inspect(def, defs, offset);
    for (const v of spans) {
      switch (v.term._) {
        case "lam":
          break;
        default:
          hoverInfo.push({
            start: v.start,
            end: v.end,
            msg: `${v.term._}(${pretty(v.type)})`,
          });
      }
      const msg = `${v.start}-${v.end} is a ${v.term._} with type ${pretty(
        v.type
      )}; ctx at this location is ${printCtx(v.ctx)}`;
      console.debug(printDiagnostic(src, TypecheckError(msg, v.start, v.end)));
    }
  }

  // Process non-definition nodes (comments, etc)
  for (const node of nondefs) {
    const spans = inspectASTNodes(node);
    for (const [k, v] of spans) {
      const msg = `${k.start}-${k.end} is a ${v.term._}`;
      console.debug(printDiagnostic(src, TypecheckError(msg, k.start, k.end)));

      switch (v.term._) {
        case "com":
          hoverInfo.push({ start: k.start, end: k.end, msg: v.term.text });
          break;
        default:
          hoverInfo.push({ start: k.start, end: k.end, msg: msg });
      }
    }
  }

  // Remove any duplicates. This may happen because of nested Origin nodes in
  // the AST.
  let result = new Array<Range & HoverInfo>();
  for (const hi of hoverInfo) {
    if (
      result.find((x) => x.start == hi.start && x.end == hi.end) == undefined
    ) {
      result.push(hi);
    }
  }

  return result;
};

export const hoverMessage = (
  src: string,
  defs: Map<string, Def2>,
  nondefs: ASTNode[],
  offset: number
): { range: { start: number; end: number }; msg: string } | null => {
  const hoverInfo = hover(src, defs, nondefs, offset);

  const overlappingSpans = hoverInfo.filter(
    (hi) => hi.start <= offset && hi.end > offset
  );

  // find the shortest node that overlaps this offset
  overlappingSpans.sort((a, b) => a.end - a.start - (b.end - b.start));

  for (const span of overlappingSpans) {
    console.log(`  span(${span.start}-${span.end}): ${span.msg}`);
  }

  if (overlappingSpans.length == 0) {
    return null;
  }

  return {
    range: { start: overlappingSpans[0].start, end: overlappingSpans[0].end },
    msg: overlappingSpans[0].msg,
  };
};

// Finds the type of the hole at this offset in the AST.
export const inferType = (
  src: string,
  defs: Map<string, Def2>,
  offset: number
): CTerm | undefined => {
  for (const [_, def] of defs) {
    const spans = inspect(def, defs);

    const overlapping = spans.filter(
      (v) => v.start <= offset && v.end > offset
    );

    const shortest = overlapping.sort((a, b) => {
      const lena = a.end - a.start;
      const lenb = b.end - b.start;
      return lena - lenb;
    });

    for (const v of shortest) {
      console.log(
        printMultilineDiagnostic(
          src,
          TypecheckError(
            `${v.term._}: ${printCtx(v.ctx)} ${pretty(v.term)}`,
            v.start,
            v.end
          )
        )
      );

      return v.type;
    }
  }

  return undefined;
};

export const findOrigin = (term: CTerm): Origin | null => {
  if (term._ == "orig") {
    return term;
  } else if (term._ == "ann") {
    return findOrigin(term.term);
  } else if (term._ == "syn") {
    return findOrigin(term.child);
  }
  return null;
};

export const definitionLocation = (
  src: string,
  defs: Map<string, Def2>,
  offset: number
): { start: number; end: number }[] => {
  var spans: Span[] = [];
  for (const [_, def] of defs) {
    const spans1 = inspect(def, defs);
    spans = [...spans, ...spans1];
  }

  const overlappingSpans = [...spans].filter(
    (v) => v.start <= offset && v.end > offset
  );
  overlappingSpans.sort((a, b) => a.end - a.start - (b.end - b.start));

  for (const v of overlappingSpans) {
    console.log(
      printMultilineDiagnostic(
        src,
        TypecheckError(
          `${v.term._}: ${printCtx(v.ctx)} ${pretty(v.term)}`,
          v.start,
          v.end
        )
      )
    );
  }

  if (overlappingSpans.length == 0) {
    return [];
  }

  const what = overlappingSpans[0];
  const term = what.term;
  switch (term._) {
    case "ref":
      const def = defs.get(term.name);
      // Hand written defs have explicit start/end positions from the
      // parser.
      if (def?.start != undefined && def?.end != undefined) {
        return [
          {
            start: def.start,
            end: def.end,
          },
        ];
      }
      const tm = def?.term;
      if (tm) {
        const orig = findOrigin(tm);
        if (orig) {
          return [
            {
              start: orig.start,
              end: orig.end,
            },
          ];
        }
      }
    default:
  }
  return [];
};

const CompletionText = 1;
const CompletionMethod = 2;
const CompletionFunction = 3;
const CompletionConstructor = 4;
const CompletionField = 5;
const CompletionVariable = 6;
const CompletionClass = 7;
const CompletionInterface = 8;
const CompletionModule = 9;
const CompletionProperty = 10;
const CompletionUnit = 11;
const CompletionValue = 12;
const CompletionEnum = 13;
const CompletionKeyword = 14;
const CompletionSnippet = 15;
const CompletionColor = 16;
const CompletionFile = 17;
const CompletionReference = 18;
const CompletionFolder = 19;
const CompletionEnumMember = 20;
const CompletionConstant = 21;
const CompletionStruct = 22;
const CompletionEvent = 23;
const CompletionOperator = 24;
const CompletionTypeParameter = 25;

export const complete = (
  src: string,
  defs: Map<string, Def2>,
  offset: number,
  typ: CTerm | undefined
): CompletionInfo[] => {
  let completionList: CompletionInfo[] = [];

  // Collect variable completions from context at the cursor position
  for (const [_, def] of defs) {
    const spans = inspect(def, defs);

    for (const v of spans) {
      if (!(v.start <= offset && v.end > offset)) {
        continue;
      }

      console.log(
        printMultilineDiagnostic(
          src,
          TypecheckError(
            `${v.term._}: ${printCtx(v.ctx)} ${pretty(v.term)}`,
            v.start,
            v.end
          )
        )
      );

      for (let i = 0; i < v.ctx.length; i++) {
        const binding = v.ctx[i];

        try {
          // If this binding has the same type as the completion position,
          // then include the suggestion.
          if (
            typ == undefined ||
            equate(
              v.ctx,
              defs,
              binding.typ,
              typ,
              Var(binding.name, v.ctx.length - i - 1)
            ).eq
          ) {
            completionList.push({
              label: binding.name,
              kind: CompletionVariable,
              sortText: "0",
              detail: `var(${pretty(binding.typ)})`,
            });
          }
        } catch (e) {
          console.error(e);
        }
      }
    }
  }

  // Add all top-level definitions as completions.
  for (const [_, def] of defs) {
    try {
      if (
        typ == undefined ||
        equate(
          [],
          defs,
          def.term.type,
          typ,
          Star() // does it matter that this is star?
        ).eq
      ) {
        if (def.term.type._ == "star") {
          completionList.push({
            label: def.name,
            kind: CompletionStruct,
            sortText: "1",
            detail: `ref(${pretty(def.term.type)})`,
          });
        } else {
          completionList.push({
            label: def.name,
            kind: CompletionFunction,
            sortText: "1",
            detail: `ref(${pretty(def.term.type)})`,
          });
        }
      }
    } catch (e) {
      console.error(e);
    }
  }

  return completionList;
};

// astToHtml outputs a html file that can be used to debug the AST along with
// the source.
export const astToHtml = (src: string, built: BuildResult): string => {
  // Loop over every def in the source and compute all of the spans.
  const spans: Span[] = [];
  for (const [_, def] of built.defs) {
    const spans1 = inspect(def, built.defs);
    spans.push(...spans1);
  }

  const lines = src.split("\n");

  const mapWhitespace = (c: string) => (c == " " ? "&nbsp;" : c);

  const lineColToOffset = (line: number, col: number) =>
    lines
      .slice(0, line)
      .map((s) => s.length + 1) // add 1 for newline
      .reduce((a, b) => a + b, 0) + col;

  return `
  <!DOCTYPE html>
  <html lang="en">
  <head>
  <meta charset="utf-8">
  <title></title>
  <style>
    body { font-family: monospace; padding-bottom: 500px; }
    .tooltip-wrap {
      position: relative;
      cursor: crosshair;
    }
    .tooltip-wrap .tooltip-content {
      display: none;
      position: absolute;
      bottom: 0%;
      left: 50px;
      right: 0%;
      top: 50px;
      width: 500px;
      height: 400px;
      overflow-y: scroll;
      background-color: #fff;
      padding: .5em;
      min-width: 10rem;
      border: 1px solid #000;
      z-index: 1;
    }
    .tooltip-wrap:hover {
      background-color: #0000ff;
      color: #fff;
    }
    .tooltip-wrap:hover .tooltip-content {
      display: block;
      color: #000;
    }
    .line {
      display: flex;
      flex-direction: row;
    }
  </style>
  </head>
  <body>
  ${lines
    .map(
      (l, linenum) =>
        `<div class="line l${linenum + 1}"><span style="width: 50px;">${
          linenum + 1
        }</span>${l
          .split("")
          .map((c, colnum) => {
            const offset = lineColToOffset(linenum, colnum);
            return `<div class="col c${
              colnum + 1
            } tooltip-wrap">${mapWhitespace(
              c
            )}<div class="tooltip-content"><div>offset=${offset}</div>${spans
              .filter((s) => s.start <= offset && s.end >= offset)
              // sort by length of span
              .toSorted((a, b) => {
                const lenA = a.end - a.start;
                const lenB = b.end - b.start;
                return lenA - lenB;
              })
              .map(
                (s) =>
                  `<div>(${s.start}-${s.end}) ${s.term._}  ${pretty(
                    s.term
                  )} type: ${pretty(s.type)}</div>`
              )
              .join("")}</div></div>`;
          })
          .join("")}</div>`
    )
    .join("")}
  </body>
  </html>
  `;
};
