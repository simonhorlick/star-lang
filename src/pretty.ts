import { Term, identifier2str } from "./ast";
import { Context } from "./context";
import * as Erased from "./erased";
import { foldTree } from "./inspect";

export function printCtxMultiline(
  ctx: Context,
  indices: boolean = false
): string {
  return (
    "[" +
    ctx
      .map(
        (v, i) => `\n ${ctx.length - i - 1} ${v.name}:${pretty(v.typ, indices)}`
      )
      .join("") +
    "\n]"
  );
}

export function printCtx(ctx: Context, indices: boolean = false): string {
  return (
    "[" +
    ctx
      .map(
        (v, i) =>
          `${v.name}${indices ? `@${ctx.length - i - 1}` : ""}:${pretty(
            v.typ,
            indices
          )}`
      )
      .join(", ") +
    "]"
  );
}

// pretty print a term
export function pretty(
  term?: Term,
  indices: boolean = false,
  annotate: boolean = false
): string {
  const pretty = (term?: Term): string => {
    if (term == undefined) {
      return "#undefined#";
    }
    switch (term._) {
      case "lam":
        return "λ" + pretty(term.name) + " " + pretty(term.body) + "";
      case "self":
        return `ι${term.name}. ${pretty(term.body)}`;
      case "app": {
        let l = pretty(term.func);
        let r = "(" + pretty(term.arg) + ")";

        if (term.func._ == "lam" || term.func._ == "ann") {
          l = "(" + l + ")";
        }

        return l + r;
      }
      case "ref":
      case "id":
        return term.name;
      case "key":
        return term.key;
      case "var":
        if (indices) {
          return `${term.name}@${term.index}`;
        } else {
          return `${term.name}`;
        }
      case "par":
        return `${term.name}`;
      case "pi":
        if (term.name == "") {
          return pretty(term.from) + "→" + pretty(term.body);
        } else {
          return `(Π${term.name}:${pretty(term.from)} ${pretty(term.body)})`;
        }
      case "ann":
        if (annotate) {
          const consoleColours = false;
          const begin = consoleColours ? "\x1b[34m" : "";
          const end = consoleColours ? "\x1b[0m" : "";
          return (
            `(` + pretty(term.term) + `):${begin}` + pretty(term.typ) + `${end}`
          );
        } else {
          return pretty(term.term);
        }
      case "star":
        return "★";
      case "case":
        return `case ${pretty(term.name)} of${term.branches
          .map((b) => `\n|  ${pretty(b.constructor)} -> ${pretty(b.term)}`)
          .join("")}`;
      case "let":
        return `let ${pretty(term.name)} = ${pretty(term.expr)} in ${pretty(
          term.body
        )}`;
      case "orig":
        return pretty(term.child);
      case "syn":
        return pretty(term.child);
      case "rel":
        return pretty(term.term);
      case "if":
        return `if ${pretty(term.condition)} then ${pretty(
          term.trueBranch
        )} else ${pretty(term.falseBranch)}`;
      case "hole":
        return `▨${term.id}`;
      case "int":
        return `${term.num}`;
      case "str":
        return `"${term.str}"`;
      case "label":
        return `@${term.label} ${pretty(term.child)}`;
      case "err":
        return `##${term.msg}##`;
    }
  };
  return pretty(term);
}

// pretty print an erased term
export function prettyC(term: Erased.Term, indices: boolean = false): string {
  switch (term._) {
    case "lam":
      // case "vlam":
      return "λ" + term.name + " " + prettyC(term.body, indices) + "";
    // case "vapp":
    case "app": {
      let l = prettyC(term.left, indices);
      let r = "(" + prettyC(term.right, indices) + ")";

      if (term.left._ == "lam") {
        l = "(" + l + ")";
      }

      return l + r;
    }
    case "ref":
      return term.name;
    case "var":
      if (indices) {
        return `${term.name}@${term.index}`;
      } else {
        return `${term.name}`;
      }
    case "str":
      return `"${term.str}"`;
  }
}

let count: number = 1;
const idMap: WeakMap<Record<string, unknown> | Array<unknown>, number> =
  new WeakMap<Record<string, unknown> | Array<unknown>, number>();

function uid(object: Term): string {
  const objectId = idMap.get(object);
  if (objectId === undefined) {
    count += 1;
    idMap.set(object, count);
    return `${object._}_${count}`;
  }
  return `${object._}_${objectId}`;
}

export const printNodeAsDotGraph = (term: Term): string => {
  let output = ``;
  output += `digraph prof {`;
  output += `  fontname="Helvetica,Arial,sans-serif"`;
  output += `  node [fontname="Helvetica,Arial,sans-serif"]`;
  output += `  edge [fontname="Helvetica,Arial,sans-serif"]`;
  output += `  node [style=filled];`;

  output += foldTree(
    (acc, curr) => {
      // add this AST node to the graph
      let node = "";
      // add any edges to the child AST nodes
      let edges = "";
      switch (curr._) {
        case "ann":
          node = `  "${uid(curr)}" [label="ann"];\n`;
          edges += `  "${uid(curr)}" -> "${uid(curr.term)}";\n`;
          edges += `  "${uid(curr)}" -> "${uid(curr.typ)}";\n`;
          break;
        case "app":
          node = `  "${uid(curr)}" [label="@"];\n`;
          edges += `  "${uid(curr)}" -> "${uid(curr.func)}";\n`;
          edges += `  "${uid(curr)}" -> "${uid(curr.arg)}";\n`;
          break;
        case "case":
          node = `  "${uid(curr)}" [label="case ${curr.name}"];\n`;
          for (const branch of curr.branches) {
            edges += `  "${uid(curr)}" -> "${uid(branch.term)}";\n`;
          }
          break;
        case "err":
          node = `  "${uid(curr)}" [label="err ${curr.msg}"];\n`;
          break;
        case "hole":
          node = `  "${uid(curr)}" [label="hole ${curr.id}"];\n`;
          break;
        case "id":
          node = `  "${uid(curr)}" [label="${curr.name}"];\n`;
          break;
        case "int":
          node = `  "${uid(curr)}" [label="${curr.num}"];\n`;
          break;
        case "str":
          node = `  "${uid(curr)}" [label="${curr.str}"];\n`;
          break;
        case "var":
          node = `  "${uid(curr)}" [label="${curr.name}"];\n`;
          break;
        case "star":
          node = `  "${uid(curr)}" [label="★"];\n`;
          break;
        case "par":
          node = `  "${uid(curr)}" [label="${curr.name}"];\n`;
          break;
        case "ref":
          node = `  "${uid(curr)}" [label="${curr.name}"];\n`;
          break;
        case "if":
          node = `  "${uid(curr)}" [label="if"];\n`;
          edges += `  "${uid(curr)}" -> "${uid(curr.condition)}";\n`;
          edges += `  "${uid(curr)}" -> "${uid(curr.falseBranch)}";\n`;
          edges += `  "${uid(curr)}" -> "${uid(curr.trueBranch)}";\n`;
          break;
        case "lam":
          node = `  "${uid(curr)}" [label="λ${identifier2str(curr.name)}"];\n`;
          edges += `  "${uid(curr)}" -> "${uid(curr.body)}";\n`;
          break;
        case "let":
          node = `  "${uid(curr)}" [label="let ${identifier2str(
            curr.name
          )}"];\n`;
          edges += `  "${uid(curr)}" -> "${uid(curr.body)}";\n`;
          edges += `  "${uid(curr)}" -> "${uid(curr.expr)}";\n`;
          break;
        case "orig":
          node = `  "${uid(curr)}" [label="orig ${curr.start}-${curr.end}"];\n`;
          edges += `  "${uid(curr)}" -> "${uid(curr.child)}";\n`;
          break;
        case "label":
          node = `  "${uid(curr)}" [label="${curr.label}"];\n`;
          edges += `  "${uid(curr)}" -> "${uid(curr.child)}";\n`;
          break;
        case "pi":
          node = `  "${uid(curr)}" [label="Π${curr.name}"];\n`;
          edges += `  "${uid(curr)}" -> "${uid(curr.from)}";\n`;
          edges += `  "${uid(curr)}" -> "${uid(curr.body)}";\n`;
          break;
        case "rel":
          node = `  "${uid(curr)}" [label="rel ${curr.uses}"];\n`;
          edges += `  "${uid(curr)}" -> "${uid(curr.term)}";\n`;
          break;
        case "self":
          node = `  "${uid(curr)}" [label="ι${curr.name}"];\n`;
          edges += `  "${uid(curr)}" -> "${uid(curr.body)}";\n`;
          break;
      }
      return acc + node + edges;
    },
    "",
    term
  );

  output += `}`;

  return output;
};
