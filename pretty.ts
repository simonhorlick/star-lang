import { Context, Term } from "./ast";
import * as Erased from "./erased";

export function printCtx(ctx: Context, indices: boolean = false): string {
  return (
    "[" + ctx.map((v) => `${v.name}:${pretty(v.typ, indices)}`).join(", ") + "]"
  );
}

// pretty print a term
export function pretty(
  term: Term,
  indices: boolean = false,
  annotate: boolean = false
): string {
  const pretty = (term: Term): string => {
    if (term == undefined) {
      return "#undefined#";
    }
    switch (term._) {
      case "lam":
        return "λ" + pretty(term.name) + " " + pretty(term.body) + "";
      case "self":
        return `ι${term.name}. ${pretty(term.body)}`;
      case "app": {
        let l = pretty(term.left);
        let r = "(" + pretty(term.right) + ")";

        if (term.left._ == "lam") {
          l = "(" + l + ")";
        }

        return l + r;
      }
      case "ref":
      case "id":
        return term.name;
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
          return pretty(term.from) + "→" + pretty(term.to);
        } else {
          return `(Π${term.name}:${pretty(term.from)}. ${pretty(term.to)})`;
        }
      case "ann":
        if (annotate) {
          const begin = "\x1b[34m";
          const end = "\x1b[0m";
          return (
            `(` + pretty(term.term) + `:${begin}` + pretty(term.typ) + `${end})`
          );
        } else {
          return pretty(term.term);
        }
      case "star":
        return "★";
      case "case":
        return `case ${pretty(term.name)} of ${term.branches
          .map((b) => `${pretty(b.constructor)} -> ${pretty(b.term)}`)
          .join(" | ")}`;
      case "let":
        return `let ${pretty(term.name)} = ${pretty(term.expr)} in ${pretty(
          term.body
        )}`;
      case "orig":
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
