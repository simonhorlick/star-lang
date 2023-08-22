import { Context, Term } from "./ast";
import * as Erased from "./erased";

export function printCtx(ctx: Context, indices: boolean = false): string {
  return (
    "[" + ctx.map((v) => `${v.name}:${pretty(v.typ, indices)}`).join(", ") + "]"
  );
}

// pretty print a term
export function pretty(term: Term, indices: boolean = false): string {
  if (term == undefined) {
    return "#undefined#";
  }
  switch (term._) {
    case "lam":
      return "λ" + pretty(term.name) + " " + pretty(term.body, indices) + "";
    case "self":
      return `ι${term.name}. ${pretty(term.body, indices)}`;
    case "app": {
      let l = pretty(term.left, indices);
      let r = "(" + pretty(term.right, indices) + ")";

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
        return pretty(term.from, indices) + "→" + pretty(term.to, indices);
      } else {
        return `(Π${term.name}:${pretty(term.from, indices)}. ${pretty(
          term.to,
          indices
        )})`;
      }
    case "ann":
      return pretty(term.term, indices);
    // return (
    //   "(" + pretty(term.term, indices) + "):" + pretty(term.typ, indices)
    // );
    case "star":
      return "★";
    case "case":
      return `case ${pretty(term.name, indices)} of ${term.branches
        .map(
          (b) =>
            `${pretty(b.constructor, indices)} -> ${pretty(b.term, indices)}`
        )
        .join(" | ")}`;
    case "let":
      return `let ${pretty(term.name, indices)} = ${pretty(
        term.expr,
        indices
      )} in ${pretty(term.body, indices)}`;
    case "orig":
      return pretty(term.child, indices);
    case "if":
      return `if ${pretty(term.condition, indices)} then ${pretty(
        term.trueBranch,
        indices
      )} else ${pretty(term.falseBranch, indices)}`;
    case "hole":
      return `▨${term.id}`;
    case "int":
      return `${term.num}`;
    case "str":
      return `"${term.str}"`;
    case "err":
      return `##${term.msg}##`;
  }
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
