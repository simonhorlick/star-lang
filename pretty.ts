import { Context, Term } from "./ast";
import * as Erased from "./erased";

export function printCtx(ctx: Context, indices: boolean = true): string {
  return ctx.map((v) => `\t${v.name}:${pretty(v.typ, indices)}`).join(",\n");
}

// pretty print a term
export function pretty(term: Term, indices: boolean = true): string {
  switch (term._) {
    case "lam":
      return (
        "λ" +
        term.name +
        // ":" +
        // prettyT(term.bindType, indices) +
        ". " +
        pretty(term.body, indices) +
        ""
      );
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
      return term.name;
    case "var":
      if (indices) {
        return `${term.name}#${term.index}`;
      } else {
        return `${term.name}`;
      }
    case "par":
      return `${term.name}`;
    case "pi":
      if (term.name == "") {
        return pretty(term.from, indices) + "→" + pretty(term.to, indices);
      } else {
        return `Π${term.name}:${pretty(term.from, indices)}. ${pretty(
          term.to,
          indices
        )}`;
      }
    case "ann":
      return (
        "(" + pretty(term.term, indices) + "):" + pretty(term.typ, indices)
      );
    case "star":
      return "★";
    case "case":
      return `case ${pretty(term.name)} of ${term.branches
        .map((b) => `${b.constructor} -> ${pretty(b.term)}`)
        .join(" | ")}`;
    case "orig":
      return pretty(term.child);
  }
}

// pretty print an erased term
export function prettyC(term: Erased.Term, indices: boolean = true): string {
  switch (term._) {
    case "lam":
      return "λ" + term.name + ". " + prettyC(term.body, indices) + "";
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
        return `${term.index}`;
      } else {
        return `${term.name}@${term.index}`;
      }
  }
}
