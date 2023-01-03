import { Term, Type } from "./ast";

// pretty print a type
export function prettyT(type: Type): string {
  switch (type._) {
    case "arrow":
      return prettyT(type.from) + "→" + prettyT(type.to);
    case "all":
      return "∀" + type.name + ". " + type.to;
    case "ers":
      return "";
    case "ref":
      return type.name;
    case "var":
      return `${type.index}`;
    case "star":
      return "★";
  }
}

// pretty print a term
export function pretty(term: Term): string {
  switch (term._) {
    case "lam": {
      const type = term.bindType._ == "ers" ? "" : ":" + prettyT(term.bindType);
      return "λ" + term.name + type + ". " + pretty(term.body) + "";
    }
    case "tabs": {
      return "Λ" + term.name + ". " + pretty(term.body) + "";
    }
    case "app": {
      let l = pretty(term.left);
      let r = "(" + pretty(term.right) + ")";

      if (term.left._ == "lam" || term.left._ == "tabs") {
        l = "(" + l + ")";
      }

      return l + r;
    }
    case "ref":
      return term.name;
    case "var":
      return /*term.name*/ `${term.index}`;
    case "ann":
      return "(" + pretty(term.term) + "):" + prettyT(term.typ);
  }
}
