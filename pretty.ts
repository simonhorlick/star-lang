import { Term, Type } from "./ast";

// pretty print a type
export function prettyT(type: Type): string {
  switch (type._) {
    case "arrow":
      return prettyT(type.from) + "→" + prettyT(type.to);
    case "ers":
      return "";
    case "ref":
      return type.name;
    default:
      return "<unknown>";
  }
}

// pretty print a term
export function pretty(term: Term): string {
  switch (term._) {
    case "lam":
      const type = term.bindType._ == "ers" ? "" : ":" + prettyT(term.bindType);
      return "λ" + term.name + type + ". " + pretty(term.body) + "";
    case "app":
      let l = pretty(term.left);
      let r = "(" + pretty(term.right) + ")";

      if (term.left._ == "lam") {
        l = "(" + l + ")";
      }

      return l + r;
    case "ref":
      return term.name;
    case "var":
      return /*term.name*/ `${term.index}`;
    default:
      return "<unknown>";
  }
}
