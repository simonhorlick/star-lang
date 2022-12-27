import { Term, Type } from "./ast";

// pretty print a type
export function prettyT(type: Type): string {
  switch (type.type) {
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
  switch (term.type) {
    case "lam":
      const type = term.typ.type == "ers" ? "" : ":" + prettyT(term.typ);
      return "λ" + term.name + type + ". " + pretty(term.body);
    case "app":
      if (term.left.type == "ref") {
        return pretty(term.left) + "(" + pretty(term.right) + ")";
      } else {
        return "(" + pretty(term.left) + ")(" + pretty(term.right) + ")";
      }
    case "ref":
      return term.name;
    default:
      return "<unknown>";
  }
}
