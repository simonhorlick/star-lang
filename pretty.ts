import { Context, Kind, Term, Type } from "./ast";

// pretty print a kind
export function prettyK(kind: Kind): string {
  switch (kind._) {
    case "karrow":
      return prettyK(kind.from) + "→" + prettyK(kind.to);
    case "star":
      return "★";
  }
}

// pretty print a type
export function prettyT(type: Type, indices: boolean = true): string {
  switch (type._) {
    case "arrow":
      return prettyT(type.from, indices) + "→" + prettyT(type.to, indices);
    case "all":
      return "∀" + type.name + "::" + prettyK(type.kind) + ". " + type.to;
    case "ers":
      return "";
    case "ref":
      return type.name;
    case "var":
      if (indices) {
        return `${type.index}`;
      } else {
        return `${type.name}@${type.index}`;
      }
    case "ttabs":
      return (
        "λ" +
        type.name +
        "::" +
        prettyK(type.kind) +
        ". " +
        prettyT(type.body, indices) +
        ""
      );

    case "ttapp":
      let l = prettyT(type.left, indices);
      let r = "(" + prettyT(type.right, indices) + ")";

      if (type.left._ == "ttabs") {
        l = "(" + l + ")";
      }

      return l + r;
  }
}

export function printCtx(ctx: Context): string {
  return ctx
    .map(
      (v) => `${v.name}:${v.type == "bind" ? prettyT(v.typ) : prettyK(v.kind)}`
    )
    .join(",");
}

// pretty print a term
export function pretty(term: Term, indices: boolean = true): string {
  switch (term._) {
    case "lam": {
      const type =
        term.bindType._ == "ers" ? "" : ":" + prettyT(term.bindType, indices);
      return "λ" + term.name + type + ". " + pretty(term.body, indices) + "";
    }
    case "tabs": {
      return "Λ" + term.name + ". " + pretty(term.body, indices) + "";
    }
    case "app": {
      let l = pretty(term.left, indices);
      let r = "(" + pretty(term.right, indices) + ")";

      if (term.left._ == "lam") {
        l = "(" + l + ")";
      }

      return l + r;
    }
    case "tapp": {
      let l = pretty(term.left, indices);
      let r = "(" + prettyT(term.right, indices) + ")";

      if (term.left._ == "tabs") {
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
    case "ann":
      return (
        "(" + pretty(term.term, indices) + "):" + prettyT(term.typ, indices)
      );
  }
}
