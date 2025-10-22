import { Context } from "./context";
import * as Erased from "./erased";
import { App, Expression, Term } from "./pratt";

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

// Turns a tree of App nodes into a list, with the innermost App node at the
// head of the list.
//
// App(App(f,a),b) => [f,a,b]
//
const collectApps = (term: App): Expression[] => {
  if (term.func._ == "app") {
    return collectApps(term.func).concat(term.arg);
  } else {
    // base case: innermost app f(a)
    return [term.func, term.arg];
  }
};
const collectAppsC = (term: Erased.App): Erased.Term[] => {
  if (term.left._ == "app") {
    return collectAppsC(term.left).concat(term.right);
  } else {
    // base case: innermost app f(a)
    return [term.left, term.right];
  }
};

// pretty print a term
export function pretty(
  term?: Expression,
  indices: boolean = false,
  annotate: boolean = false
): string {
  const pretty = (term?: Expression): string => {
    if (term == undefined) {
      return "#undefined#";
    }
    switch (term._) {
      case "lam":
        return "λ" + pretty(term.name) + " " + pretty(term.body) + "";
      case "self":
        return `ι${term.name}. ${pretty(term.body)}`;
      case "app": {
        // App(f,a) => f(a)
        // App(App(f,a),b) => f(a,b)

        // Does the left hand side of the app require parenthesis for
        // disambiguation?
        const needsParens = (t: Expression): boolean => {
          switch (t._) {
            case "lam":
            case "self":
            case "pi":
            case "ann":
              return true;
            case "orig":
            case "syn":
              return needsParens(t.child);
            // case "rel":
            //   return needsParens(t.term);
            default:
              return false;
          }
        };

        const apps = collectApps(term);
        const pfunc = pretty(apps[0]);
        const func = needsParens(apps[0]) ? `(` + pfunc + `)` : pfunc;
        return func + "(" + apps.slice(1).map(pretty).join(",") + ")";
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
            `(` +
            pretty(term.term) +
            `):${begin}` +
            pretty(term.type) +
            `${end}`
          );
        } else {
          return pretty(term.term);
        }
      case "star":
        return "★";
      case "case":
        return `case ${pretty(term.name)} of${term.branches
          .map((b) => `\n|  ${pretty(b.constructor)} => ${pretty(b.term)}`)
          .join("")}`;
      case "let":
        return `let ${pretty(term.name)} = ${pretty(term.expr)} in ${pretty(
          term.body
        )}`;
      case "orig":
        return pretty(term.child);
      case "syn":
        return pretty(term.child);
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
      case "add":
        return `(${pretty(term.lhs)} + ${pretty(term.rhs)})`;
      case "sub":
        return `(${pretty(term.lhs)} - ${pretty(term.rhs)})`;
      case "mul":
        return `(${pretty(term.lhs)} * ${pretty(term.rhs)})`;
      case "div":
        return `(${pretty(term.lhs)} / ${pretty(term.rhs)})`;
      case "comp":
        return `(${pretty(term.lhs)} . ${pretty(term.rhs)})`;
      case "idx":
        return `${pretty(term.arr)}[${pretty(term.idx)}]`;
      case "cat":
        return `(${pretty(term.lhs)} ++ ${pretty(term.rhs)})`;
      case "gt":
        return `(${pretty(term.lhs)} > ${pretty(term.rhs)})`;
      case "lt":
        return `(${pretty(term.lhs)} < ${pretty(term.rhs)})`;
      case "gte":
        return `(${pretty(term.lhs)} >= ${pretty(term.rhs)})`;
      case "lte":
        return `(${pretty(term.lhs)} <= ${pretty(term.rhs)})`;
      case "eq":
        return `(${pretty(term.lhs)} == ${pretty(term.rhs)})`;
      case "neq":
        return `(${pretty(term.lhs)} != ${pretty(term.rhs)})`;
      case "and":
        return `(${pretty(term.lhs)} && ${pretty(term.rhs)})`;
      case "or":
        return `(${pretty(term.lhs)} || ${pretty(term.rhs)})`;
      case "cons":
        return `(${pretty(term.head)} :: ${pretty(term.tail)})`;
      case "nil":
        return `[]`;
      case "neg":
        return `(-${pretty(term.exp)})`;
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
      // Does the left hand side of the app require parenthesis for
      // disambiguation?
      const needsParens = (t: Erased.Term): boolean => {
        switch (t._) {
          case "lam":
            return true;
          default:
            return false;
        }
      };

      const apps = collectAppsC(term);
      const pfunc = prettyC(apps[0], indices);
      const func = needsParens(apps[0]) ? `(` + pfunc + `)` : pfunc;
      return (
        func +
        "(" +
        apps
          .slice(1)
          .map((t) => prettyC(t, indices))
          .join(",") +
        ")"
      );
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
