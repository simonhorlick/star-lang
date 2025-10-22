import { Expression } from "./pratt";

// // map a function over the AST.
// export const mapTerm = (
//   f: (curr: Expression) => Expression, // returns the new accumulator
//   tt: Expression // the root of the trees
// ): Expression => {
//   const t = f(tt);
//   switch (t._) {
//     case "app":
//       return App(f(t.func), f(t.arg));
//     case "lam":
//       return AbsI(t.name, f(t.body));
//     case "ann":
//       return Ann(f(t.term), f(t.type));
//     case "case":
//       return Case(
//         f(t.name),
//         t.branches.map((b) => Branch(b.constructor, f(b.term)))
//       );
//     case "if":
//       return If(f(t.condition), f(t.trueBranch), f(t.falseBranch));
//     case "let":
//       return Let(t.name, f(t.expr), f(t.body));
//     case "orig":
//       return Origin(t.start, t.end, f(t.child));
//     case "syn":
//       return Syntax(t.syntax, f(t.child));
//     case "pi":
//       return Pi(t.name, f(t.from), f(t.body));
//     // case "rel":
//     //   return Rel(f(t.term), t.uses);
//     case "label":
//       return Label(t.label, f(t.child));
//     case "self":
//       return Self(t.name, f(t.body));
//     case "id":
//     case "key":
//     case "int":
//     case "par":
//     case "hole":
//     case "err":
//     case "star":
//     case "ref":
//     case "str":
//     case "nil":
//     case "var": {
//       return f(t);
//     }
//     case "neg":
//       return IntNeg(f(t.exp));
//     // binary operations
//     case "add":
//       return IntPlus(f(t.lhs), f(t.rhs));
//     case "sub":
//       return IntSub(f(t.lhs), f(t.rhs));
//     case "mul":
//       return IntMul(f(t.lhs), f(t.rhs));
//     case "div":
//       return IntDiv(f(t.lhs), f(t.rhs));
//     case "comp":
//       return Comp(f(t.lhs), f(t.rhs));
//     case "idx":
//       return Idx(f(t.arr), f(t.idx));
//     case "cat":
//       return Cat(f(t.lhs), f(t.rhs));
//     case "gt":
//       return Gt(f(t.lhs), f(t.rhs));
//     case "lt":
//       return Lt(f(t.lhs), f(t.rhs));
//     case "gte":
//       return Gte(f(t.lhs), f(t.rhs));
//     case "lte":
//       return Lte(f(t.lhs), f(t.rhs));
//     case "eq":
//       return Eq(f(t.lhs), f(t.rhs));
//     case "neq":
//       return Neq(f(t.lhs), f(t.rhs));
//     case "and":
//       return And(f(t.lhs), f(t.rhs));
//     case "or":
//       return Or(f(t.lhs), f(t.rhs));
//     case "cons":
//       return Cons(f(t.head), f(t.tail));
//     default:
//       return unreachable(t);
//   }
// };

// // pre-order traversal of the term tree - visit the node itself, followed by
// // any child nodes.
// export const foldTree = <A>(
//   f: (acc: A, curr: Expression) => A, // returns the new accumulator
//   init: A, // initial value of the accumulator
//   t: Expression // the starting term
// ): A => {
//   const x = f(init, t);
//   switch (t._) {
//     case "app": {
//       const left = foldTree(f, x, t.func);
//       const rght = foldTree(f, left, t.arg);
//       return rght;
//     }
//     case "lam": {
//       const curr = foldTree(f, x, t.name);
//       const body = foldTree(f, curr, t.body);
//       return body;
//     }
//     case "ann": {
//       const tm = foldTree(f, x, t.term);
//       const typ = foldTree(f, tm, t.type);
//       return typ;
//     }
//     case "case": {
//       const name = foldTree(f, x, t.name);
//       let prev = name;
//       for (const b of t.branches) {
//         const ctr = foldTree(f, prev, b.constructor);
//         prev = foldTree(f, ctr, b.term);
//       }
//       return prev;
//     }
//     case "if": {
//       const cond = foldTree(f, x, t.condition);
//       const fls = foldTree(f, cond, t.falseBranch);
//       const tru = foldTree(f, fls, t.trueBranch);
//       return tru;
//     }
//     case "let": {
//       const name = foldTree(f, x, t.name);
//       const expr = foldTree(f, name, t.expr);
//       const body = foldTree(f, expr, t.body);
//       return body;
//     }
//     case "orig": {
//       return foldTree(f, x, t.child);
//     }
//     case "syn": {
//       const syn = foldTree(f, x, t.syntax);
//       const child = foldTree(f, syn, t.child);
//       return child;
//     }
//     case "label": {
//       return foldTree(f, x, t.child);
//     }
//     case "pi": {
//       const frm = foldTree(f, x, t.from);
//       const to = foldTree(f, frm, t.body);
//       return to;
//     }
//     // case "rel": {
//     //   return foldTree(f, x, t.term);
//     // }
//     case "self": {
//       return foldTree(f, x, t.body);
//     }
//     case "id":
//     case "key":
//     case "int":
//     case "par":
//     case "hole":
//     case "err":
//     case "star":
//     case "ref":
//     case "str":
//     case "var": {
//       return x;
//     }
//     case "add":
//     case "sub":
//     case "mul":
//     case "div":
//     case "neg":
//     case "comp":
//     case "idx":
//     case "cat":
//     case "gt":
//     case "lt":
//     case "gte":
//     case "lte":
//     case "eq":
//     case "neq":
//     case "and":
//     case "or":
//     case "cons":
//     case "nil":
//       throw new Error(`unimplemented`);
//     default:
//       return unreachable(t);
//   }
// };

function unreachable(t: never): never {
  throw new Error(`not reachable`);
}
