import { Term } from "./ast";
import { identifier } from "./check";
import * as Erased from "./erased";
import { prettyC } from "./pretty";

export function erase(term: Term): Erased.Term {
  // TODO: remove unused arguments
  switch (term._) {
    case "var":
      return Erased.Var(term.name, term.index);
    case "lam":
      return Erased.Abs(identifier(term.name), erase(term.body));
    case "app":
      return Erased.App(erase(term.left), erase(term.right));
    case "ann":
      return erase(term.term);
    case "ref":
      return Erased.Ref(term.name);
    case "pi":
      throw "erase: unexpected pi";
    case "star":
      throw "erase: unexpected star";
    case "case":
      throw "erase: unexpected case";
    case "if":
      throw "erase: unexpected if";
    case "self":
      // throw "unexpected self";
      return Erased.Abs("erased", Erased.Var("erased", 0));
    case "orig":
      return erase(term.child);
    case "par":
      throw "erase: unexpected par";
    case "id":
      throw "erase: unexpected id";
    case "hole":
      throw "erase: unexpected hole";
    case "int":
      throw "erase: unexpected integer literal";
    case "str":
      throw "erase: unexpected string literal";
    case "err":
      throw "erase: unexpected parse error";
  }
}

// Shifting renumbers the indices of the free variables in a term.
export function termShift2(d: number, t: Erased.Term): Erased.Term {
  const walk = (d: number, c: number, t: Erased.Term): Erased.Term => {
    switch (t._) {
      case "var":
        if (t.index >= c) {
          return Erased.Var(t.name, t.index + d);
        } else {
          return Erased.Var(t.name, t.index);
        }
      case "lam":
        return Erased.Abs(t.name, walk(d, c + 1, t.body));
      case "app":
        return Erased.App(walk(d, c, t.left), walk(d, c, t.right));
      case "ref":
        return t;
    }
  };
  return walk(d, 0, t);
}

// Given a term t, find all Vars with index j and replace them with the term s.
export function termSubst2(
  j: number,
  s: Erased.Term,
  t: Erased.Term
): Erased.Term {
  const walk = (
    j: number,
    s: Erased.Term,
    c: number,
    t: Erased.Term
  ): Erased.Term => {
    switch (t._) {
      case "var":
        if (t.index == j + c) {
          // Substitute in the term s, renumbering any free variables so the
          // expression is consistent.
          return termShift2(c, s);
        } else {
          return Erased.Var(t.name, t.index);
        }
      case "lam":
        return Erased.Abs(t.name, walk(j, s, c + 1, t.body));
      case "app":
        return Erased.App(walk(j, s, c, t.left), walk(j, s, c, t.right));
      case "ref":
        return t;
    }
  };

  return walk(j, s, 0, t);
}

// The term being substituted for the bound variable is first shifted up by one, then the
// substitution is made, and then the whole result is shifted down by one to account for the
// fact that the bound variable has been used up.
export function termSubstTop2(s: Erased.Term, t: Erased.Term): Erased.Term {
  return termShift2(-1, termSubst2(0, termShift2(1, s), t));
}

// Traverse App terms and collect the arguments in-order.
//       ap
//      /  \
//     ap   d
//    /  \
//   ap   c
//  /  \
// a    b
export const traverseInOrder = (
  root: Erased.Term,
  rightDepthLimit: number
): Array<Erased.Term> => {
  const doTraverse = (
    s: Erased.Term,
    rightDepth: number
  ): Array<Erased.Term> => {
    if (rightDepth >= rightDepthLimit) {
      return [s];
    }
    if (s._ == "app") {
      return doTraverse(s.left, 0).concat(doTraverse(s.right, rightDepth + 1));
    } else {
      return [s];
    }
  };

  return doTraverse(root, 0);
};

export function toJsArray(s: Erased.Term): Array<Erased.Term> {
  // either `nil(T)` or `((cons(T))(head))(tail)`
  const terms = traverseInOrder(s, 1);
  if (terms[0]._ == "ref" && terms[0].name == "nil") {
    return [];
  } else if (terms[0]._ == "ref" && terms[0].name == "cons") {
    const head = terms[2];
    const tail = terms[3];
    return [head].concat(toJsArray(tail));
  } else {
    throw `unexpected ${prettyC(terms[0])}`;
  }
}

// A term is in normal form if it cannot be reduced any further. Reduce the
// expression so that it no longer contains any function applications and
// becomes in normal form.
//
// Normal-order evaluation of a lambda expression is the repeated application of the leftmost reducible function application. In other words, normal order evaluation is the strategy that always reduces the left-most outer-most redex first. You can think about normal-order evaluation as traversing the lambda expression and evaluating every function you find before evaluating any function arguments.
//
// Evaluate this term by. When applied to a term that is not yet a value, it yields
// the next step of evaluation for that term. When applied to a value an exception is thrown.
// This function delays reduction of the arguments. Due to the way datatypes are
// encoded as lambdas we cannot always eagerly evaluate arguments, for example
// an if statement is expressed as a function `if(c,t,f)` and we only ever want
// to evaluate the appropriate branch.
export function reduceOnce2(
  defs: Erased.Def[],
  term: Erased.Term
): [Erased.Term, boolean] {
  switch (term._) {
    case "app":
      if (term.left._ == "lam") {
        const abstraction = term.left;
        const argument = term.right;
        // Beta reduction. Substitute the argument in the body of the
        // abstraction.
        return [termSubstTop2(argument, abstraction.body), true];
      } else {
        if (term.left._ == "ref" && term.left.name == "runtime") {
          // runtime(["println","string"])
          const args = toJsArray(term.right);

          // (cons(T))("println")(cons(T)("string")(nil(T)))
          //
          console.log(args.map((x) => prettyC(x)).join(", "));
        }

        // we know left is an not an abstraction.
        if (term.left._ != "var") {
          const left = reduceOnce2(defs, term.left);
          return [Erased.App(left[0], term.right), true];
        } else {
          // if LHS is a var and RHS contains no redex, then the expression is
          // in normal form.
          const right = reduceOnce2(defs, term.right);
          return [Erased.App(term.left, right[0]), right[1]];
        }
      }
    case "lam":
      // As we substitute arguments into the body of abstractions we need to
      // reduce those.
      if (term.body._ == "var") {
        return [term, false];
      }
      const body = reduceOnce2(defs, term.body);
      return [Erased.Abs(term.name, body[0]), body[1]];
    case "var":
      throw "cannot reduce Var";
    case "ref":
      const match = defs.find((d) => d.name == term.name);
      if (match == undefined) {
        throw `reference not found: ${term.name}`;
      }
      return [match.term, true];
  }
}

export function reduce(defs: Erased.Def[], t: Erased.Term): Erased.Term {
  let normalForm = false;
  let prev: Erased.Term = t;
  while (!normalForm) {
    // console.log(prettyC(t, false));
    const [rt, b] = reduceOnce2(defs, t);
    normalForm = !b;

    // debug check
    if (!normalForm && prettyC(rt) == prettyC(prev)) {
      throw "no forward progress";
    }
    prev = t;
    t = rt;
  }
  return t;
}
