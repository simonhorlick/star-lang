import { Term } from "./ast";
import { identifier } from "./check";
import * as Erased from "./erased";

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

// Evaluate this term by a single step. When applied to a term that is not yet a value, it yields
// the next step of evaluation for that term. When applied to a value an exception is thrown.
export function reduceOnce2(
  defs: Erased.Def[],
  term: Erased.Term
): Erased.Term {
  let isValue = (term: Erased.Term) => term._ == "lam";
  switch (term._) {
    case "app":
      if (term.left._ == "lam" && isValue(term.right)) {
        // E-AppAbs: (λx:T11.t12)v2 → [x/v2]t12
        return termSubstTop2(term.right, term.left.body);
      } else if (isValue(term.left)) {
        // E-App2
        return Erased.App(term.left, reduceOnce2(defs, term.right));
      } else {
        // E-App1
        return Erased.App(reduceOnce2(defs, term.left), term.right);
      }
    case "lam":
      throw "cannot reduce Abs";
    case "var":
      throw "cannot reduce Var";
    case "ref":
      const match = defs.filter((d) => d.name == term.name);
      if (match.length == 0) {
        return term;
      }
      return match[0].term;
  }
}

export function reduce(defs: Erased.Def[], t: Erased.Term): Erased.Term {
  let isValue = (term: Erased.Term) => term._ == "lam";
  while (!isValue(t)) {
    t = reduceOnce2(defs, t);
  }
  return t;
}
