// Shifting renumbers the indices of the free variables in a term.
// If the variable index is greater than the cutoff, c, then adjust the index

import {
  AbsI,
  Ann,
  App,
  Branch,
  Case,
  If,
  Let,
  Origin,
  Pi,
  Rel,
  Self,
  Term,
  Var,
} from "./ast";

// by d.
export function shift(d: number, c: number, t: Term): Term {
  switch (t._) {
    case "var":
      return t.index >= c ? Var(t.name, t.index + d) : t;
    case "lam":
      return AbsI(t.name, shift(d, c + 1, t.body));
    case "self":
      return Self(t.name, shift(d, c + 1, t.body));
    case "app":
      return App(shift(d, c, t.left), shift(d, c, t.right));
    case "ann":
      return Ann(shift(d, c, t.term), t.typ);
    case "pi":
      return Pi(t.name, shift(d, c, t.from), shift(d, c + 1, t.body));
    case "star":
    case "ref":
    case "par":
    case "id":
    case "hole":
    case "int":
    case "str":
      return t;
    case "orig":
      return Origin(t.start, t.end, shift(d, c, t.child));
    case "case":
      return Case(
        shift(d, c, t.name),
        t.branches.map((b) => Branch(b.constructor, shift(d, c, b.term))) // TODO: Is this correct? Do we need to shift here?
      );
    case "let":
      return Let(t.name, shift(d, c, t.expr), shift(d, c + 1, t.body));
    case "if":
      return If(
        shift(d, c, t.condition),
        shift(d, c, t.trueBranch),
        shift(d, c, t.falseBranch)
      );
    case "rel":
      return Rel(shift(d, c, t.term), t.uses);
    case "err":
      return t;
  }
}

// Given a term t, find all Vars with index j and replace them with the term s.
export function subst(
  j: number,
  s: Term,
  c: number,
  t: Term,
  name: string
): Term {
  switch (t._) {
    case "var":
      // Substitute in the term s, renumbering any free variables so the
      // expression is consistent.
      // Debug check:
      // if (t.index == j + c && t.name != name) {
      //   throw `name mismatch in subst: var at index ${j + c} is ${
      //     t.name
      //   }; but expected to find ${name}`;
      // }
      return t.index == j + c ? shift(c, 0, s) : t;
    case "lam":
      return AbsI(t.name, subst(j, s, c + 1, t.body, name));
    case "self":
      return Self(t.name, subst(j, s, c + 1, t.body, name));
    case "app":
      return App(subst(j, s, c, t.left, name), subst(j, s, c, t.right, name));
    case "ann":
      return Ann(subst(j, s, c, t.term, name), t.typ);
    case "pi":
      return Pi(
        t.name,
        subst(j, s, c, t.from, name),
        subst(j, s, c + 1, t.body, name)
      );
    case "par":
      throw "subst: unexpected par";
    case "star":
    case "ref":
    case "id":
    case "hole":
    case "int":
    case "str":
      return t;
    case "orig":
      return Origin(t.start, t.end, subst(j, s, c, t.child, name));
    case "case":
      throw "subst: unexpected case";
    case "let":
      return Let(
        t.name,
        subst(j, s, c, t.expr, name),
        subst(j, s, c + 1, t.body, name)
      );
    case "if":
      throw "subst: unexpected if";
    case "rel":
      return Rel(subst(j, s, c, t.term, name), t.uses);
    case "err":
      throw "subst: unexpected parse error";
  }
}

// Replaces all instances of Var(0) with s in the term t. A name can be passed
// as a sanity check to ensure the substituted variables are the correct ones.
export function substTop(s: Term, t: Term, name: string): Term {
  // The term being substituted for the bound variable is first shifted up by one, then the
  // substitution is made, and then the whole result is shifted down by one to account for the
  // fact that the bound variable has been used up.
  return shift(-1, 0, subst(0, shift(1, 0, s), 0, t, name));
}

// Given a term t, find all Holes with index j and replace them with the term s.
export function substHole(j: number, s: Term, t: Term): Term {
  switch (t._) {
    case "var":
      return t;
    case "lam":
      return AbsI(t.name, substHole(j, s, t.body));
    case "self":
      return Self(t.name, substHole(j, s, t.body));
    case "app":
      return App(substHole(j, s, t.left), substHole(j, s, t.right));
    case "ann":
      return Ann(substHole(j, s, t.term), substHole(j, s, t.typ));
    case "pi":
      return Pi(t.name, substHole(j, s, t.from), substHole(j, s, t.body));
    case "par":
      throw "substHole: unexpected par";
    case "star":
    case "ref":
    case "id":
    case "int":
    case "str":
      return t;
    case "hole":
      if (t.id == j) {
        return s;
      }
      return t;
    case "orig":
      return Origin(t.start, t.end, substHole(j, s, t.child));
    case "case":
      throw "substHole: unexpected case";
    case "let":
      throw "substHole: unexpected let";
    case "if":
      throw "substHole: unexpected if";
    case "rel":
      return Rel(substHole(j, s, t.term), t.uses);
    case "err":
      throw "substHole: unexpected parse error";
  }
}
