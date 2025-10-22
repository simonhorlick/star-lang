// Shifting renumbers the indices of the free variables in a term.
// If the variable index is greater than the cutoff, c, then adjust the index

import {
  AbsI,
  Ann,
  App,
  Branch,
  Case,
  Cons,
  CTerm,
  Idx,
  Label,
  Let,
  Nil,
  Origin,
  Pi,
  // Rel,
  Self,
  Syntax,
  Var,
} from "./sugar";

// Shift all Var indices up by d.
export function shift(d: number, c: number, t: CTerm): CTerm {
  switch (t._) {
    case "var":
      return t.index >= c ? Var(t.name, t.index + d) : t;
    case "lam":
      return AbsI(t.name, shift(d, c + 1, t.body));
    case "self":
      return Self(t.name, shift(d, c + 1, t.body));
    case "app":
      return App(shift(d, c, t.func), shift(d, c, t.arg));
    case "ann":
      return Ann(shift(d, c, t.term), t.type);
    case "pi":
      return Pi(t.name, shift(d, c, t.from), shift(d, c + 1, t.body));
    case "star":
    case "ref":
    case "id":
    case "key":
    case "hole":
    case "int":
    case "str":
      return t;
    case "orig":
      return Origin(t.start, t.end, shift(d, c, t.child));
    case "syn":
      return Syntax(t.syntax, shift(d, c, t.child));
    case "label":
      return Label(t.label, shift(d, c, t.child));
    case "case":
      return Case(
        shift(d, c, t.name),
        t.branches.map((b) => Branch(b.constructor, shift(d, c, b.term))) // TODO: Is this correct? Do we need to shift here?
      );
    case "let":
      return Let(t.name, shift(d, c, t.expr), shift(d, c + 1, t.body));
    // case "rel":
    //   return Rel(shift(d, c, t.term), t.uses);
    case "err":
      return t;
  }
}

// Given a term t, find all Vars with index j and replace them with the term s.
export function subst(
  j: number,
  s: CTerm,
  c: number,
  t: CTerm,
  name: string
): CTerm {
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
      return App(subst(j, s, c, t.func, name), subst(j, s, c, t.arg, name));
    case "ann":
      return Ann(subst(j, s, c, t.term, name), t.type);
    case "pi":
      return Pi(
        t.name,
        subst(j, s, c, t.from, name),
        subst(j, s, c + 1, t.body, name)
      );
    case "star":
    case "ref":
    case "id":
    case "key":
    case "hole":
    case "int":
    case "str":
      return t;
    case "orig":
      return Origin(t.start, t.end, subst(j, s, c, t.child, name));
    case "syn":
      return Syntax(t.syntax, subst(j, s, c, t.child, name));
    case "case":
      return Case(
        t.name,
        t.branches.map((b) =>
          Branch(b.constructor, subst(j, s, c, b.term, name))
        )
      );
    case "let":
      return Let(
        t.name,
        subst(j, s, c, t.expr, name),
        subst(j, s, c + 1, t.body, name)
      );
    case "label":
      return Label(t.label, subst(j, s, c, t.child, name));
    // case "rel":
    //   return Rel(subst(j, s, c, t.term, name), t.uses);
    case "err":
      return t;
  }
}

// Replaces all instances of Var(0) with s in the term t. A name can be passed
// as a sanity check to ensure the substituted variables are the correct ones.
export function substTop(s: CTerm, t: CTerm, name: string): CTerm {
  // The term being substituted for the bound variable is first shifted up by one, then the
  // substitution is made, and then the whole result is shifted down by one to account for the
  // fact that the bound variable has been used up.
  return shift(-1, 0, subst(0, shift(1, 0, s), 0, t, name));
}

// Given a term t, find all Holes with index j and replace them with the term s.
export function substHole(j: number, s: CTerm, t: CTerm): CTerm {
  switch (t._) {
    case "var":
      return t;
    case "lam":
      return AbsI(t.name, substHole(j, s, t.body));
    case "self":
      return Self(t.name, substHole(j, s, t.body));
    case "app":
      return App(substHole(j, s, t.func), substHole(j, s, t.arg));
    case "ann":
      return Ann(substHole(j, s, t.term), substHole(j, s, t.type));
    case "pi":
      return Pi(t.name, substHole(j, s, t.from), substHole(j, s, t.body));
    case "star":
    case "ref":
    case "id":
    case "key":
    case "int":
    case "str":
    case "err":
      return t;
    case "hole":
      if (t.id == j) {
        return s;
      }
      return t;
    case "orig":
      return Origin(t.start, t.end, substHole(j, s, t.child));
    case "syn":
      return Syntax(t.syntax, substHole(j, s, t.child));
    case "case":
      throw "substHole: unexpected case";
    case "let":
      throw "substHole: unexpected let";
    case "label":
      return Label(t.label, substHole(j, s, t.child));
    // case "rel":
    //   return Rel(substHole(j, s, t.term), t.uses);
  }
}
