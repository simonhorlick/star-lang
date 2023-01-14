import {
  Term,
  Type,
  App,
  Abs,
  Var,
  Ref,
  Ann,
  Arrow,
  TAbs,
  All,
  TApp,
  Def,
  TTApp,
  TTAbs,
} from "./ast";
import * as Erased from "./erased";

export function isValue(term: Term): boolean {
  return term._ == "lam" || term._ == "tabs";
}

// Shifting renumbers the indices of the free variables in a term.
export function termShift(d: number, t: Term): Term {
  // The shifting function below takes a “cutoff” parameter c that controls which variables should
  // be shifted.
  const walk = (d: number, c: number, t: Term): Term => {
    if (t._ == "var") {
      let x = t.index;
      if (x >= c) {
        return Var(t.name, x + d);
      } else {
        return Var(t.name, x);
      }
    } else if (t._ == "lam") {
      let t1 = t.body;
      let ty = t.bindType;
      return Abs(t.name, walk(d, c + 1, t1), ty);
    } else if (t._ == "app") {
      return App(walk(d, c, t.left), walk(d, c, t.right));
    } else {
      return t;
    }
  };
  return walk(d, 0, t);
}

// Given a term t, find all Vars with index j and replace them with the term s.
export function termSubst(j: number, s: Term, t: Term): Term {
  const walk = (j: number, s: Term, c: number, t: Term): Term => {
    switch (t._) {
      case "var":
        if (t.index == j + c) {
          // Substitute in the term s, renumbering any free variables so the
          // expression is consistent.
          return termShift(c, s);
        } else {
          return Var(t.name, t.index);
        }
      case "lam":
        return Abs(t.name, walk(j, s, c + 1, t.body), t.bindType);
      case "app":
        return App(walk(j, s, c, t.left), walk(j, s, c, t.right));
      case "tabs":
        return TAbs(t.name, walk(j, s, c + 1, t.body), t.kind);
      case "tapp":
        return TApp(walk(j, s, c, t.left), t.right);
      case "ann":
        return Ann(walk(j, s, c, t.term), t.typ);
      case "ref":
        return t;
    }
  };
  return walk(j, s, 0, t);
}

// The term being substituted for the bound variable is first shifted up by one, then the
// substitution is made, and then the whole result is shifted down by one to account for the
// fact that the bound variable has been used up.
export function termSubstTop(s: Term, t: Term): Term {
  return termShift(-1, termSubst(0, termShift(1, s), t));
}

function typeShiftAbove(d: number, c: number, tyT: Type): Type {
  const walk = (c: number, ty: Type): Type => {
    switch (ty._) {
      case "var":
        if (ty.index >= c) {
          return Var(ty.name, ty.index + d);
        } else {
          return Var(ty.name, ty.index);
        }
      case "arrow":
        return Arrow(walk(c, ty.from), walk(c, ty.to));
      case "all":
        return All(ty.name, walk(c + 1, ty.to), ty.kind);
      case "ttabs":
        return TTAbs(ty.name, walk(c + 1, ty.body), ty.kind);
      case "ttapp":
        return TTApp(walk(c, ty.left), walk(c, ty.right));
      case "ref":
        return ty;
    }
  };
  return walk(c, tyT);
}

export function typeSubst(tyS: Type, j: number, tyT: Type): Type {
  const walk = (c: number, t: Type): Type => {
    switch (t._) {
      case "arrow":
        return Arrow(walk(c, t.from), walk(c, t.to));
      case "var":
        return t.index == c ? typeShift(c, tyS) : Var(t.name, t.index);
      case "all":
        return All(t.name, walk(c + 1, t.to), t.kind);
      case "ttabs":
        return TTAbs(t.name, walk(c + 1, t.body), t.kind);
      case "ttapp":
        return TTApp(walk(c, t.left), walk(c, t.right));
      case "ref":
        return t;
    }
  };
  return walk(j, tyT);
}

// Perform the substitution of a type into a term, see E-TappTabs.
export function tytermSubst(tyS: Type, j: number, t: Term): Term {
  const walk = (c: number, t: Term): Term => {
    switch (t._) {
      case "var":
        return Var(t.name, t.index);
      case "lam":
        // We use c+1 in typeSubst so the type may reference this abstraction.
        return Abs(
          t.name,
          walk(c + 1, t.body),
          typeSubst(tyS, c + 1, t.bindType)
        );
      case "app":
        return App(walk(c, t.left), walk(c, t.right));
      case "tabs":
        return TAbs(t.name, walk(c + 1, t.body), t.kind);
      case "tapp":
        return TApp(walk(c, t.left), typeSubst(tyS, c, t.right));
      case "ann":
        throw "not implemented";
      case "ref":
        return Ref(t.name);
    }
  };
  return walk(j, t);
}

// Increment any Var nodes that refer to free variables in the given type.
export function typeShift(d: number, tyT: Type): Type {
  return typeShiftAbove(d, 0, tyT);
}

function tytermSubstTop(tyS: Type, t: Term): Term {
  return termShift(-1, tytermSubst(typeShift(1, tyS), 0, t));
}

export function typeSubstTop(tyS: Type, tyT: Type): Type {
  return typeShift(-1, typeSubst(typeShift(1, tyS), 0, tyT));
}

// Evaluate this term by a single step. When applied to a term that is not yet a value, it yields
// the next step of evaluation for that term. When applied to a value an exception is thrown.
export function reduceOnce(defs: Def[], term: Term): Term {
  switch (term._) {
    case "app":
      if (term.left._ == "lam" && isValue(term.right)) {
        // E-AppAbs
        // (λx:T11.t12)v2 → [x/v2]t12
        let t12 = term.left.body;
        let v2 = term.right;
        return termSubstTop(v2, t12);
      } else if (isValue(term.left)) {
        // E-App2
        return App(term.left, reduceOnce(defs, term.right));
      } else {
        // E-App1
        return App(reduceOnce(defs, term.left), term.right);
      }
    case "tapp":
      if (term.left._ == "tabs") {
        // (ΛX.t12)(T2) → [X/T2]t12    E-TappTabs

        let t11 = term.left.body;
        let tyT2 = term.right;

        return tytermSubstTop(tyT2, t11);
      } else {
        //     t1 → t1'
        // ---------------- E-TApp
        // t1(T2) → t1'(T2)
        let t1 = term.left;
        let tyT2 = term.right;
        let t1p = reduceOnce(defs, t1);
        return TApp(t1p, tyT2);
      }
    case "tabs":
      throw "cannot reduce TAbs";
    case "lam":
      throw "cannot reduce Abs";
    case "var":
      throw "cannot reduce Var";
    case "ann": // ignored at runtime
      return reduceOnce(defs, term.term);
    case "ref":
      const match = defs.filter((d) => d.name == term.name);
      if (match.length == 0) {
        return term;
      }
      return match[0].term;
  }
}

export function erase(term: Term): Erased.Term {
  switch (term._) {
    case "var":
      return Erased.Var(term.name, term.index);
    case "lam":
      return Erased.Abs(term.name, erase(term.body));
    case "app":
      return Erased.App(erase(term.left), erase(term.right));
    case "tabs":
      return erase(term.body);
    case "tapp":
      return erase(term.left);
    case "ann":
      return erase(term.term);
    case "ref":
      return Erased.Ref(term.name);
  }
}

// Shifting renumbers the indices of the free variables in a term.
export function termShift2(d: number, t: Erased.Term): Erased.Term {
  const walk = (d: number, c: number, t: Erased.Term): Erased.Term => {
    if (t._ == "var") {
      let x = t.index;
      if (x >= c) {
        return Var(t.name, x + d);
      } else {
        return Var(t.name, x);
      }
    } else if (t._ == "lam") {
      let t1 = t.body;
      return Erased.Abs(t.name, walk(d, c + 1, t1));
    } else if (t._ == "app") {
      return Erased.App(walk(d, c, t.left), walk(d, c, t.right));
    } else {
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
      case "var": {
        let x = t.index;
        if (x == j + c) {
          // Substitute in the term s, renumbering any free variables so the
          // expression is consistent.
          return termShift2(c, s);
        } else {
          return Erased.Var(t.name, x);
        }
      }
      case "lam": {
        let t1 = t.body;
        return Erased.Abs(t.name, walk(j, s, c + 1, t1));
      }
      case "app": {
        return Erased.App(walk(j, s, c, t.left), walk(j, s, c, t.right));
      }
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
        // E-AppAbs
        // (λx:T11.t12)v2 → [x/v2]t12
        let t12 = term.left.body;
        let v2 = term.right;
        return termSubstTop2(v2, t12);
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
