import {
  Term,
  Type,
  App as AppT,
  Abs as AbsT,
  Var as VarT,
  Ref as RefT,
  Def as DefT,
  Ann as AnnT,
  Arrow as ArrowT,
  TAbs as TAbsT,
  All as AllT,
  Star as StarT,
  TApp as TAppT,
  KArrow as KArrowT,
  TTApp as TTAppT,
  TTAbs as TTAbsT,
  Kind,
} from "./ast";

export function isValue(term: Term): boolean {
  return term._ == "lam" || term._ == "tabs";
}

export const App = (left: Term, right: Term): AppT => ({
  _: "app",
  left: left,
  right: right,
});

export const Ann = (term: Term, type: Type): AnnT => ({
  _: "ann",
  term: term,
  typ: type,
});

export const Abs = (
  name: string,
  body: Term,
  typ: Type = { _: "ers" }
): AbsT => ({
  _: "lam",
  name: name,
  body: body,
  bindType: typ,
});

export const TAbs = (name: string, body: Term, kind: Kind): TAbsT => ({
  _: "tabs",
  name: name,
  body: body,
  kind: kind,
});

export const TApp = (left: Term, right: Type): TAppT => ({
  _: "tapp",
  left: left,
  right: right,
});

export const TTAbs = (name: string, body: Type, kind: Kind): TTAbsT => ({
  _: "ttabs",
  name: name,
  body: body,
  kind: kind,
});

export const TTApp = (left: Type, right: Type): TTAppT => ({
  _: "ttapp",
  left: left,
  right: right,
});

export const Var = (name: string, index: number): VarT => ({
  _: "var",
  name: name,
  index: index,
});

export const Ref = (name: string): RefT => ({
  _: "ref",
  name: name,
});

export const Star = (): StarT => ({
  _: "star",
});

export const KArrow = (from: Kind, to: Kind): KArrowT => ({
  _: "karrow",
  from: from,
  to: to,
});

export const Def = (
  name: string,
  term: Term,
  type: Type = { _: "ers" }
): DefT => ({
  _: "def",
  name: name,
  typ: type,
  term: term,
});

export const Arrow = (from: Type, to: Type): ArrowT => ({
  _: "arrow",
  from: from,
  to: to,
});

export const All = (name: string, to: Type, kind: Kind): AllT => ({
  _: "all",
  to: to,
  name: name,
  kind: kind,
});

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

function termSubstWalk(j: number, s: Term, c: number, t: Term): Term {
  switch (t._) {
    case "var": {
      let x = t.index;
      if (x == j + c) {
        // Substitute in the term s, renumbering any free variables so the
        // expression is consistent.
        return termShift(c, s);
      } else {
        return Var(t.name, x);
      }
    }
    case "lam": {
      let t1 = t.body;
      let ty = t.bindType;
      return Abs(t.name, termSubstWalk(j, s, c + 1, t1), ty);
    }
    case "app": {
      return App(
        termSubstWalk(j, s, c, t.left),
        termSubstWalk(j, s, c, t.right)
      );
    }
    case "tabs": {
      let t1 = t.body;
      return TAbs(t.name, termSubstWalk(j, s, c + 1, t1), t.kind);
    }
    case "tapp":
      return TApp(termSubstWalk(j, s, c, t.left), t.right);
    case "ann":
      return Ann(termSubstWalk(j, s, c, t.term), t.typ);
    case "ref":
      return t;
  }
}

// Given a term t, find all Vars with index j and replace them with the term s.
export function termSubst(j: number, s: Term, t: Term): Term {
  return termSubstWalk(j, s, 0, t);
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
      case "var": {
        let x = ty.index;
        if (x >= c) {
          return Var(ty.name, x + d);
        } else {
          return Var(ty.name, x);
        }
      }
      case "arrow": {
        let tyT1 = ty.from;
        let tyT2 = ty.to;
        return Arrow(walk(c, tyT1), walk(c, tyT2));
      }
      case "all": {
        let tyX = ty.name;
        let tyT2 = ty.to;
        return All(tyX, walk(c + 1, tyT2), ty.kind);
      }
      case "ers":
        return ty;
      case "ref":
        return ty;
      case "ttabs": {
        let tyX = ty.name;
        let tyT2 = ty.body;
        return TTAbs(tyX, walk(c + 1, tyT2), ty.kind);
      }
      case "ttapp":
        return TTApp(walk(c, ty.left), walk(c, ty.right));
    }
  };
  return walk(c, tyT);
}

function tmmap(
  onvar: (name: string, index: number) => Term,
  ontype: (c: number, bindType: Type) => Type,
  c: number,
  t: Term
): Term {
  const walk = (c: number, t: Term): Term => {
    switch (t._) {
      case "var":
        return onvar(t.name, t.index);
      case "lam":
        // Here we use ontype(c + 1) so the type may reference this abstraction.
        return Abs(t.name, walk(c + 1, t.body), ontype(c + 1, t.bindType));
      case "app":
        return App(walk(c, t.left), walk(c, t.right));
      case "tabs":
        return TAbs(t.name, walk(c + 1, t.body), t.kind);
      case "tapp":
        return TApp(walk(c, t.left), ontype(c, t.right));
      case "ann":
        throw "not implemented";
      //  return Ann(t.term, t.typ);
      case "ref":
        return Ref(t.name);
    }
  };
  return walk(c, t);
}

function tymap(
  onvar: (name: string, j: number, index: number) => Type,
  c: number,
  tyT: Type
): Type {
  const walk = (c: number, tyT: Type): Type => {
    switch (tyT._) {
      case "arrow":
        return Arrow(walk(c, tyT.from), walk(c, tyT.to));
      case "var":
        return onvar(tyT.name, c, tyT.index);
      case "all": {
        let tyX = tyT.name;
        let tyT2 = tyT.to;
        return All(tyX, walk(c + 1, tyT2), tyT.kind);
      }
      case "ref":
        return tyT;
      case "ers":
        return tyT;
      case "ttabs": {
        let tyX = tyT.name;
        let tyT2 = tyT.body;
        return TTAbs(tyX, walk(c + 1, tyT2), tyT.kind);
      }
      case "ttapp":
        return TTApp(walk(c, tyT.left), walk(c, tyT.right));
    }
  };
  return walk(c, tyT);
}

export function typeSubst(tyS: Type, j: number, tyT: Type): Type {
  return tymap(
    (name: string, j: number, x: number) =>
      x == j ? typeShift(j, tyS) : Var(name, x),
    j,
    tyT
  );
}

export function tytermSubst(tyS: Type, j: number, t: Term): Term {
  return tmmap(
    (name, index) => Var(name, index),
    (j, tyT) => typeSubst(tyS, j, tyT),
    j,
    t
  );
}

// Increment any Var nodes that refer to free variables in the given type.
export function typeShift(d: number, tyT: Type): Type {
  return typeShiftAbove(d, 0, tyT);
}

function tytermSubstTop(tyS: Type, t: Term): Term {
  return termShift(-1, tytermSubst(typeShift(1, tyS), 0, t));
}

export function typeSubstTop(tyS, tyT): Type {
  return typeShift(-1, typeSubst(typeShift(1, tyS), 0, tyT));
}

// Evaluate this term by a single step. When applied to a term that is not yet a value, it yields
// the next step of evaluation for that term. When applied to a value an exception is thrown.
export function reduceOnce(defs: DefT[], term: Term): Term {
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
