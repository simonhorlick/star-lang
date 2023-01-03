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
  All as AllT,
  Star as StarT,
} from "./ast";

export function isValue(term: Term): boolean {
  // FIXME: I'm not sure if Var should be considered a value. In the book it
  // isn't.
  return term._ == "lam"; // || term._ == "var";
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

export const All = (name: string, body: Term): AllT => ({
  _: "all",
  name: name,
  body: body,
});

export const Var = (
  name: string,
  index: number,
  contextLength: number = -1
): VarT => ({
  _: "var",
  name: name,
  index: index,
  contextLength: contextLength,
});

export const Ref = (name: string): RefT => ({
  _: "ref",
  name: name,
});

export const Star = (): StarT => ({
  _: "star",
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

// The shifting function below takes a “cutoff” parameter c that controls which variables should
// be shifted.
function walk(d: number, c: number, t: Term): Term {
  if (t._ == "var") {
    let n = t.contextLength;
    let x = t.index;
    if (x >= c) {
      return Var(t.name, x + d, n + d);
    } else {
      return Var(t.name, x, n + d);
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
}

// shifting (6.2.1)
function termShift(d: number, t: Term): Term {
  return walk(d, 0, t);
}

function termSubstWalk(j: number, s: Term, c: number, t: Term): Term {
  if (t._ == "var") {
    let n = t.contextLength;
    let x = t.index;
    if (x == j + c) {
      return termShift(c, s);
    } else {
      return Var(t.name, x, n);
    }
  } else if (t._ == "lam") {
    let t1 = t.body;
    let ty = t.bindType;
    return Abs(t.name, termSubstWalk(j, s, c + 1, t1), ty);
  } else if (t._ == "app") {
    return App(termSubstWalk(j, s, c, t.left), termSubstWalk(j, s, c, t.right));
  } else {
    return t;
  }
}

// The substitution [j -> s]t of term s for the variable numbered j in term t.
function termSubst(j: number, s: Term, t: Term): Term {
  return termSubstWalk(j, s, 0, t);
}

// The term being substituted for the bound variable is first shifted up by one, then the
// substitution is made, and then the whole result is shifted down by one to account for the
// fact that the bound variable has been used up.
function termSubstTop(s: Term, t: Term): Term {
  return termShift(-1, termSubst(0, termShift(1, s), t));
}

// Evaluate this term by a single step. When applied to a term that is not yet a value, it yields
// the next step of evaluation for that term. When applied to a value an exception is thrown.
export function reduceOnce(defs: DefT[], term: Term): Term {
  switch (term._) {
    case "app":
      if (term.left._ == "lam" && isValue(term.right)) {
        // E-AppAbs
        let t12 = term.left.body;
        let v2 = term.right;
        return termSubstTop(v2, t12);
      } else if (term.left._ == "all" && isValue(term.right)) {
        // TODO: E-TAppTAbs
        throw "not implemented";
      } else if (isValue(term.left)) {
        // E-App2
        return App(term.left, reduceOnce(defs, term.right));
      } else {
        // E-App1
        return App(reduceOnce(defs, term.left), term.right);
      }
    case "all":
      throw "cannot reduce All";
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
