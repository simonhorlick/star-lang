import { Term, Def, Type } from "./ast";

export function isValue(term: Term): boolean {
  return term.type == "lam";
}

const App = (left: Term, right: Term): Term => ({
  type: "app",
  left: left,
  right: right,
});

const Abs = (name: string, body: Term, typ: Type): Term => ({
  type: "lam",
  name: name,
  body: body,
  typ: typ,
});

const Var = (name: string, index: number, contextLength: number): Term => ({
  type: "var",
  name: name,
  index: index,
  contextLength: contextLength,
});

// The shifting function below takes a “cutoff” parameter c that controls which variables should
// be shifted.
function walk(d: number, c: number, t: Term): Term {
  if (t.type == "var") {
    let n = t.contextLength!;
    let x = t.index!;
    if (x >= c) {
      return Var(t.name, x + d, n + d);
    } else {
      return Var(t.name, x, n + d);
    }
  } else if (t.type == "lam") {
    let t1 = t.body;
    let ty = t.typ;
    return Abs(t.name, walk(d, c + 1, t1), ty);
  } else if (t.type == "app") {
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
  if (t.type == "var") {
    let n = t.contextLength;
    let x = t.index;
    if (x == j + c) {
      return termShift(c, s);
    } else {
      return Var(t.name, x, n);
    }
  } else if (t.type == "lam") {
    let t1 = t.body;
    let ty = t.typ;
    return Abs(t.name, termSubstWalk(j, s, c + 1, t1), ty);
  } else if (t.type == "app") {
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

// reduce takes a term and reduces it to normal form.
export function reduceOnce(defs: Def[], term: Term): Term {
  if (term.type == "app") {
    if (term.left.type == "lam" && isValue(term.right)) {
      // E-AppAbs
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
  } else if (term.type == "lam") {
    throw "cannot reduce Abs";
  } else {
    const match = defs.filter((d) => d.name == term.name);
    if (match.length == 0) {
      return term;
    }
    return match[0].term;
  }
}
