import { Term, Def } from "./ast";

export function isValue(term: Term): boolean {
  return term.type != "app";
}

// The shifting function below takes a “cutoff” parameter c that controls which variables should
// be shifted.
function walk(d: number, c: number, t: Term): Term {
  if (t.type == "ref") {
    let n = t.contextLength!;
    let x = t.index!;
    if (x >= c) {
      return {
        type: "ref",
        name: t.name,
        index: x + d,
        contextLength: n + d,
      };
    } else {
      return {
        type: "ref",
        name: t.name,
        index: x,
        contextLength: n + d,
      };
    }
  } else if (t.type == "lam") {
    let t1 = t.body;
    let ty = t.typ;
    return {
      type: "lam",
      name: t.name,
      body: walk(d, c + 1, t1),
      typ: ty,
    };
  } /*if (t.type == "app")*/ else {
    return {
      type: "app",
      left: walk(d, c, t.left),
      right: walk(d, c, t.right),
    };
  }
}

// shifting (6.2.1)
function termShift(d: number, t: Term): Term {
  return walk(d, 0, t);
}

function termSubstWalk(j: number, s: Term, c: number, t: Term): Term {
  if (t.type == "ref") {
    let n = t.contextLength;
    let x = t.index;
    if (x == j + c) {
      return termShift(c, s);
    } else {
      return {
        type: "ref",
        name: t.name,
        index: x,
        contextLength: n,
      };
    }
  } else if (t.type == "lam") {
    let t1 = t.body;
    let ty = t.typ;
    return {
      type: "lam",
      name: t.name,
      body: termSubstWalk(j, s, c + 1, t1),
      typ: ty,
    };
  } /*if (t.type == "app")*/ else {
    return {
      type: "app",
      left: termSubstWalk(j, s, c, t.left),
      right: termSubstWalk(j, s, c, t.right),
    };
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
export function reduceOnce(ctx: Def[], term: Term): Term {
  if (term.type == "app") {
    if (term.left.type == "lam" && isValue(term.right)) {
      let t12 = term.left.body;
      let v2 = term.right;
      return termSubstTop(v2, t12);
    } else if (isValue(term.left)) {
      return {
        type: "app",
        left: term.left,
        right: reduceOnce(ctx, term.right),
      };
    } else {
      return {
        type: "app",
        left: reduceOnce(ctx, term.left),
        right: term.right,
      };
    }
  } else if (term.type == "lam") {
    console.log("cannot reduce Abs");
    return {
      type: "ref",
      name: "__not_found__",
      index: undefined,
      contextLength: undefined,
    };
  } else {
    console.log("cannot reduce Ref");
    return {
      type: "ref",
      name: "__not_found__",
      index: undefined,
      contextLength: undefined,
    };
  }
}
