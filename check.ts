// check implements a typechecker for this language
import {
  Context,
  Term,
  Type,
  App,
  Abs,
  Var,
  Ann,
  Pi,
  Def,
  Star,
  Self,
  Case,
  Branch,
  Origin,
  Normal,
} from "./ast";
import { pretty, printCtx } from "./pretty";

var _ = require("lodash");

export const logFull = (x: any) => {
  const util = require("util");
  console.log(
    util.inspect(x, { showHidden: false, depth: null, colors: true })
  );
};

export const typeEq = (A: Type, B: Type) => _.isEqual(A, B);

export const ctxContains = (name: string, ctx: Context) =>
  ctx.find((b) => b.name == name) != undefined;

export const addTermToCtx = (
  ctx: Context,
  name: string,
  type: Type
): Context => {
  if (name != "" && name != "P" && ctxContains(name, ctx)) {
    console.log(
      `warning: variable ${name} shadows existing variable; context is ${printCtx(
        ctx
      )}`
    );
  }
  return [...ctx, { type: "bind", name: name, typ: type }];
};

export const lookupType = (
  ctx: Context,
  index: number,
  name: string | undefined = undefined
): Type => {
  if (index >= ctx.length) {
    throw `variable ${name} not found in context`;
  }
  let x = ctx[ctx.length - index - 1];
  // For debugging - this can only happen if the wrong index is used in a
  // hand-crafted expression.
  if (name && x.name != name) {
    throw `name mismatch: got ${name}; expected ${x.name}`;
  }
  // Shift the indices referenced in this type to take into account the actual
  // context length. When this type was added to the context all variables are
  // offset from 0, but when looking up the entry in position i, the absolute
  // offsets of all variables in this entry are offset by i.
  return shift(index, 0, x.typ);
};

export type TypecheckError = {
  _: "typecheckerror";
  msg: string;
  start: number;
  end: number;
};

export const TypecheckError = (
  msg: string,
  start: number,
  end: number
): TypecheckError => ({
  _: "typecheckerror",
  msg: msg,
  start: start,
  end: end,
});

export interface Result {
  _: "result";
  term: Term;
  type: Type;
}

export const Result = (term: Term, type: Term): Result => ({
  _: "result",
  term: term,
  type: type,
});

// infer the type of a term. This produces an annotated version of the term
// whose type can always be checked.
export const infer = (
  defs: Def[],
  ctx: Context,
  term: Term,
  originStart: number = 0,
  originEnd: number = 0
): Result | TypecheckError => {
  switch (term._) {
    case "pi": {
      // Γ ⊢ A <= ★
      // Γ,x:A ⊢ B <= ★
      // ----------------
      // Γ ⊢ Πx:A. B => ★
      let elA = check(defs, ctx, term.from, Star(), originStart, originEnd);
      if (elA._ == "typecheckerror") {
        return elA;
      }
      let elB = check(
        defs,
        addTermToCtx(ctx, term.name, term.from),
        term.to,
        Star(),
        originStart,
        originEnd
      );
      if (elB._ == "typecheckerror") {
        return elB;
      }
      return Result(Pi(term.name, elA.term, elB.term), Star());
    }
    case "star":
      // ----------------
      // Γ ⊢ ★ => ★
      return Result(term, Star());
    case "var":
      // Look up its type in the context.
      if (term.index >= ctx.length) {
        return TypecheckError(
          "undefined variable " + term.name,
          originStart,
          originEnd
        );
      }
      return Result(term, lookupType(ctx, term.index, term.name));
    case "app": {
      // We must infer the type of the function f, but once we have that type, we may
      // to use it to check the type of the argument:
      //
      // Γ ⊢ f => (x:A) -> B
      // Γ ⊢ b <= A
      // ------------------- app
      // Γ ⊢ f(b) => B[b/x]

      let f = term.left;
      let b = term.right;
      let fType = infer(defs, ctx, f, originStart, originEnd);
      if (fType._ == "typecheckerror") {
        return fType;
      }
      let fTypeElaborated = fType.term;
      let nf = ensurePi(defs, term, fType.type, originStart, originEnd);
      if (nf._ == "typecheckerror") {
        return nf;
      }
      let tyA = nf.from;
      let tyB = nf.to;
      let arg = typecheck(defs, ctx, b, tyA, originStart, originEnd);
      if (arg._ == "typecheckerror") {
        return arg;
      }
      let et2 = arg.term;
      // Substitute the argument in the pi type with the elaborated argument to
      // the app inside of tyB.
      let typ = substTop(et2, tyB, nf.name);

      console.log(
        `Γ ⊢ ${pretty(f)} => ${pretty(fType.type)}
Γ ⊢ ${pretty(b)} <= ${pretty(tyA)}
------------------- app
Γ ⊢ ${pretty(term)} => ${pretty(typ)}`
      );

      return Result(App(fTypeElaborated, et2), typ);
    }
    case "ann": {
      let typ = check(defs, ctx, term.typ, Star(), originStart, originEnd);
      if (typ._ == "typecheckerror") {
        return typ;
      }
      // check the annotated type matches the computed type.
      let ty = typecheck(
        defs,
        ctx,
        term.term,
        term.typ,
        originStart,
        originEnd
      );
      if (ty._ == "typecheckerror") {
        return ty;
      }

      return Result(ty.term, ty.type);
    }
    case "ref":
      const match = defs.filter((d) => d.name == term.name);
      if (match.length == 0) {
        return TypecheckError(
          `reference not found: ${term.name}; ctx is ${printCtx(ctx)}`,
          originStart,
          originEnd
        );
      }

      // Without loss of generality we can assume that other definitions
      // typecheck because if we use a definition that later fails to check
      // the compilation will fail with a typecheck error.
      return Result(term, match[0].typ);
    default:
      return TypecheckError(
        `cannot infer type of ${term._}`,
        originStart,
        originEnd
      );
  }
};

// check a term has the given type, producing an elaborated term where all of the type annotations
// have been filled in. The type argument must be in whnf in checking mode.
const check = (
  defs: Def[],
  ctx: Context,
  term: Term,
  type: Normal,
  originStart: number,
  originEnd: number
): Result | TypecheckError => {
  if (term._ == "case") {
    throw "unexpected case";
  }

  if (term._ == "orig") {
    return check(defs, ctx, term.child, type, term.start, term.end);
  }

  if (type._ == "ann") {
    return typecheck(defs, ctx, term, type.term, originStart, originEnd);
  }

  console.log(`${" ".repeat(ctx.length)} ctx ${printCtx(ctx)}`);
  console.log(
    `${" ".repeat(ctx.length)} checking ${pretty(term)} has type ${pretty(
      type
    )}`
  );

  // TODO: When adding a variable to the context, ensure it doesn't shadow an
  // existing variable.

  switch (term._) {
    case "self": {
      // What's the type of a self-type?
      if (type._ != "star") {
        return TypecheckError(
          `expected star type; got ${type._}`,
          originStart,
          originEnd
        );
      }
      return Result(term, type);
    }
    case "lam":
      // Γ,x:A ⊢ a <= B
      // ----------------
      // Γ ⊢ λx.a <= Πx:A. B
      if (type._ != "pi") {
        return TypecheckError(
          `expected pi type; got ${type._}`,
          originStart,
          originEnd
        );
      }

      // we add the bound variable x:A to the context (assuming that x has type
      // A) then using that context we check the body has type B.
      let ebody = typecheck(
        defs,
        addTermToCtx(ctx, term.name, shift(1, 0, type.from)),
        term.body,
        type.to,
        originStart,
        originEnd
      );
      if (ebody._ == "typecheckerror") {
        return ebody;
      }
      return Result(Abs(term.name, Ann(ebody.term, ebody.type)), type);
  }

  // If there's a type, and one of the other rules doesn't apply, then check
  // the type matches inferred type.
  let ty1 = infer(defs, ctx, term, originStart, originEnd);
  if (ty1._ == "typecheckerror") {
    return ty1;
  }

  if (!equate(defs, term, type, ty1.type, ctx.length)) {
    return TypecheckError(
      `typecheck failed: \n\t${pretty(type, false)}\nis not\n\t${pretty(
        ty1.type,
        false
      )}`,
      originStart,
      originEnd
    );
  }

  return Result(term, ty1.type);
};

// check that the given term has the expected type.
export const typecheck = (
  defs: Def[],
  ctx: Context,
  tm: Term,
  ty: Term,
  originStart: number = 0,
  originEnd: number = 0
): Result | TypecheckError => {
  const tmnf = whnf(true, defs, tm, undefined);
  const tynf = whnf(true, defs, ty, tm);
  if (tynf._ == "typecheckerror") {
    return tynf;
  }
  if (tmnf._ == "typecheckerror") {
    return tmnf;
  }
  return check(defs, ctx, tmnf, tynf, originStart, originEnd);
};

// Shifting renumbers the indices of the free variables in a term.
// If the variable index is greater than the cutoff, c, then adjust the index
// by d.
export function shift(d: number, c: number, t: Term): Term {
  switch (t._) {
    case "var":
      return t.index >= c ? Var(t.name, t.index + d) : t;
    case "lam":
      return Abs(t.name, shift(d, c + 1, t.body));
    case "self":
      return Self(t.name, shift(d, c + 1, t.body));
    case "app":
      return App(shift(d, c, t.left), shift(d, c, t.right));
    case "ann":
      return Ann(shift(d, c, t.term), t.typ);
    case "pi":
      return Pi(t.name, shift(d, c, t.from), shift(d, c + 1, t.to));
    case "star":
    case "ref":
    case "par":
      return t;
    case "orig":
      return shift(d, c, t.child);
    case "case":
      throw "shift: unexpected case";
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
      return Abs(t.name, subst(j, s, c + 1, t.body, name));
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
        subst(j, s, c + 1, t.to, name)
      );
    case "par":
      throw "subst: unexpected par";
    case "star":
    case "ref":
      return t;
    case "orig":
      return Origin(t.start, t.end, subst(j, s, c, t.child, name));
    case "case":
      throw "subst: unexpected case";
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

// aeq returns true if the two terms are alpha-equivalent, i.e. they are the
// same up to renaming of bound variables.
const aeq = (t1: Term, t2: Term): boolean => {
  // FIXME: This isn't really correct because the name fields (used for
  // debugging) would collide.
  return _.isEqual(t1, t2);
};

export const equate = (
  defs: Def[],
  term: Term,
  ty1: Term,
  ty2: Term,
  depth: number = 0
): boolean => {
  console.log(`${" ".repeat(depth)}equate ${pretty(ty1)} == ${pretty(ty2)}`);
  if (aeq(ty1, ty2)) {
    return true;
  }

  const bothref = ty1._ == "ref" && ty2._ == "ref";

  let n1 = whnf(!bothref, defs, ty1, term);
  let n2 = whnf(!bothref, defs, ty2, term);
  if (n1._ == "typecheckerror" || n2._ == "typecheckerror") return false;

  console.log(`${" ".repeat(depth)}equate ${pretty(n1)} == ${pretty(n2)}`);

  if (n1._ == "app" && n2._ == "app") {
    let a1 = n1.left;
    let a2 = n1.right;
    let b1 = n2.left;
    let b2 = n2.right;
    return (
      equate(defs, term, a1, b1, depth + 1) &&
      equate(defs, term, a2, b2, depth + 1)
    );
  } else if (n1._ == "lam" && n2._ == "lam") {
    return equate(defs, term, n1.body, n2.body, depth + 1);
  } else if (n1._ == "self" && n2._ == "self") {
    return equate(defs, term, n1.body, n2.body, depth + 1);
  } else if (n1._ == "pi" && n2._ == "pi") {
    return (
      equate(defs, term, n1.from, n2.from, depth + 1) &&
      equate(defs, term, n1.to, n2.to, depth + 1)
    );
  } else if (n1._ == "ref" && n2._ == "ref") {
    return n1.name == n2.name;
  } else if (n1._ == "star" && n2._ == "star") {
    return true;
  } else if (n1._ == "var" && n2._ == "var") {
    return n1.index == n2.index;
  } else {
    return false;
  }
};

// Compute the weak head normal form for a term.
export const whnf = (
  unfold: boolean,
  defs: Def[],
  t: Term,
  selfTerm: Term | undefined
): Normal | TypecheckError => {
  switch (t._) {
    case "ref":
      if (!unfold) return t;
      const match = defs.filter((d) => d.name == t.name);
      if (match.length == 0) {
        return TypecheckError(`whnf: reference not found: ${t.name}`, 0, 0);
      }
      return whnf(false, defs, match[0].term, selfTerm);
    case "app": {
      let nf = whnf(unfold, defs, t.left, selfTerm);
      if (nf._ == "typecheckerror") {
        return nf;
      }
      if (nf._ == "lam") {
        return whnf(
          unfold,
          defs,
          substTop(t.right, nf.body, nf.name),
          selfTerm
        );
      }
      return App(nf, t.right);
    }
    case "ann":
      return whnf(unfold, defs, t.term, selfTerm);
    case "par":
      throw "whnf: unexpected Par";
    case "self":
      // eliminate self
      if (selfTerm == undefined) {
        // This can happen if we're checking a type definition, i.e. Nat:*.
        const nf = whnf(unfold, defs, t.body, selfTerm);
        if (nf._ == "typecheckerror") {
          return nf;
        }
        return Self(t.name, nf);
      }
      return whnf(unfold, defs, substTop(selfTerm, t.body, t.name), selfTerm);
    case "var":
    case "lam":
    case "pi":
    case "star":
      return t;
    case "case":
      throw "whnf: unexpected case";
    case "orig": // remove origins
      return whnf(unfold, defs, t.child, selfTerm);
  }
};

// Ensure that ty reduces to a Pi type and return it.
function ensurePi(
  defs: Def[],
  tm: Term,
  ty: Term,
  originStart: number,
  originEnd: number
): Pi | TypecheckError {
  let nf = whnf(true, defs, ty, tm);
  if (nf._ == "typecheckerror") {
    return nf;
  }
  if (nf._ != "pi") {
    return TypecheckError(
      `expected pi type on the left of app; got ${nf._}: ${pretty(nf)}`,
      originStart,
      originEnd
    );
  }
  return nf;
}

export const dbgCheckIndices = <T extends Term>(
  ctx: Context,
  depth: number,
  t: T
): T => {
  // check the names of Var terms match what's in the context.
  switch (t._) {
    case "var":
      lookupType(ctx, t.index, t.name);
      return t;
    case "lam":
      dbgCheckIndices(addTermToCtx(ctx, t.name, Star()), depth + 1, t.body);
      return t;
    case "self":
      dbgCheckIndices(addTermToCtx(ctx, t.name, Star()), depth + 1, t.body);
      return t;
    case "app":
      dbgCheckIndices(ctx, depth, t.left);
      dbgCheckIndices(ctx, depth, t.right);
      return t;
    case "ann":
      dbgCheckIndices(ctx, depth, t.term);
      dbgCheckIndices(ctx, depth, t.typ);
      return t;
    case "pi":
      dbgCheckIndices(ctx, depth, t.from);
      dbgCheckIndices(addTermToCtx(ctx, t.name, Star()), depth + 1, t.to);
      return t;
    case "star":
    case "ref":
    case "par":
      return t;
    case "case":
      // FIXME: Improve the types here.
      throw "unexpected case at typecheck";
    case "orig":
      dbgCheckIndices(ctx, depth, t.child);
      return t;
  }
};
