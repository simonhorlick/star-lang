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
  Constructor,
  ADT,
  Identifier,
  AbsI,
} from "./ast";
import { pretty, printCtx } from "./pretty";
import { desugarTerm } from "./process";

var _ = require("lodash");

const verbose = false;

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
  defs: Map<string, Def>,
  adts: Map<string, ADT>,
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
      let elA = check(
        defs,
        adts,
        ctx,
        term.from,
        Star(),
        originStart,
        originEnd
      );
      if (elA._ == "typecheckerror") {
        return elA;
      }
      let elB = check(
        defs,
        adts,
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
      let fType = infer(defs, adts, ctx, f, originStart, originEnd);
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
      let arg = typecheck(defs, adts, ctx, b, tyA, originStart, originEnd);
      if (arg._ == "typecheckerror") {
        return arg;
      }
      let et2 = arg.term;
      // Substitute the argument in the pi type with the elaborated argument to
      // the app inside of tyB.
      let typ = substTop(et2, tyB, nf.name);

      if (verbose)
        console.log(
          `Γ ⊢ ${pretty(f)} => ${pretty(fType.type)}
Γ ⊢ ${pretty(b)} <= ${pretty(tyA)}
------------------- app
Γ ⊢ ${pretty(term)} => ${pretty(typ)}`
        );

      // After inferring the type of f we need to return it as an annotation so
      // that further stages can use it.

      return Result(
        App(Ann(fTypeElaborated, fType.type), Ann(et2, arg.type)),
        typ
      );
      // return Result(App(fTypeElaborated, et2), typ);
    }
    case "ann": {
      let typ = check(
        defs,
        adts,
        ctx,
        term.typ,
        Star(),
        originStart,
        originEnd
      );
      if (typ._ == "typecheckerror") {
        return typ;
      }
      // check the annotated type matches the computed type.
      let ty = typecheck(
        defs,
        adts,
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
      const match = defs.get(term.name);
      if (match == undefined) {
        return TypecheckError(
          `reference not found: ${term.name}; ctx is ${printCtx(ctx)}`,
          originStart,
          originEnd
        );
      }

      // Without loss of generality we can assume that other definitions
      // typecheck because if we use a definition that later fails to check
      // the compilation will fail with a typecheck error.
      return Result(term, match.typ);
    case "orig":
      const tc = infer(defs, adts, ctx, term.child, term.start, term.end);
      if (tc._ == "typecheckerror") {
        return tc;
      }
      return Result(Origin(term.start, term.end, tc.term), tc.type);
    default:
      return TypecheckError(
        `cannot infer type of ${term._}`,
        originStart,
        originEnd
      );
  }
};

// check a term has the given type, producing an elaborated term where all of
// the type annotations have been filled in. The type argument must be in weak
// head normal form.
const check = (
  defs: Map<string, Def>,
  adts: Map<string, ADT>,
  ctx: Context,
  term: Term,
  type: Normal,
  originStart: number,
  originEnd: number
): Result | TypecheckError => {
  if (term._ == "orig") {
    const tc = check(defs, adts, ctx, term.child, type, term.start, term.end);
    if (tc._ == "typecheckerror") {
      return tc;
    }
    return Result(Origin(term.start, term.end, tc.term), tc.type);
  }

  if (verbose) console.log(`${" ".repeat(ctx.length)} ctx=${printCtx(ctx)}`);
  if (verbose)
    console.log(
      `${" ".repeat(ctx.length)} checking ${pretty(term)} has type ${pretty(
        type
      )}`
    );

  // TODO: When adding a variable to the context, ensure it doesn't shadow an
  // existing variable.

  switch (term._) {
    case "case": {
      // the type of an App is
      // Γ ⊢ f => Πx:A. B
      // Γ ⊢ b <= A
      // ------------------- app
      // Γ ⊢ f(b) => B[b/x]
      //
      // We should be able to construct this App node and infer it's type then
      // check the type is equivalent. But what's P? Can we take the expected
      // type and use it?
      //
      //  case x of
      //    c1 -> t1
      //    c2 -> t2
      // desugars to:
      //  x(() MotiveType, t1, t2)
      //
      // When we desugar a case we need to create abstractions for all of the
      // arguments in each branch, for example, assume x is a Nat:
      // case x of
      //  zero -> true
      //  succ -> false
      // we need to desugar the second branch to be
      //  Abs("x.n", Ref("false"))

      const P = Abs("", shift(1, 0, type)); // P just returns the expected type
      const branches = term.branches.reduce<Term | TypecheckError>(
        (acc: Term | TypecheckError, curr) => {
          const branchTerm = curr.term;

          if (acc._ == "typecheckerror") {
            return acc;
          }

          // Make any constructor arguments available using dot notation.

          // We need to infer the type of x; this *must* be done as part of
          // the typechecking phase.
          const xTyp = infer(
            defs,
            adts,
            ctx,
            term.name,
            originStart,
            originEnd
          );
          if (xTyp._ == "typecheckerror") {
            return xTyp;
          }
          const ref = strip(xTyp.type);
          if (ref._ != "ref") {
            return TypecheckError(
              `type of argument to case should be a reference; got ${ref._}`,
              originStart,
              originEnd
            );
          }

          // Now look up the constructors for the type.
          const adtDef = adts.get(ref.name);
          if (adtDef == undefined) {
            return TypecheckError(
              `type not found: ${ref.name}`,
              originStart,
              originEnd
            );
          }

          var constructor: Constructor | undefined = undefined;
          for (const con of adtDef.constructors) {
            if (identifier(con.name) == curr.constructor) {
              constructor = con;
            }
          }
          if (constructor == undefined) {
            throw `constructor not found: ${curr.constructor}`;
          }

          // FIXME: Ensure all branches are covered.

          const absArgs = constructor.args.reduce(
            (acc2, curr2) => Abs(`${pretty(term.name)}.${curr2.name}`, acc2),
            shift(constructor.args.length, 0, branchTerm)
          );

          return App(acc, absArgs);
        },
        App(term.name, P) as Term
      );

      if (branches._ == "typecheckerror") {
        return branches;
      }

      // desugarTerm ensures any Refs that reference constructor arguments
      // are converted into Vars.
      const desugared = desugarTerm(branches, undefined, adts, ctx);

      if (verbose) console.log(printCtx(ctx) + " " + pretty(desugared, true));

      return check(defs, adts, ctx, desugared, type, originStart, originEnd);
    }
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
      const pi = ensurePi(defs, term, type, originStart, originEnd);
      if (pi._ == "typecheckerror") {
        return pi;
      }

      // we add the bound variable x:A to the context (assuming that x has type
      // A) then using that context we check the body has type B.
      let ebody = typecheck(
        defs,
        adts,
        addTermToCtx(ctx, identifier(term.name), shift(1, 0, pi.from)),
        term.body,
        pi.to,
        originStart,
        originEnd
      );
      if (ebody._ == "typecheckerror") {
        return ebody;
      }
      // // Annotate the body of the abstraction with the checked type.
      // const etype = whnf(false, defs, ebody.type, undefined);
      // if (etype._ == "typecheckerror") {
      //   return etype;
      // }
      // const b = Ann(ebody.term, etype);

      // We return the elaborated body here - as case statements must be
      // desugared for any consumers.
      return Result(AbsI(term.name, ebody.term), type);

    // return Result(
    //   Ann(Abs(term.name, ebody.term), Pi(pi.name, pi.from, etype)),
    //   pi
    // );
  }

  // If there's a type, and one of the other rules doesn't apply, then check
  // the type matches inferred type.
  let ty1 = infer(defs, adts, ctx, term, originStart, originEnd);
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

  return Result(ty1.term, ty1.type);
};

// check that the given term has the expected type.
export const typecheck = (
  defs: Map<string, Def>,
  adts: Map<string, ADT>,
  ctx: Context,
  tm: Term,
  ty: Term,
  originStart: number = 0,
  originEnd: number = 0
): Result | TypecheckError => {
  if (tm._ == "orig") {
    const tc = typecheck(defs, adts, ctx, tm.child, ty, tm.start, tm.end);
    if (tc._ == "typecheckerror") {
      return tc;
    }
    return Result(Origin(tm.start, tm.end, tc.term), tc.type);
  }

  if (verbose) console.log(`${" ".repeat(ctx.length)} ctx=${printCtx(ctx)}`);
  if (verbose)
    console.log(
      `${" ".repeat(ctx.length)} typecheck ${pretty(tm)} has type ${pretty(ty)}`
    );

  const tmnf = tm; //whnf(true, defs, tm, undefined);
  const tynf = whnf(false, defs, ty, tm);
  if (tynf._ == "typecheckerror") {
    return tynf;
  }
  // if (tmnf._ == "typecheckerror") {
  //   return tmnf;
  // }
  return check(defs, adts, ctx, tmnf, tynf, originStart, originEnd);
};

// Shifting renumbers the indices of the free variables in a term.
// If the variable index is greater than the cutoff, c, then adjust the index
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
      return Pi(t.name, shift(d, c, t.from), shift(d, c + 1, t.to));
    case "star":
    case "ref":
    case "par":
    case "id":
      return t;
    case "orig":
      return Origin(t.start, t.end, shift(d, c, t.child));
    case "case":
      return Case(
        shift(d, c, t.name),
        t.branches.map((b) => Branch(b.constructor, shift(d, c, b.term))) // TODO: Is this correct? Do we need to shift here?
      );
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
        subst(j, s, c + 1, t.to, name)
      );
    case "par":
      throw "subst: unexpected par";
    case "star":
    case "ref":
    case "id":
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
  defs: Map<string, Def>,
  term: Term,
  ty1: Term,
  ty2: Term,
  depth: number = 0
): boolean => {
  if (verbose)
    console.log(`${" ".repeat(depth)}equate ${pretty(ty1)} == ${pretty(ty2)}`);
  if (aeq(ty1, ty2)) {
    return true;
  }

  const bothref = ty1._ == "ref" && ty2._ == "ref";

  let n1 = whnf(!bothref, defs, ty1, term);
  let n2 = whnf(!bothref, defs, ty2, term);
  if (n1._ == "typecheckerror" || n2._ == "typecheckerror") return false;

  if (verbose)
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

export const identifier = (id: Term): string => {
  switch (id._) {
    case "id":
      return id.name;
    case "orig":
      return identifier(id.child);
    default:
      throw `expected identifier; got ${id._}`;
  }
};

// Compute the weak head normal form for a term.
export const whnf = (
  unfold: boolean,
  defs: Map<string, Def>,
  t: Term,
  selfTerm: Term | undefined
): Normal | TypecheckError => {
  switch (t._) {
    case "ref":
      if (!unfold) return t;
      const match = defs.get(t.name);
      if (match == undefined) {
        return TypecheckError(`whnf: reference not found: ${t.name}`, 0, 0);
      }
      return whnf(false, defs, match.term, selfTerm);
    case "app": {
      let nf = whnf(unfold, defs, t.left, selfTerm);
      if (nf._ == "typecheckerror") {
        return nf;
      }
      if (nf._ == "lam") {
        return whnf(
          unfold,
          defs,
          substTop(t.right, nf.body, identifier(nf.name)),
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
    case "id":
      return t;
    case "case":
      return t;
    //throw "whnf: unexpected case";
    case "orig": // remove origins
      return whnf(unfold, defs, t.child, selfTerm);
  }
};

// Ensure that ty reduces to a Pi type and return it.
export function ensurePi(
  defs: Map<string, Def>,
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

export const dbgCheckIndices = (ctx: Context, depth: number, t: Term): Term => {
  // check the names of Var terms match what's in the context.
  switch (t._) {
    case "var":
      lookupType(ctx, t.index, t.name);
      return t;
    case "lam":
      dbgCheckIndices(
        addTermToCtx(ctx, identifier(t.name), Star()),
        depth + 1,
        t.body
      );
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
    case "id":
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

export function strip(t: Term): Term {
  switch (t._) {
    case "var":
      return t;
    case "lam":
      return AbsI(t.name, strip(t.body));
    case "self":
      return Self(t.name, strip(t.body));
    case "app":
      return App(strip(t.left), strip(t.right));
    case "ann":
      return Ann(strip(t.term), strip(t.typ));
    case "pi":
      return Pi(t.name, strip(t.from), strip(t.to));
    case "par":
    case "star":
    case "ref":
    case "id":
      return t;
    case "orig":
      return strip(t.child);
    case "case":
      return Case(
        strip(t.name),
        t.branches.map((b) => Branch(b.constructor, strip(b.term)))
      );
  }
}

export function serialise(t: Term, d: number = 0): string {
  const pd = "  ".repeat(d);
  switch (t._) {
    case "var":
      return `${pd}Var(${t.name})`;
    case "lam":
      return `${pd}Abs("${t.name}", \n${serialise(t.body, d + 1)}\n${pd})`;
    case "self":
      return `${pd}Self("${t.name}", \n${serialise(t.body, d + 1)}\n${pd})`;
    case "app":
      return `${pd}App(\n${serialise(t.left, d + 1)}, \n${serialise(
        t.right,
        d + 1
      )}\n${pd})`;
    case "ann":
      return `${pd}Ann(\n${serialise(t.term, d + 1)}, \n${serialise(
        t.typ,
        d + 1
      )}\n${pd})`;
    case "pi":
      return `${pd}Pi("${t.name}", \n${serialise(t.from, d + 1)}, \n${serialise(
        t.to,
        d + 1
      )}\n${pd})`;
    case "par":
      return `${pd}Par(${t.name})`;
    case "star":
      return `${pd}Star`;
    case "ref":
      return `${pd}Ref(${t.name})`;
    case "id":
      return `${pd}Identifier(${t.name})`;
    case "orig":
      return `${pd}Origin(${t.start}, ${t.end}, \n${serialise(
        t.child,
        d + 1
      )}\n${pd})`;
    case "case":
      return `${pd}Case(
        ${serialise(t.name, d + 1)},
        [${t.branches
          .map((b) => `Branch(${b.constructor}, ${serialise(b.term, d + 1)})`)
          .join(",")}]
      )`;
  }
}
