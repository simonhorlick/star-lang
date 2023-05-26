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
  ASTNode,
  Argument,
  If,
  Hole,
  Ref,
} from "./ast";
import { whnf } from "./equal";
import { pretty, printCtx } from "./pretty";
import { desugarTerm } from "./process";

var _ = require("lodash");

const verbose = true;

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
  dbgCheckIndices(ctx, 0, type);
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
  // For example, if the context is [(A *), (a A@0)] then the returned type
  // for a@0 is A@1, not A@0.
  return shift(index + 1, 0, x.typ);
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
  holes: Array<{ id: number; term: Term }>;
}

export const Result = (
  term: Term,
  type: Term,
  holes: Array<{ id: number; term: Term }>
): Result => ({
  _: "result",
  term: term,
  type: type,
  holes: holes,
});

// infer the type of a term. This produces an annotated version of the term
// whose type can always be checked.
export const infer = (
  defs: Map<string, Def>,
  adts: Map<string, ADT>,
  ctx: Context,
  term: Term,
  os: number,
  oe: number
): Result | TypecheckError => {
  switch (term._) {
    case "pi": {
      // Γ ⊢ A <= ★
      // Γ,x:A ⊢ B <= ★
      // ----------------
      // Γ ⊢ Πx:A. B => ★
      let elA = check(defs, adts, ctx, term.from, Star(), os, oe);
      if (elA._ == "typecheckerror") {
        return elA;
      }
      let elB = check(
        defs,
        adts,
        addTermToCtx(ctx, term.name, term.from),
        term.to,
        Star(),
        os,
        oe
      );
      if (elB._ == "typecheckerror") {
        return elB;
      }
      return Result(
        Pi(term.name, elA.term, elB.term),
        Star(),
        elB.holes.concat(elA.holes)
      );
    }
    case "star":
      // ----------------
      // Γ ⊢ ★ => ★
      return Result(term, Star(), []);
    case "var":
      // Look up its type in the context.
      if (term.index >= ctx.length) {
        return TypecheckError("undefined variable " + term.name, os, oe);
      }
      return Result(term, lookupType(ctx, term.index, term.name), []);
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
      let fType = infer(defs, adts, ctx, f, os, oe);
      if (fType._ == "typecheckerror") {
        return fType;
      }
      let fTypeElaborated = fType.term;
      // TODO: Is this necessary?
      let nf = whnf(true, ctx, defs, fType.type, term);
      if (nf._ == "typecheckerror") {
        return nf;
      }
      if (nf._ != "pi") {
        console.error(pretty(fType.type));
        console.error(pretty(nf));
        return TypecheckError(
          `expected pi type on the left of app; got ${nf._}: ${pretty(nf)}`,
          os,
          oe
        );
      }

      let tyA = nf.from;
      let tyB = nf.to;
      let arg = typecheck(defs, adts, ctx, b, tyA, os, oe);
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
        typ,
        arg.holes.concat(fType.holes)
      );
      // return Result(App(fTypeElaborated, et2), typ);
    }
    case "ann": {
      let typ = check(defs, adts, ctx, term.typ, Star(), os, oe);
      if (typ._ == "typecheckerror") {
        return typ;
      }
      // check the annotated type matches the computed type.
      let ty = typecheck(defs, adts, ctx, term.term, term.typ, os, oe);
      if (ty._ == "typecheckerror") {
        return ty;
      }

      return Result(ty.term, ty.type, typ.holes.concat(ty.holes));
    }
    case "ref":
      const match = defs.get(term.name);
      if (match == undefined) {
        return TypecheckError(
          `reference not found: ${term.name}; ctx is ${printCtx(ctx)}`,
          os,
          oe
        );
      }

      // Without loss of generality we can assume that other definitions
      // typecheck because if we use a definition that later fails to check
      // the compilation will fail with a typecheck error.
      return Result(term, match.typ, []);
    case "orig":
      const tc = infer(defs, adts, ctx, term.child, term.start, term.end);
      if (tc._ == "typecheckerror") {
        return tc;
      }
      return Result(Origin(term.start, term.end, tc.term), tc.type, tc.holes);
    case "int":
      return Result(term, Ref("Nat"), []);
    default:
      return TypecheckError(`cannot infer type of ${term._}`, os, oe);
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
  os: number,
  oe: number
): Result | TypecheckError => {
  if (term._ == "orig") {
    const tc = check(defs, adts, ctx, term.child, type, term.start, term.end);
    if (tc._ == "typecheckerror") {
      return tc;
    }
    return Result(Origin(term.start, term.end, tc.term), tc.type, tc.holes);
  }

  if (verbose) {
    console.log(`check ${pretty(term)} <= ${pretty(type)} in ${printCtx(ctx)}`);
  }

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
          const xTyp = infer(defs, adts, ctx, term.name, os, oe);
          if (xTyp._ == "typecheckerror") {
            return xTyp;
          }
          let ref = strip(xTyp.type);
          if (ref._ == "ref") {
            // ok
          } else if (ref._ == "app") {
            // find the type
            ref = getTypeNameFromTypeConstructor(ref);
          } else {
            return TypecheckError(
              `type of argument to case should be a reference; got ${ref._}`,
              os,
              oe
            );
          }

          // Now look up the constructors for the type.
          const adtDef = adts.get(ref.name);
          if (adtDef == undefined) {
            return TypecheckError(`type not found: ${ref.name}`, os, oe);
          }

          var constructor: Constructor | undefined = undefined;
          const constructorName = identifier(curr.constructor);
          for (const con of adtDef.constructors) {
            if (identifier(con.name) == constructorName) {
              constructor = con;
            }
          }
          if (constructor == undefined) {
            throw `constructor not found: ${constructorName}`;
          }

          // FIXME: Ensure all branches are covered.

          const absArgs = constructor.args.reduceRight(
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

      return check(defs, adts, ctx, desugared, type, os, oe);
    }
    case "self": {
      // What's the type of a self-type?
      if (type._ != "star") {
        return TypecheckError(`expected star type; got ${type._}`, os, oe);
      }
      return Result(term, type, []);
    }
    case "hole": {
      return Result(term, type, []);
    }
    case "lam": {
      // The type of a lambda is a pi, so check this. It might also be an
      // expression that evaluates to a pi type, for example a function
      // application, or a reference, so make sure to normalise that first.
      const normalTy = whnf(true, ctx, defs, type, term);
      if (normalTy._ != "pi") {
        return TypecheckError(
          `expected pi type; got ${type._}: ${pretty(type)}`,
          os,
          oe
        );
      }

      // The domain of the pi type needs to be a type.
      const domain = check(defs, adts, ctx, normalTy.from, Star(), os, oe);
      if (domain._ == "typecheckerror") {
        return domain;
      }

      // We add the bound variable x:A to the context then using that context we
      // check the body has type B.
      let ebody = typecheck(
        defs,
        adts,
        addTermToCtx(ctx, identifier(term.name), normalTy.from),
        term.body,
        normalTy.to,
        os,
        oe
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
      return Result(
        AbsI(term.name, ebody.term),
        type,
        domain.holes.concat(ebody.holes)
      );
    }
  }

  // If there's a type, and one of the other rules doesn't apply, then check
  // the type matches inferred type.
  let ty1 = infer(defs, adts, ctx, term, os, oe);
  if (ty1._ == "typecheckerror") {
    return ty1;
  }
  console.log("inferred " + pretty(ty1.term) + " => " + pretty(ty1.type));

  // TODO: Fill hole from type. Say type=Maybe(Bool) and ty1.type=Maybe(▨0) then
  // we can substitute all ▨0 in ty1 with Bool.
  // let type2 = type;

  // const holes: Array<{ id: number; term: Term }> = [];
  // // match up a hole with a constraint
  // if (type._ == "hole" && ty1.type._ != "hole") {
  //   holes.push({ id: type.id, term: ty1.type });
  // }

  const eq = equate(ctx, defs, term, type, ty1.type, ctx.length);
  if (!eq.eq) {
    return TypecheckError(
      `typecheck failed: ${pretty(type, false)} is not ${pretty(
        ty1.type,
        false
      )}`,
      os,
      oe
    );
  }

  return Result(ty1.term, ty1.type, ty1.holes.concat(eq.holes));
};

export const fill = (chk: Result): Result => {
  // TODO: Do any hole filling now and return the filled subtree.
  let updtm = chk.term;
  let updty = chk.type;

  for (let i = 0; i < chk.holes.length; i++) {
    // If we have a mapping to another hole, i.e. the holes are the same, then
    // give them a consistent id.
    const holetm = chk.holes[i].term;
    if (holetm._ == "hole") {
      for (let j = i + 1; j < chk.holes.length; j++) {
        if (chk.holes[j].id == chk.holes[i].id) {
          chk.holes[j].id = holetm.id;
        }
      }
    }
  }

  for (let i = 0; i < chk.holes.length; i++) {
    const hole = chk.holes[i];
    updtm = substHole(hole.id, hole.term, updtm);
    updty = substHole(hole.id, hole.term, updty);

    // Update any subsequent holes in this list.
    for (let j = i + 1; j < chk.holes.length; j++) {
      chk.holes[j].term = substHole(hole.id, hole.term, chk.holes[j].term);
    }
  }

  return Result(updtm, updty, chk.holes);
};

// check that the given term has the expected type.
export const typecheck = (
  defs: Map<string, Def>,
  adts: Map<string, ADT>,
  ctx: Context,
  tm: Term,
  ty: Term,
  os: number = 0,
  oe: number = 0
): Result | TypecheckError => {
  if (tm._ == "orig") {
    const tc = typecheck(defs, adts, ctx, tm.child, ty, tm.start, tm.end);
    if (tc._ == "typecheckerror") {
      return tc;
    }
    return Result(Origin(tm.start, tm.end, tc.term), tc.type, tc.holes);
  }

  const tynf = whnf(false, ctx, defs, ty, tm);
  if (tynf._ == "typecheckerror") {
    return tynf;
  }

  const chk = check(defs, adts, ctx, tm, tynf, os, oe);
  if (chk._ == "typecheckerror") {
    return chk;
  }

  return fill(chk);
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
    case "if":
      return If(
        shift(d, c, t.condition),
        shift(d, c, t.trueBranch),
        shift(d, c, t.falseBranch)
      );
    case "err":
      throw "unexpected parse error";
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
    case "hole":
    case "int":
    case "str":
      return t;
    case "orig":
      return Origin(t.start, t.end, subst(j, s, c, t.child, name));
    case "case":
      throw "subst: unexpected case";
    case "if":
      throw "subst: unexpected if";
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
      return Pi(t.name, substHole(j, s, t.from), substHole(j, s, t.to));
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
    case "if":
      throw "substHole: unexpected if";
    case "err":
      throw "substHole: unexpected parse error";
  }
}

// aeq returns true if the two terms are alpha-equivalent, i.e. they are the
// same up to renaming of bound variables.
const aeq = (t1: Term, t2: Term): boolean => {
  // ignore origins
  if (t1._ == "orig") {
    return aeq(t1.child, t2);
  }
  if (t2._ == "orig") {
    return aeq(t1, t2.child);
  }

  switch (t1._) {
    case "var":
      return t2._ == "var" && t1.index == t2.index;
    case "lam":
      return t2._ == "lam" && aeq(t1.body, t2.body);
    case "self":
      return t2._ == "self" && aeq(t1.body, t2.body);
    case "app":
      return t2._ == "app" && aeq(t1.left, t2.left) && aeq(t1.right, t2.right);
    case "ann":
      return t2._ == "ann" && aeq(t1.term, t2.term) && aeq(t1.typ, t2.typ);
    case "pi":
      return t2._ == "pi" && aeq(t1.from, t2.from) && aeq(t1.to, t2.to);
    case "par":
      throw "aeq: unexpected par";
    case "star":
      return t2._ == "star";
    case "ref":
      return t2._ == "ref" && t2.name == t1.name;
    case "id":
      return t2._ == "id" && t1.name == t2.name;
    case "hole":
      return t2._ == "hole" && t1.id == t2.id;
    case "case":
      // TODO: Should case statements still exist at this point? Why do they?
      return (
        t2._ == "case" &&
        aeq(t1.name, t2.name) &&
        t1.branches.length == t2.branches.length &&
        // FIXME: This also maintains ordering of the branches - is this what
        // we want?
        t1.branches.every(
          (branch, i) =>
            aeq(branch.constructor, t2.branches[i].constructor) &&
            aeq(branch.term, t2.branches[i].term)
        )
      );
    case "if":
      throw "aeq: unexpected if";
    case "int":
      return t2._ == "int" && t2.num == t1.num;
    case "str":
      return t2._ == "str" && t2.str == t1.str;
    case "err":
      throw "aeq: unexpected parse error";
  }
};

export const equate = (
  ctx: Context,
  defs: Map<string, Def>,
  term: Term,
  ty1: Term,
  ty2: Term,
  depth: number = 0
): { eq: boolean; holes: Array<{ id: number; term: Term }> } => {
  if (aeq(ty1, ty2)) {
    return { eq: true, holes: [] };
  }

  let n1 = whnf(true, ctx, defs, ty1, term);
  let n2 = whnf(true, ctx, defs, ty2, term);
  if (n1._ == "typecheckerror" || n2._ == "typecheckerror") {
    return { eq: false, holes: [] };
  }

  if (verbose) {
    console.log(`equate ${pretty(n1)} == ${pretty(n2)}`);
  }

  if (ty1._ == "app" && ty2._ == "app") {
    const l = equate(ctx, defs, term, ty1.left, ty2.left, depth + 1);
    const r = equate(ctx, defs, term, ty1.right, ty2.right, depth + 1);
    return { eq: l.eq && r.eq, holes: l.holes.concat(r.holes) };
  } else if (n1._ == "lam" && n2._ == "lam") {
    return equate(ctx, defs, term, n1.body, n2.body, depth + 1);
  } else if (n1._ == "self" && n2._ == "self") {
    return equate(ctx, defs, term, n1.body, n2.body, depth + 1);
  } else if (n1._ == "pi" && n2._ == "pi") {
    const l = equate(ctx, defs, term, n1.from, n2.from, depth + 1);
    const r = equate(ctx, defs, term, n1.to, n2.to, depth + 1);
    return { eq: l.eq && r.eq, holes: l.holes.concat(r.holes) };
  } else if (n1._ == "star" && n2._ == "star") {
    return { eq: true, holes: [] };
  } else if (n1._ == "var" && n2._ == "var") {
    return { eq: n1.index == n2.index, holes: [] };
  } else if (n1._ == "hole") {
    // Assume the hole is valid, if it's not the typecheck will fail after the
    // hole substitution.
    return { eq: true, holes: [{ id: n1.id, term: ty2 }] };
  } else if (n2._ == "hole") {
    return { eq: true, holes: [{ id: n2.id, term: ty1 }] };
  } else {
    return { eq: false, holes: [] };
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
    case "hole":
    case "int":
    case "str":
      return t;
    case "case":
      // FIXME: Improve the types here.
      throw "unexpected case at typecheck";
    case "if":
      throw "unexpected if at typecheck";
    case "orig":
      dbgCheckIndices(ctx, depth, t.child);
      return t;
    case "err":
      throw "unexpected parse error";
  }
};

export function stripAST(t: ASTNode): ASTNode {
  switch (t._) {
    case "adt":
      return ADT(
        t.name,
        t.params.map((p) => Argument(p.name, strip(p.type))),
        t.constructors.map((c) =>
          Constructor(
            c.name,
            c.args.map((p) => Argument(p.name, strip(p.type)))
          )
        )
      );
    case "com":
      return t;
    case "def":
      return Def(t.name, strip(t.term), strip(t.typ));
    case "nl":
      return t;
    case "orig2":
      return t.child;
    case "pkg":
      return t;
    case "sp":
      return t;
    case "err":
      return t;
  }
}

export function strip(t: Term): Term {
  switch (t._) {
    case "var":
      return t;
    case "lam":
      return Abs(identifier(t.name), strip(t.body));
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
    case "hole":
    case "int":
    case "str":
    case "err":
      return t;
    case "orig":
      return strip(t.child);
    case "case":
      return Case(
        strip(t.name),
        t.branches.map((b) =>
          Branch(strip(b.constructor) as Identifier, strip(b.term))
        )
      );
    case "if":
      return If(strip(t.condition), strip(t.trueBranch), strip(t.falseBranch));
  }
}

export function serialise(t: Term, d: number = 0): string {
  switch (t._) {
    case "var":
      return `Var(${t.name})`;
    case "lam":
      return `Abs("${identifier(t.name)}", ${serialise(t.body, d + 1)})`;
    case "self":
      return `Self("${t.name}", ${serialise(t.body, d + 1)})`;
    case "app":
      return `App(${serialise(t.left, d + 1)}, ${serialise(t.right, d + 1)})`;
    case "ann":
      return `Ann(${serialise(t.term, d + 1)}, ${serialise(t.typ, d + 1)})`;
    case "pi":
      return `Pi("${t.name}", ${serialise(t.from, d + 1)}, ${serialise(
        t.to,
        d + 1
      )})`;
    case "par":
      return `Par(${t.name})`;
    case "star":
      return `Star`;
    case "ref":
      return `Ref(${t.name})`;
    case "id":
      return `Identifier(${t.name})`;
    case "orig":
      return `Origin(${t.start}, ${t.end}, ${serialise(t.child, d + 1)})`;
    case "case":
      return `Case(${serialise(t.name, d + 1)},[${t.branches
        .map(
          (b) =>
            `Branch(${serialise(b.constructor, d + 1)}, ${serialise(
              b.term,
              d + 1
            )})`
        )
        .join(",")}])`;
    case "if":
      return `If(${serialise(t.condition)}, ${serialise(
        t.trueBranch
      )}, ${serialise(t.falseBranch)})`;
    case "hole":
      return `Hole()`;
    case "int":
      return `${t.num}`;
    case "str":
      return `"${t.str}"`;
    case "err":
      return `ParseError(${t.msg})`;
  }
}

// given an ast of the form App(App(App(X,y),z),w) return the leftmost ref X.
function getTypeNameFromTypeConstructor(t: Term): Ref {
  switch (t._) {
    case "ref":
      return t;
    case "app":
      return getTypeNameFromTypeConstructor(t.left);
    default:
      throw `unexpected ${t._}`;
  }
}
