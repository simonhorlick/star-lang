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
} from "./ast";
import { pretty, printCtx } from "./pretty";

var _ = require("lodash");

export const typeEq = (A: Type, B: Type) => _.isEqual(A, B);

export const addTermToCtx = (
  ctx: Context,
  name: string,
  type: Type
): Context => [...ctx, { type: "bind", name: name, typ: type }];

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

type TypecheckError = {
  _: "typecheckerror";
  msg: string;
};

const TypecheckError = (msg: string): TypecheckError => ({
  _: "typecheckerror",
  msg: msg,
});

interface Result {
  _: "result";
  term: Term;
  type: Type;
}

const Result = (term: Term, type: Term): Result => ({
  _: "result",
  term: term,
  type: type,
});

// infer the type of a term. This produces an annotated version of the term
// whose type can always be checked.
export const infer = (
  defs: Def[],
  ctx: Context,
  term: Term
): Result | TypecheckError => tc(defs, ctx, term);

// check that the given term has the expected type.
export const check = (
  defs: Def[],
  ctx: Context,
  tm: Term,
  ty: Term
): Result | TypecheckError => {
  let nf = whnf(true, defs, ty);
  switch (nf._) {
    case "ann":
      return check(defs, ctx, tm, nf.term);
    default:
      return tc(defs, ctx, tm, nf);
  }
};

// Make sure that the term is a "type" (i.e. that it has type 'Type')
export const checkStar = (
  defs: Def[],
  ctx: Context,
  term: Term
): Result | TypecheckError => tc(defs, ctx, term, Star());

// check a term, producing an elaborated term where all of the type annotations
// have been filled in. The second argument is undefined in inference mode and
// an expected type (must be in whnf) in checking mode.
export const tc = (
  defs: Def[],
  ctx: Context,
  term: Term,
  type?: Term // this is undefined in inference mode.
): Result | TypecheckError => {
  const printIndices = false;
  if (type) {
    // checking mode
    console.log(
      `Γ=[${printCtx(ctx, printIndices)}] checking \n${pretty(
        term,
        printIndices
      )} <= ${pretty(type, printIndices)}`
    );
  } else {
    // inference mode
    console.log(
      `Γ=[${printCtx(ctx, printIndices)}] inferring type for \n${pretty(
        term,
        printIndices
      )}`
    );
  }

  dbgCheckIndices(ctx, 0, term);

  // inference mode
  if (type == undefined) {
    switch (term._) {
      case "self": {
        throw "self term";
      }
      case "pi": {
        // Γ ⊢ A <= ★
        // Γ,x:A ⊢ B <= ★
        // ----------------
        // Γ ⊢ Πx:A. B => ★
        let elA = check(defs, ctx, term.from, Star());
        if (elA._ == "typecheckerror") {
          return elA;
        }
        let elB = check(
          defs,
          addTermToCtx(ctx, term.name, term.from),
          term.to,
          Star()
        );
        if (elB._ == "typecheckerror") {
          return elB;
        }
        console.log(`inferred type is ${pretty(Star(), printIndices)}`);
        return Result(Pi(term.name, elA.term, elB.term), Star());
      }
      case "star":
        // ----------------
        // Γ ⊢ ★ => ★
        console.log(`inferred type is ${pretty(Star(), printIndices)}`);
        return Result(Star(), Star());
      case "var":
        // Look up its type in the context.
        if (term.index >= ctx.length) {
          return TypecheckError("undefined variable " + term.name);
        }
        console.log(
          `inferred type is ${pretty(
            lookupType(ctx, term.index, term.name),
            printIndices
          )}`
        );
        return Result(term, lookupType(ctx, term.index, term.name));
      case "lam": {
        // Γ,x:A ⊢ a <= B
        // ----------------
        // Γ ⊢ λx.a <= Πx:A. B

        // infer the type of a lambda expression, when an annotation on the
        // binder is present
        if (term.argtype == undefined) {
          return TypecheckError("lambda requires annotation");
        }
        let atyA = checkStar(defs, ctx, term.argtype);
        if (atyA._ == "typecheckerror") {
          return atyA;
        }
        // infer the type of the body of the lambda expression
        let inferred = infer(
          defs,
          addTermToCtx(ctx, term.name, atyA.term),
          term.body
        );
        if (inferred._ == "typecheckerror") {
          return inferred;
        }
        let ebody = inferred.term;
        let atyB = inferred.type;
        console.log(
          `inferred type is ${pretty(
            Pi(term.name, atyA.term, atyB),
            printIndices
          )}`
        );

        return Result(
          Abs(term.name, ebody, term.argtype),
          Pi(term.name, atyA.term, atyB)
        );
      }
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
        let fType = infer(defs, ctx, f);
        if (fType._ == "typecheckerror") {
          return fType;
        }
        let fTypeElaborated = fType.term;
        let nf = ensurePi(defs, fType.type);
        if (nf._ == "typecheckerror") {
          return nf;
        }
        let tyA = nf.from;
        let tyB = nf.to;
        let arg = check(defs, ctx, b, tyA);
        if (arg._ == "typecheckerror") {
          return arg;
        }
        let et2 = arg.term;
        console.log(`inferred type is ${pretty(tyB, printIndices)}`);
        // Substitute the argument in the pi type with the elaborated argument to
        // the app inside of tyB.
        let typ = substTop(et2, tyB, nf.name);
        console.log(`subst type is ${pretty(typ, printIndices)}`);

        return Result(App(fTypeElaborated, et2), typ);
      }
      case "ann": {
        let typ = checkStar(defs, ctx, term.typ);
        if (typ._ == "typecheckerror") {
          return typ;
        }
        // check the annotated type matches the computed type.
        let ty = check(defs, ctx, term.term, term.typ);
        if (ty._ == "typecheckerror") {
          return ty;
        }

        console.log(`inferred type is ${pretty(ty.type, printIndices)}`);

        return Result(ty.term, ty.type);
      }
      case "ref":
        const match = defs.filter((d) => d.name == term.name);
        if (match.length == 0) {
          return TypecheckError(`reference not found: ${term.name}`);
        }
        console.log(`inferred type is ${pretty(match[0].typ, printIndices)}`);

        // FIXME: Don't repeat this work if the term has already been checked.
        return check(defs, ctx, match[0].term, match[0].typ);
    }
  } else {
    dbgCheckIndices(ctx, 0, type);

    if (type._ == "self") {
      // Γ ⊢ t:[t/x]T
      // ------------ selfGen
      // Γ ⊢ t:ιx.T
      //
      // Γ ⊢ t:ιx.T
      // ------------ selfInst
      // Γ ⊢ t:[t/x]T

      // In the current type, replace any references to the self type by the
      // value being typed.
      return check(defs, ctx, term, substTop(term, type.body, type.name));
    }

    switch (term._) {
      case "self": {
        throw "self term";
      }

      case "lam":
        // Γ,x:A ⊢ a <= B
        // ----------------
        // Γ ⊢ λx.a <= Πx:A. B

        // checking mode.
        if (type._ != "pi") {
          return TypecheckError(`expected pi type; got ${type._}`);
        }

        if (term.argtype) {
          if (!equate(defs, term, type.from, term.argtype)) {
            return TypecheckError("annotation on binder doesn't match pi type");
          }
        }

        // we add the bound variable x:A to the context (assuming that x has type
        // A) then using that context we check the body has type B.
        let ebody = check(
          defs,
          addTermToCtx(ctx, term.name, shift(1, 0, type.from)),
          term.body,
          type.to
        );
        if (ebody._ == "typecheckerror") {
          return ebody;
        }
        return Result(
          Abs(term.name, Ann(ebody.term, ebody.type), term.argtype),
          type
        );
    }

    // If there's a type, and one of the other rules doesn't apply, then check
    // the type matches inferred type.
    let ty1 = infer(defs, ctx, term);
    if (ty1._ == "typecheckerror") {
      return ty1;
    }
    console.log(
      `Γ=[${printCtx(ctx, printIndices)}] inferred\n\t${pretty(
        ty1.type,
        printIndices
      )};\nchecking it matches\n\t${pretty(type, printIndices)}`
    );

    if (!equate(defs, term, type, ty1.type)) {
      return TypecheckError(
        `typecheck failed: \n\t${pretty(
          type,
          printIndices
        )}\nis not\n\t${pretty(ty1.type, printIndices)}`
      );
    }
    return Result(term, ty1.type);
  }
};

// Shifting renumbers the indices of the free variables in a term.
export function shift(d: number, c: number, t: Term): Term {
  // If the variable index is greater than the cutoff, c, then adjust the index
  // by d.
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
    case "star":
    case "ref":
      return t;
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

// export function isValue(term: Term): boolean {
//   return term._ == "lam";
// }

// // Big-step evaluation for the given term.
// export function evaluate(defs: Def[], term: Term): Term {
//   switch (term._) {
//     case "app":
//       let e1 = evaluate(defs, term.left);
//       let e2 = evaluate(defs, term.right);
//       if (e1._ == "lam" && isValue(e2)) {
//         return substTop(e2, e1.body);
//       }
//       return App(e1, e2);
//     case "lam":
//       return term;
//     // throw "cannot reduce Abs";
//     case "var":
//       throw "cannot reduce Var";
//     case "ann": // ignored at runtime
//       return evaluate(defs, term.term);
//     case "ref":
//       const match = defs.filter((d) => d.name == term.name);
//       if (match.length == 0) {
//         return term;
//       }
//       return evaluate(defs, match[0].term);
//     case "pi":
//       throw "can't eval pi";
//     case "star":
//       throw "can't eval star";
//   }
// }

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
  t1: Term,
  t2: Term
): boolean => {
  if (aeq(t1, t2)) {
    return true;
  }

  let n1 = whnf(true, defs, t1);
  let n2 = whnf(true, defs, t2);

  switch (n1._) {
    case "app":
      if (n2._ != "app") return false;
      let a1 = n1.left;
      let a2 = n1.right;
      let b1 = n2.left;
      let b2 = n2.right;
      return equate(defs, term, a1, b1) && equate(defs, term, a2, b2);
    case "lam":
      if (n2._ != "lam") return false;
      return equate(defs, term, n1.body, n2.body);
    case "self":
      if (n2._ != "self") return false;
      return equate(defs, term, n1.body, n2.body);
    case "pi":
      if (n2._ != "pi") return false;
      return (
        equate(defs, term, n1.from, n2.from) && equate(defs, term, n1.to, n2.to)
      );
    case "ref":
      if (n2._ == "ref" && n1.name == n2.name) return true;
      // FIXME: When does this happen?
      throw "failed to equate ref";
    case "star":
      return n2._ == "star";
    case "var":
      return n2._ == "var" && n1.index == n2.index;
    case "ann":
      // TODO: Make this impossible using proper types.
      throw "internal checker error: unexpected Ann in whnf term";
  }
};

// Compute the weak head normal form for a term.
export const whnf = (unfold: boolean, defs: Def[], t: Term): Term => {
  switch (t._) {
    case "ref":
      if (!unfold) return t;
      const match = defs.filter((d) => d.name == t.name);
      if (match.length == 0) {
        throw `reference not found: ${t.name}`;
      }
      return whnf(false, defs, match[0].term);
    case "app": {
      let t1 = t.left;
      let t2 = t.right;
      let nf = whnf(unfold, defs, t1);
      if (nf._ == "lam") {
        let body = nf.body;
        return whnf(unfold, defs, substTop(t2, body, nf.name));
      }
      return App(nf, t2);
    }
    case "ann":
      // TODO: Just ignore the Ann?
      throw "unexpected Ann";
    case "var":
    case "lam":
    case "self":
    case "pi":
    case "star":
      return t;
  }
};

// Ensure that ty reduces to a Pi type and return it.
function ensurePi(defs: Def[], ty: Term): Pi | TypecheckError {
  const nf = whnf(true, defs, ty);
  if (nf._ != "pi") {
    return TypecheckError(
      `expected pi type on the left of app; got ${nf._}: ${pretty(nf)}`
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
      return t;
  }
};
