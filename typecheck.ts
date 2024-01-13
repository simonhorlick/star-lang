// typecheck.ts implements a simple bidirectional typechecker for this language
//
// The typechecker is split into two based on the term being checked. Some
// terms, like lambdas, must be checked against a specified type. Others, like
// applications can be inferred by looking up their definition.
//
import {
  Term,
  Type,
  App,
  Ann,
  Pi,
  Def,
  Star,
  Origin,
  ADT,
  Ref,
  identifier2str as id,
  IntLit,
  Var,
  Self,
  Hole,
} from "./ast";
import { reduce } from "./equal";
import { pretty, printCtx } from "./pretty";
import { Context, addTermToCtx as cons, lookupType } from "./context";
import { substHole, substTop } from "./substitution";
import { StringLit } from "./erased";

const verbose = true;

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

// infer the type of a term
export const infer = (
  defs: Map<string, Def>,
  adts: Map<string, ADT>,
  ctx: Context,
  term: Term,
  os: number,
  oe: number
): Result => {
  switch (term._) {
    case "var": {
      // Look up its type in the context.
      if (term.index >= ctx.length) {
        throw TypecheckError("undefined variable " + term.name, os, oe);
      }
      return Result(term, lookupType(ctx, term.index, term.name), []);
    }
    case "pi": {
      // The domain of the pi needs to be a type.
      let d = check(defs, adts, ctx, term.from, Star(), os, oe);

      let c = check(
        defs,
        adts,
        cons(ctx, term.name, term.from),
        term.body,
        Star(),
        os,
        oe
      );

      // The type of a pi is ★.
      return Result(term, Star(), d.holes.concat(c.holes));
    }
    case "star": {
      // ----------------
      // Γ ⊢ ★ => ★
      return Result(term, Star(), []);
    }
    case "app": {
      // We must infer the type of the function f, but once we have that type,
      // we may to use it to check the type of the argument:
      //
      // Γ ⊢ f => (x:A) -> B
      // Γ ⊢ b <= A
      // ------------------- app
      // Γ ⊢ f(b) => B[b/x]
      const inf = infer(defs, adts, ctx, term.func, os, oe);
      const funcTyp = reduce(true, ctx, defs, inf.type);

      // can be self
      const funcTyp2 =
        funcTyp._ == "self"
          ? substTop(term.func, funcTyp.body, funcTyp.name)
          : funcTyp;

      if (funcTyp2._ != "pi") {
        throw TypecheckError(
          `expected function got ${pretty(funcTyp2)}`,
          os,
          oe
        );
      }
      // Check the type of the argument.
      const arg = check(defs, adts, ctx, term.arg, funcTyp2.from, os, oe);

      // substitute the argument into the pi to get the type.
      let typ = substTop(arg.term, funcTyp2.body, funcTyp2.name);

      console.log(`Γ ⊢ ${pretty(term.func)} => ${pretty(funcTyp2)}`);
      console.log(`Γ ⊢ ${pretty(term.arg)} <= ${pretty(funcTyp2.from)}`);
      console.log(`------------------- app`);
      console.log(`Γ ⊢ ${pretty(term)} => ${pretty(typ)}`);

      return Result(term, typ, arg.holes.concat(inf.holes));
    }
    case "ann": {
      // Check the annotation is actually a type.
      const typ = check(defs, adts, ctx, term.typ, Star(), os, oe);
      // Check the annotated type matches the computed type.
      const c = check(defs, adts, ctx, term.term, term.typ, os, oe);
      return Result(term, c.type, typ.holes.concat(c.holes));
    }
    case "ref": {
      const match = defs.get(term.name);
      if (match == undefined) {
        throw TypecheckError(
          `reference not found: ${term.name}; ctx is ${printCtx(ctx)}`,
          os,
          oe
        );
      }
      return Result(match.term.term, match.term.typ, []);
    }
    case "self": {
      // Add the value being typed to the context (i.e. self-typing) and check the body has the correct type.
      let c = check(
        defs,
        adts,
        cons(ctx, term.name, term),
        term.body,
        Star(),
        os,
        oe
      );

      return Result(term, Star(), c.holes);
    }
    case "orig": {
      return infer(defs, adts, ctx, term.child, term.start, term.end);
    }
    case "int": {
      return Result(term, Ref("Nat"), []);
    }
    case "str": {
      return Result(term, Ref("String"), []);
    }
    default: {
      throw `infer: ${term._} ${pretty(term)} is not inferrable`;
    }
  }
};

// check the term val has the type typ.
const check = (
  defs: Map<string, Def>,
  adts: Map<string, ADT>,
  ctx: Context,
  val: Term,
  tty: Term,
  os: number,
  oe: number
): Result => {
  if (val._ == "orig") {
    return check(defs, adts, ctx, val.child, tty, val.start, val.end);
  }

  const pval = pretty(val);
  const ptty = pretty(tty);
  console.log(`ch ${pval}`);
  console.log(`<= ${ptty}`);

  var typ = reduce(true, ctx, defs, tty);

  // If an expression has a self-type then the term we're checking must be
  // substituted into the type before we can continue.
  typ = typ._ == "self" ? substTop(val, typ.body, typ.name) : typ;

  if (val._ == "lam") {
    // Lambdas must be checked against a supplied pi type.
    //
    // Γ,x:A ⊢ a <= B
    // Γ ⊢ A <= *
    // ---------------------- lambda
    // Γ ⊢ λx.a <= (x:A) -> B

    if (typ._ != "pi") {
      throw `lam must have pi type; got ${pretty(typ)}`;
    }

    // We add the bound variable x:A to the context then using that context we
    // check the body has type B.
    let c = check(
      defs,
      adts,
      cons(ctx, id(val.name), typ.from),
      val.body,
      typ.body,
      os,
      oe
    );

    return Result(val, typ, c.holes);
  } else if (val._ == "hole") {
    // Holes always check against their desired types.
    return Result(val, tty, []);
  } else {
    // infer the type of the term and check this matches the supplied type.
    var ii = infer(defs, adts, ctx, val, os, oe);
    var inf = reduce(true, ctx, defs, ii.type);
    var inf = inf._ == "self" ? substTop(val, inf.body, inf.name) : inf;
    const eq = equate(ctx, defs, inf, typ);
    if (!eq.eq) {
      const ptyp = pretty(tty);
      const pinf = pretty(ii.type);
      throw TypecheckError(`typecheck failed: ${ptyp} is not ${pinf}`, os, oe);
    }
    return Result(val, typ, ii.holes.concat(eq.holes));
  }
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
): Result => {
  if (tm._ == "orig") {
    const tc = typecheck(defs, adts, ctx, tm.child, ty, tm.start, tm.end);
    return Result(Origin(tm.start, tm.end, tc.term), tc.type, tc.holes);
  }

  const chk = check(defs, adts, ctx, tm, ty, os, oe);

  return fill(chk);
};

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
      return t2._ == "app" && aeq(t1.func, t2.func) && aeq(t1.arg, t2.arg);
    case "ann":
      return t2._ == "ann" && aeq(t1.term, t2.term) && aeq(t1.typ, t2.typ);
    case "pi":
      return t2._ == "pi" && aeq(t1.from, t2.from) && aeq(t1.body, t2.body);
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
    case "let":
      throw "let not implemented";
    // return t2._ == "let" && aeq(t1.expr, t2.expr) && aeq(t1.body, t2.body);
    case "if":
      throw "aeq: unexpected if";
    case "int":
      return t2._ == "int" && t2.num == t1.num;
    case "str":
      return t2._ == "str" && t2.str == t1.str;
    case "err":
      // throw "aeq: unexpected parse error";
      return true;
    case "rel":
      throw "aeq: unexpected rel";
  }
};

export const equate = (
  ctx: Context,
  defs: Map<string, Def>,
  ty1: Term,
  ty2: Term,
  depth: number = 0
): { eq: boolean; holes: Array<{ id: number; term: Term }> } => {
  if (aeq(ty1, ty2)) {
    return { eq: true, holes: [] };
  }

  const lhs = pretty(ty1);
  const rhs = pretty(ty2);
  if (verbose) {
    console.log(`eq ${lhs}`);
    console.log(`== ${rhs}`);
  }

  if (depth > 1000) {
    throw "equate depth exceeds limit";
  }

  if (ty1._ == "app" && ty2._ == "app") {
    const l = equate(ctx, defs, ty1.func, ty2.func, depth + 1);
    const r = equate(ctx, defs, ty1.arg, ty2.arg, depth + 1);
    return { eq: l.eq && r.eq, holes: l.holes.concat(r.holes) };
  } else if (ty1._ == "lam" && ty2._ == "lam") {
    return equate(ctx, defs, ty1.body, ty2.body, depth + 1);
  } else if (ty1._ == "self" && ty2._ == "self") {
    return equate(ctx, defs, ty1.body, ty2.body, depth + 1);
  } else if (ty1._ == "pi" && ty2._ == "pi") {
    const l = equate(ctx, defs, ty1.from, ty2.from, depth + 1);
    const r = equate(ctx, defs, ty1.body, ty2.body, depth + 1);
    return { eq: l.eq && r.eq, holes: l.holes.concat(r.holes) };
  } else if (ty1._ == "star" && ty2._ == "star") {
    return { eq: true, holes: [] };
  } else if (ty1._ == "var" && ty2._ == "var") {
    return { eq: ty1.index == ty2.index, holes: [] };
  } else if (ty1._ == "hole") {
    // Assume the hole is valid, if it's not the typecheck will fail after the
    // hole substitution.
    return { eq: true, holes: [{ id: ty1.id, term: ty2 }] };
  } else if (ty2._ == "hole") {
    return { eq: true, holes: [{ id: ty2.id, term: ty1 }] };
  } else {
    const n1 = reduce(true, ctx, defs, ty1);
    if (n1 !== ty1) {
      return equate(ctx, defs, n1, ty2, depth + 1);
    }

    const n2 = reduce(true, ctx, defs, ty2);
    if (n2 !== ty2) {
      return equate(ctx, defs, ty1, n2, depth + 1);
    }

    return { eq: false, holes: [] };
  }
};

export const defs = (defs: Def[] = []): Map<string, Def> => {
  const m = new Map<string, Def>();
  for (const d of defs) {
    m.set(d.name, d);
  }
  return m;
};

export const adts = (adts: ADT[] = []): Map<string, ADT> => {
  const m = new Map<string, ADT>();
  for (const adt of adts) {
    m.set(id(adt.name), adt);
  }
  return m;
};
