// typecheck.ts implements a simple bidirectional typechecker for this language
//
// The typechecker is split into two based on the term being checked. Some
// terms, like lambdas, must be checked against a specified type. Others, like
// applications can be inferred by looking up their definition.
//
import {
  Star,
  Ref,
  App,
  Ann,
  AbsI,
  Pi,
  Abs,
  Origin,
  Syntax,
  Hole,
  Case,
  Label,
  CTerm,
  strip,
  fixupRefs,
  Branch,
  Self,
  Let,
  ParseError,
} from "./sugar";
import { reduce } from "./equal";
import { pretty, printCtx } from "./pretty";
import { Context, addTermToCtx as cons, lookupType } from "./context";
import { shift, substHole, substTop } from "./substitution";
import { Set } from "immutable";
import { ADT, Argument, Constructor, Def, Def2 } from "./ast";
import { identifier2str } from "./pratt";

import { createLogger } from "./logger";

const logger = createLogger("typecheck");

type Term = CTerm;
type Type = CTerm;

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

// Helper function to create a better error message when a polymorphic constructor
// is missing type arguments.
const makeMissingTypeArgError = (val: Term, infType: Type): string | null => {
  // Check if the inferred type is a Pi type starting with a type parameter (ΠA:★ ...)
  // This indicates a polymorphic constructor
  if (infType._ === "pi" && infType.from._ === "star" && val._ === "ref") {
    // Extract the constructor name
    const constructorName = val.name;

    return `missing type argument to polymorphic constructor '${constructorName}'. This constructor requires a type parameter`;
  }

  return null;
};

// infer the type of a term
export const infer = (
  defs: Map<string, Def2>,
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

      logger.debug(`Γ ⊢ ${pretty(term.func)} => ${pretty(funcTyp2)}`);
      logger.debug(`Γ ⊢ ${pretty(term.arg)} <= ${pretty(funcTyp2.from)}`);
      logger.debug(`------------------- app`);
      logger.debug(`Γ ⊢ ${pretty(term)} => ${pretty(typ)}`);

      return Result(App(inf.term, arg.term), typ, arg.holes.concat(inf.holes));
    }
    case "ann": {
      // Check the annotation is actually a type.
      const typ = check(defs, adts, ctx, term.type, Star(), os, oe);
      // Check the annotated type matches the computed type.
      const c = check(defs, adts, ctx, term.term, term.type, os, oe);
      // Return the desugared term.
      return Result(Ann(c.term, c.type), c.type, typ.holes.concat(c.holes));
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
      // Do we need to return the looked up ref? Or can this be done in reduce?
      return Result(term, match.term.type, []);
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
      const x = infer(defs, adts, ctx, term.child, term.start, term.end);
      return Result(Origin(term.start, term.end, x.term), x.type, x.holes);
    }
    case "syn": {
      return infer(defs, adts, ctx, term.child, os, oe);
    }
    case "label": {
      return infer(defs, adts, ctx, term.child, os, oe);
    }
    case "int": {
      return Result(term, Ref("Nat"), []);
    }
    case "str": {
      return Result(term, Ref("String"), []);
    }
    case "case": {
      // TODO:
      throw "TODO";
    }
    case "err": {
      // Sometimes it's necessary to infer the type of an error node. This can
      // happen as part of the case desugaring. In this case we return a hole
      // and attempt to fill it.
      return Result(term, Hole(Math.random()), []);
    }
    default: {
      throw TypecheckError(
        `infer: ${term._} ${pretty(term)} is not inferrable`,
        os,
        oe
      );
    }
  }
};

const checkTree = (init: Term, defs: Map<string, Def2>): void => {
  const ct = (t: CTerm): void => {
    switch (t._) {
      case "app":
        ct(t.func);
        ct(t.arg);
        break;
      case "lam":
        ct(t.name);
        ct(t.body);
        break;
      case "ann":
        ct(t.term);
        ct(t.type);
        break;
      case "case":
        ct(t.name);
        t.branches.forEach((b) => {
          ct(b.constructor);
          ct(b.term);
        });
        break;
      case "let":
        ct(t.name);
        ct(t.expr);
        ct(t.body);
        break;
      case "orig":
        ct(t.child);
        break;
      case "syn":
        ct(t.child);
        break;
      case "pi":
        ct(t.from);
        ct(t.body);
        break;
      case "label":
        ct(t.child);
        break;
      case "self":
        ct(t.body);
        break;

      // Leaf terms
      case "id":
      case "key":
      case "int":
      case "hole":
      case "err":
      case "star":
      case "str":
      case "var":
        break;

      case "ref":
        if (!defs.has(t.name)) {
          throw new Error(`undefined reference: ${t.name}`);
        }
        break;
      default:
        throw new Error(`unexpected term in checkTree`);
    }
  };
  ct(init);
};

// check the term val has the type typ.
export const check = (
  defs: Map<string, Def2>,
  adts: Map<string, ADT>,
  ctx: Context,
  val: Term,
  tty: Term,
  os: number = 0,
  oe: number = 0
): Result => {
  // Keep origins and syntax nodes for inspection.
  if (val._ == "orig") {
    const x = check(defs, adts, ctx, val.child, tty, val.start, val.end);
    return Result(Origin(val.start, val.end, x.term), x.type, x.holes);
  } else if (val._ == "syn") {
    const x = check(defs, adts, ctx, val.child, tty, os, oe);
    return Result(Syntax(val.syntax, x.term), x.type, x.holes);
  } else if (val._ == "label") {
    const x = check(defs, adts, ctx, val.child, tty, os, oe);
    return Result(Label(val.label, x.term), x.type, x.holes);
  }

  // debug check
  try {
    checkTree(tty, defs);
  } catch (e) {
    console.error(`debug check failed: ${e}`);
    console.error(`tty: ${pretty(tty)}`);
  }

  const pval = pretty(val);
  const ptty = pretty(tty);
  const pctx = printCtx(ctx);
  logger.debug(`cx ${pctx}`);
  logger.debug(`ch ${pval}`);
  logger.debug(`<= ${ptty}`);

  // Desugar let expressions.
  if (val._ == "let") {
    // A let statement desugars to a lambda. For example:
    //
    //   let x = t1 in expr  ~>  (λx:T1 expr)(t1)
    //
    // The typechecker requires all lambdas to be annotated with a pi-type so
    // we infer the type of x and annotate the lambda with the type T1->typ
    // and check if it fits.

    const expressionType = infer(defs, adts, ctx, val.expr, os, oe);

    const desugared = App(
      Ann(AbsI(val.name, val.body), Pi("", expressionType.type, tty)),
      val.expr
    );

    return check(defs, adts, ctx, desugared, tty, os, oe);
  }

  // Desugar case expressions.
  if (val._ == "case") {
    return desugarCaseStatement(defs, adts, ctx, val, os, oe, tty);
  }

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
      throw TypecheckError(`lam must have pi type; got ${pretty(typ)}`, os, oe);
    }

    // We add the bound variable x:A to the context then using that context we
    // check the body has type B.
    let c = check(
      defs,
      adts,
      cons(ctx, identifier2str(val.name), typ.from),
      val.body,
      typ.body,
      os,
      oe
    );

    // Return the desugared term. If the lambda body was a case statement then
    // we need to return the desugared version.
    // Annotate the AST with the type of the lambda. This is so the tooling has
    // access to these types for inspection.
    const annotated = Ann(AbsI(val.name, c.term), Pi("", typ.from, c.type));
    return Result(annotated, tty, c.holes);
  } else if (val._ == "hole") {
    // Holes always check against their desired types.
    return Result(val, tty, []);
  } else if (val._ == "err") {
    // Parse errors always check against their desired types.
    return Result(Ann(val, tty), tty, []);
  } else if (val._ == "ref") {
    // For references, check if they exist before inferring their type.
    // If they don't exist, annotate with the expected type for tooling.
    const match = defs.get(val.name);
    if (match == undefined) {
      // Return an annotated error term instead of the reference, so the
      // expected type information is preserved for tooling.
      return Result(Ann(val, tty), tty, []);
    }
    // Reference exists, check it normally.
    var inf = infer(defs, adts, ctx, val, os, oe);
    const eq = equate(ctx, defs, inf.type, typ, val);
    if (!eq.eq) {
      const ptyp = pretty(tty);
      const pinf = pretty(inf.type);

      // Check if this is a missing type argument error
      const betterError = makeMissingTypeArgError(val, inf.type);
      if (betterError) {
        throw TypecheckError(betterError, os, oe);
      }

      throw TypecheckError(
        `typecheck failed: ${ptyp} is not ${pinf} in ctx ${printCtx(ctx)}`,
        os,
        oe
      );
    }
    return Result(val, tty, inf.holes.concat(eq.holes));
  } else {
    // infer the type of the term and check that it's equal to the supplied
    // type.
    var inf = infer(defs, adts, ctx, val, os, oe);
    const eq = equate(ctx, defs, inf.type, typ, val);
    if (!eq.eq) {
      const ptyp = pretty(tty);
      const pinf = pretty(inf.type);

      // Check if this is a missing type argument error
      const betterError = makeMissingTypeArgError(val, inf.type);
      if (betterError) {
        throw TypecheckError(betterError, os, oe);
      }

      throw TypecheckError(
        `typecheck failed: ${ptyp} is not ${pinf} in ctx ${printCtx(ctx)}`,
        os,
        oe
      );
    }

    return Result(inf.term, tty, inf.holes.concat(eq.holes));
  }
};

const findConstructor = (name: string, adt: ADT, os: number, oe: number) => {
  for (const con of adt.constructors) {
    if (identifier2str(con.name) == name) {
      return con;
    }
  }
  throw TypecheckError(`constructor not found: ${name}`, os, oe);
};

// The case statement is used for destructuring ADTs. Syntactically, we
// specify what should happen for every constructor, then when the statement
// is evaluated one of the branches is picked.
//
// For example:
//
//   type List(T *) = nil | cons(head T, tail List(T))
//   let x:List(Bool) = nil
//   let b = case x of
//     nil -> false
//     cons -> x.head
//
// In terms of implementation, each value is represented as a lambda that acts
// as an eliminator for that type. The way it does this is that it takes an
// argument for each constructor and each value returns that specific
// constructor. For booleans this would look like:
//
//   true = λt λf t
//   false = λt λf f
//   true(5)(6) ~> 5
//   false(5)(6) ~> 6
//
// Back to our List example, if x is the identifier we're destructuring we
// can write:
//
//   x(nilBranch)(λx.head λx.tail consBranch)
//
// then during evaluation x can be either nil or cons, nil evaluating to
// `nilBranch` and cons evaluating to `λx.head λx.tail consBranch`.
//
// Indexed types such as Vectors have optional type annotations on each
// constructor, for example:
//
// type Vector(T *, n Nat) = vnil : Vector(T, 0) | ext(head T, tail Vector(T, n)) : Vector(T, succ(n))
//
export const desugarCaseStatement = (
  defs: Map<string, Def2>,
  adts: Map<string, ADT>,
  ctx: Context,
  caseStmt: Case,
  os: number,
  oe: number,
  tty: Term
): Result => {
  // We need to infer the type of x so that we can look up the constructors.
  const xTyp = infer(defs, adts, ctx, caseStmt.name, os, oe);
  let ref = strip(xTyp.type);
  if (ref._ == "ref") {
    // ok
  } else if (ref._ == "app") {
    // This may be a type constructor such as List. We don't need the
    // arguments to look up the ADT definition.
    ref = getTypeNameFromTypeConstructor(ref);
  } else {
    throw TypecheckError(
      `type of argument to case should be a reference; got ${ref._}`,
      os,
      oe
    );
  }

  // Now look up the constructors for the type.
  const adtDef = adts.get(ref.name);
  if (adtDef == undefined) {
    throw TypecheckError(`type not found: ${ref.name}`, os, oe);
  }

  // Ensure all branches are covered.
  if (caseStmt.branches.length < adtDef.constructors.length) {
    throw TypecheckError(`case statement doesn't handle all cases`, os, oe);
  } else if (caseStmt.branches.length > adtDef.constructors.length) {
    throw TypecheckError(`case statement has too many cases`, os, oe);
  }

  const caseName = pretty(caseStmt.name);

  // Desugar each branch of the case statement and emit lambdas for the
  // constructor arguments.
  const branches = caseStmt.branches.map((branch) => {
    var constructor: Constructor | undefined = findConstructor(
      identifier2str(branch.constructor),
      adtDef,
      os,
      oe
    );

    // Make constructor arguments available on each branch. Any free Vars inside
    // the branch term must be bumped as we add these Abs nodes to the tree.
    // All variables in the branch term reference the outer context and must be
    // shifted up by the number of constructor arguments we're adding.
    const shifted = shift(constructor.args.length, 0, branch.term);

    const branchBodyWithArgs = constructor.args.reduceRight(
      (acc: Term, arg: Argument) => Abs(`${caseName}.${arg.name}`, acc),
      shifted
    );

    // Desugar the branch body - at this point the body still contains Refs that
    // reference the constructor arguments. Turn these into Vars.
    const branchBodyWithArgsDesugared = fixupRefs(
      branchBodyWithArgs,
      undefined,
      adts,
      ctx
    );

    // FIXME: This isn't an origin?
    return Syntax(branch.constructor as Origin, branchBodyWithArgsDesugared);
  });

  // The case statement desugars to
  //  val(λP tty)(λval.arg1 ... λval.argN branch1)...(λval.arg1 ... λval.argN branchN)

  // Leave this binder empty so that dependently typed expressions don't
  // throw binder mismatch errors.
  const P = Abs("", shift(0, 0, tty)); // P just returns the expected type

  const desugared = branches.reduce<Term>((acc: Term, branch) => {
    return App(acc, branch);
  }, App(caseStmt.name, P) as Term);

  return check(defs, adts, ctx, desugared, tty, os, oe);
};

// given an ast of the form App(App(App(X,y),z),w) return the leftmost ref X.
function getTypeNameFromTypeConstructor(t: Term): Ref {
  switch (t._) {
    case "ref":
      return t;
    case "app":
      return getTypeNameFromTypeConstructor(t.func);
    default:
      throw `unexpected ${t._}`;
  }
}

// fill attempts to consolidate holes. During typechecking we mark which holes
// must be the same and when we encounter an equality between a hole and a term
// we note down what the hole must contain. This function then substitutes those
// inferred values into the AST.
export const fill = (chk: Result): Result => {
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

  // TODO: Remove holes that just reference themselves - i.e. 0 => Hole(0). It's
  // not incorrect but the substHoles below will do nothing.

  for (let i = 0; i < chk.holes.length; i++) {
    const hole = chk.holes[i];
    updtm = substHole(hole.id, hole.term, updtm);
    updty = substHole(hole.id, hole.term, updty);

    // Update any subsequent holes in this list.
    for (let j = i + 1; j < chk.holes.length; j++) {
      chk.holes[j].term = substHole(hole.id, hole.term, chk.holes[j].term);
    }
  }

  // TODO: Doesn't this require re-checking?

  return Result(updtm, updty, chk.holes);
};

// aeq returns true if the two terms are alpha-equivalent, i.e. they are the
// same up to renaming of bound variables.
const aeq = (t1: Term, t2: Term): boolean => {
  // ignore origins
  if (t1._ == "orig" || t1._ == "syn" || t1._ == "label") {
    return aeq(t1.child, t2);
  }
  if (t2._ == "orig" || t2._ == "syn" || t2._ == "label") {
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
      return t2._ == "ann" && aeq(t1.term, t2.term) && aeq(t1.type, t2.type);
    case "pi":
      return t2._ == "pi" && aeq(t1.from, t2.from) && aeq(t1.body, t2.body);
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
      return t2._ == "let" && aeq(t1.expr, t2.expr) && aeq(t1.body, t2.body);
    case "int":
      return t2._ == "int" && t2.num == t1.num;
    case "str":
      return t2._ == "str" && t2.str == t1.str;
    case "err":
      // throw "aeq: unexpected parse error";
      return true;
    case "key":
      throw "aeq: unexpected keyword";
  }
};

// equate calculates whether two terms are equal. If there are any holes the
// hole is considered to be filled by the term and is returned. If two holes
// are compared then it's assumed they're the same and that fact is returned.
// For example,
//   null(▨0) == null(▨1) implies that ▨0 and ▨1 are the same hole
//   f(Nat,Bool) == f(Nat,▨0) imples that ▨0 is Bool.
export const equate = (
  ctx: Context,
  defs: Map<string, Def2>,
  ty1: Term,
  ty2: Term,
  val: Term,
  depth: number = 0,
  checking: Set<string> = Set()
): { eq: boolean; holes: Array<{ id: number; term: Term }> } => {
  // Ignore origins.
  if (ty1._ == "orig" || ty1._ == "syn") {
    return equate(ctx, defs, ty1.child, ty2, val, depth + 1, checking);
  }
  if (ty2._ == "orig" || ty2._ == "syn") {
    return equate(ctx, defs, ty1, ty2.child, val, depth + 1, checking);
  }

  if (aeq(ty1, ty2)) {
    return { eq: true, holes: [] };
  }

  const lhs = pretty(ty1);
  const rhs = pretty(ty2);
  if (verbose) {
    logger.debug(`eq ${lhs}`);
    logger.debug(`== ${rhs}`);
  }

  // FIXME: There must be a better way of doing this.
  // FIXME: This also simplifies expressions (no indices, no annotations)
  const current = `${lhs} == ${rhs}`;
  if (checking.has(current)) {
    return { eq: false, holes: [] };
  }
  const nc = checking.add(current);

  if (depth > 1000) {
    throw TypecheckError("equate depth exceeds limit", 0, 0);
  }

  if (ty1._ == "app" && ty2._ == "app") {
    const l = equate(ctx, defs, ty1.func, ty2.func, val, depth + 1, nc);
    const r = equate(ctx, defs, ty1.arg, ty2.arg, val, depth + 1, nc);
    const e = l.eq && r.eq;
    if (e) return { eq: true, holes: l.holes.concat(r.holes) };
  } else if (ty1._ == "lam" && ty2._ == "lam") {
    const e = equate(ctx, defs, ty1.body, ty2.body, val, depth + 1, nc);
    if (e.eq) return e;
  } else if (ty1._ == "self" && ty2._ == "self") {
    const e = equate(ctx, defs, ty1.body, ty2.body, val, depth + 1, nc);
    if (e.eq) return e;
  } else if (ty1._ == "pi" && ty2._ == "pi") {
    const l = equate(ctx, defs, ty1.from, ty2.from, val, depth + 1, nc);
    const r = equate(ctx, defs, ty1.body, ty2.body, val, depth + 1, nc);
    const e = l.eq && r.eq;
    if (e) return { eq: true, holes: l.holes.concat(r.holes) };
  } else if (ty1._ == "star" && ty2._ == "star") {
    return { eq: true, holes: [] };
  } else if (ty1._ == "var" && ty2._ == "var") {
    return { eq: ty1.index == ty2.index, holes: [] };
  } else if (ty1._ == "ref" && ty2._ == "ref") {
    // Comparing two definitions for equality returns false if they have
    // different names. This ensures types with different meanings are not
    // equal, even if their implementation is the same.
    return { eq: ty1.name == ty2.name, holes: [] };
  } else if (ty1._ == "let" && ty2._ == "let") {
    const e = equate(ctx, defs, ty1.body, ty2.body, val, depth + 1, nc);
    if (e.eq) return e;
  } else if (ty1._ == "hole") {
    // Assume the hole is valid, if it's not the typecheck will fail after the
    // hole substitution.
    logger.debug(`ho ${ty1.id}`);
    logger.debug(`== ${rhs}`);
    // It's important that we return the non-reduced term here, otherwise the
    // hole filling will resolve some long term the user isn't expecting.
    return { eq: true, holes: [{ id: ty1.id, term: ty2 }] };
  } else if (ty2._ == "hole") {
    logger.debug(`ho ${ty2.id}`);
    logger.debug(`== ${lhs}`);
    return { eq: true, holes: [{ id: ty2.id, term: ty1 }] };
  }

  // Try and reduce the left hand side and compare again.
  let n1 = reduce(true, ctx, defs, ty1);
  n1 = n1._ == "self" ? substTop(val, n1.body, n1.name) : n1;
  if (n1 !== ty1) {
    return equate(ctx, defs, n1, ty2, val, depth + 1, nc);
  }

  // Try and reduce the right hand side and compare again.
  let n2 = reduce(true, ctx, defs, ty2);
  n2 = n2._ == "self" ? substTop(val, n2.body, n2.name) : n2;
  if (n2 !== ty2) {
    return equate(ctx, defs, ty1, n2, val, depth + 1, nc);
  }

  return { eq: false, holes: [] };
};

export const defs = (defs: Def2[] = []): Map<string, Def2> => {
  const m = new Map<string, Def2>();
  for (const d of defs) {
    m.set(d.name, d);
  }
  return m;
};

export const adts = (adts: ADT[] = []): Map<string, ADT> => {
  const m = new Map<string, ADT>();
  for (const adt of adts) {
    m.set(identifier2str(adt.name), adt);
  }
  return m;
};
