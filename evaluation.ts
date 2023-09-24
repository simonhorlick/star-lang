import { Term } from "./ast";
import { identifier } from "./check";
import * as Erased from "./erased";
import { prettyC } from "./pretty";

let fs = require("fs");

function getChar(): string {
  let buffer = Buffer.alloc(1);
  fs.readSync(0, buffer, 0, 1);
  return buffer.toString("utf8");
}

export function erase(term: Term): Erased.Term {
  // TODO: remove unused arguments
  switch (term._) {
    case "var":
      return Erased.Var(term.name, term.index);
    case "lam":
      return Erased.Abs(identifier(term.name), erase(term.body));
    case "app":
      return Erased.App(erase(term.left), erase(term.right));
    case "ann":
      return erase(term.term);
    case "ref":
      return Erased.Ref(term.name);
    case "pi":
      return Erased.Abs("pi", Erased.Var("pi", 0));
    case "star":
      throw "erase: unexpected star";
    case "case":
      throw "erase: unexpected case";
    case "if":
      throw "erase: unexpected if";
    case "let":
      throw "erase: unexpected let";
    case "self":
      // throw "unexpected self";
      return Erased.Abs("erased", Erased.Var("erased", 0));
    case "orig":
      return erase(term.child);
    case "rel":
      return erase(term.term);
    case "par":
      throw "erase: unexpected par";
    case "id":
      throw "erase: unexpected id";
    case "hole":
      throw "erase: unexpected hole";
    case "int":
      throw "erase: unexpected integer literal";
    case "str":
      return Erased.StringLit(term.str);
    case "err":
      throw "erase: unexpected parse error";
  }
}

// Shifting renumbers the indices of the free variables in a term.
export function termShift2(d: number, t: Erased.Term): Erased.Term {
  const walk = (d: number, c: number, t: Erased.Term): Erased.Term => {
    switch (t._) {
      case "var":
        if (t.index >= c) {
          return Erased.Var(t.name, t.index + d);
        } else {
          return Erased.Var(t.name, t.index);
        }
      case "lam":
        // case "vlam":
        return Erased.Abs(t.name, walk(d, c + 1, t.body));
      case "app":
        // case "vapp":
        return Erased.App(walk(d, c, t.left), walk(d, c, t.right));
      case "ref":
        return t;
      case "str":
        return t;
    }
  };
  return walk(d, 0, t);
}

// Given a term t, find all Vars with index j and replace them with the term s.
export function termSubst2(
  j: number,
  s: Erased.Term,
  t: Erased.Term
): Erased.Term {
  const walk = (
    j: number,
    s: Erased.Term,
    c: number,
    t: Erased.Term
  ): Erased.Term => {
    switch (t._) {
      case "var":
        if (t.index == j + c) {
          // Substitute in the term s, renumbering any free variables so the
          // expression is consistent.
          return termShift2(c, s);
        } else {
          return Erased.Var(t.name, t.index);
        }
      case "lam":
        // case "vlam":
        return Erased.Abs(t.name, walk(j, s, c + 1, t.body));
      case "app":
        // case "vapp":
        return Erased.App(walk(j, s, c, t.left), walk(j, s, c, t.right));
      case "ref":
        return t;
      case "str":
        return t;
    }
  };

  return walk(j, s, 0, t);
}

// The term being substituted for the bound variable is first shifted up by one, then the
// substitution is made, and then the whole result is shifted down by one to account for the
// fact that the bound variable has been used up.
export function termSubstTop2(s: Erased.Term, t: Erased.Term): Erased.Term {
  return termShift2(-1, termSubst2(0, termShift2(1, s), t));
}

// Traverse App terms and collect the arguments in-order.
//       ap
//      /  \
//     ap   d
//    /  \
//   ap   c
//  /  \
// a    b
export const traverseInOrder = (
  root: Erased.Term,
  rightDepthLimit: number
): Array<Erased.Term> => {
  const doTraverse = (
    s: Erased.Term,
    rightDepth: number
  ): Array<Erased.Term> => {
    if (rightDepth >= rightDepthLimit) {
      return [s];
    }
    if (
      s._ == "app"
      //  || s._ == "vapp"
    ) {
      return doTraverse(s.left, 0).concat(doTraverse(s.right, rightDepth + 1));
    } else {
      return [s];
    }
  };

  return doTraverse(root, 0);
};

export function toJsArray(s: Erased.Term): Array<Erased.Term> {
  // either `nil(T)` or `((cons(T))(head))(tail)`
  const terms = traverseInOrder(s, 1);
  if (terms[0]._ == "ref" && terms[0].name == "nil") {
    return [];
  } else if (terms[0]._ == "ref" && terms[0].name == "cons") {
    const head = terms[2];
    const tail = terms[3];
    return [head].concat(toJsArray(tail));
  } else {
    throw `toJsArray: unexpected ${prettyC(terms[0])}`;
  }
}

interface Redex {
  _: "rx";
  term: Erased.Term;
}
interface NormalForm {
  _: "nf";
  term: Erased.Term;
}
type Step = Redex | NormalForm;

export const Redex = (t: Erased.Term): Redex => ({
  _: "rx",
  term: t,
});
export const NormalForm = (t: Erased.Term): NormalForm => ({
  _: "nf",
  term: t,
});

function runtime(args: Erased.StringLit[]): Step {
  switch (args[0].str) {
    case "println":
      console.log(args[1].str);
      // evaluate this expression to the argument string.
      return NormalForm(args[1]);
    default:
      throw `unknown runtime function: ${args[0].str}`;
  }
}

const HasFreeVariables = (t: Erased.Term, n: number = 0): boolean => {
  switch (t._) {
    case "app":
      return HasFreeVariables(t.left, n) || HasFreeVariables(t.right, n);
    case "lam":
      return HasFreeVariables(t.body, n + 1);
    case "ref":
      return false;
    case "str":
      return false;
    case "var":
      return t.index >= n;
  }
};

interface Runtime {
  getChar: () => string;
  println: (s: string) => void;
}

export const nodeJsRuntime: Runtime = {
  getChar: getChar,
  println: (s: string) => console.log(s),
};

export const mockRuntime: Runtime = {
  getChar: () => "c",
  println: (s: string) => {},
};

//
//
// Definition : A lambda expression is in normal form if it contains no β-redexes, so that it cannot be further reduced using the β-rule. An expression in normal form has no more function applications to evaluate.
//

// When applied to a term that is not yet a value, it yields
// the next step of evaluation for that term. When applied to a value an exception is thrown.
// Reduce the term using a applicative-order evaluation strategy whereby a
// function's arguments are evaluated completely before the function is applied.
// returns true if there are more redexes and the term is not yet in normal form.
// TODO: I think for this we need the concept of a value - i.e. a term that's
// in normal form, and then apply the function if all args are in normal form.
// reduce the arguments first, then do beta reduction.
//
// Reduction rules:
//
// ------------------  beta (apply a function)
// (λx M)N → M[x ↦ N]
//
// N → N'
// ------------ mu (evaluate an actual parameter)
// M(N) → M(N')
//
// M → M'
// ------------ nu (evaluate to get a closure that can be applied)
// M(N) → M'(N)
//
// M → M'
// ------------ xi (optimise code, e.g., by inlining)
// λx M → λx M'
//
export function reduceOnce3(
  rt: Runtime,
  defs: Erased.Def[],
  term: Erased.Term
): Step {
  // A term has one of three forms (x, λx M, and M(N)), and given each form, you
  // look for a rule that has the form in the conclusion.

  // The x form is not reduced by any rule, so the reducer always returns NormalForm.
  if (term._ == "var" || term._ == "str") {
    return NormalForm(term);
  }

  if (term._ == "app") {
    // The M(N) form (application) might be reduced by Beta, Mu, or Nu. The
    // choices for reducing M(N) are:
    //  Nu    Try to reduce M
    //  Mu    Try to reduce N
    //  Beta  (only applies if M is a λ-form)

    // Three rules can be ordered in six ways, but in practice, only three orders are used.
    // If we try first Beta, then Nu, and finally Mu, we are implementing the normal-order reduction strategy. It is also called the “leftmost, outer-most” reduction strategy.
    // If we try Mu before Beta, we have an applicative-order reduction strategy. There are two typical variants: Mu, Nu, Beta is a left-to-right applicative-order reduction strategy, and Nu, Mu, Beta is a right-to-left applicative-order reduction strategy.

    const M = term.left;
    const N = term.right;

    //
    // ------------------  beta (apply a function)
    // (λx M)N → M[x ↦ N]
    //
    // M → M'
    // ------------ nu (evaluate to get a closure that can be applied)
    // M(N) → M'(N)
    // N → N'
    // ------------ mu (evaluate an actual parameter)
    // M(N) → M(N')

    // beta
    if (M._ == "lam") {
      return Redex(termSubstTop2(N, M.body));
    }
    // nu
    const Mprime = reduceOnce3(rt, defs, M);
    if (prettyC(M) != prettyC(Mprime.term)) {
      return Redex(Erased.App(Mprime.term, N));
    }

    // mu
    const Nprime = reduceOnce3(rt, defs, N);
    // TODO: How do we know whether this rule applies? Surely it needs to be
    // known as part of the term.
    if (prettyC(N) != prettyC(Nprime.term)) {
      //     console.log(`${prettyC(N)} → ${prettyC(Nprime.term)}
      // ------------ mu (evaluate an actual parameter)
      // ${prettyC(Erased.App(M, N))} → ${prettyC(Erased.App(M, Nprime.term))}
      //   `);
      return Redex(Erased.App(M, Nprime.term));
    }

    // we have to check the tree and match on
    //     ap
    //    /  \
    //   ap   Unit
    //  /  \
    // pl  String
    if (M._ == "app" && M.left._ == "ref" && M.left.name == "println") {
      // Ensure everything is fully normalised first
      if (!HasFreeVariables(term)) {
        // beta-reduce the App, returning Unit -> Pair(String)(Unit)
        //
        // λs λn pair(String)(Unit)(Erased.StringLit("result"))(n)
        //
        // pair = λA λB λa λb λP λpair pair(a)(b)
        const argument = M.right;
        if (argument._ != "str") {
          throw "runtime error: expected string literal in argument to println";
        }
        rt.println(argument.str);

        const result = Erased.Abs(
          "n",
          Erased.App(
            Erased.App(
              Erased.App(
                Erased.App(Erased.Ref("pair"), Erased.Ref("String")),
                Erased.Ref("Unit")
              ),
              Erased.StringLit("printed") // no result
            ),
            Erased.Var("n", 0)
          )
        );
        const resultTree = Erased.App(result, N);

        return Redex(resultTree);
      }
    }

    // look up a def.
    if (M._ == "ref") {
      if (M.name == "println") {
        return Redex(term);
      }

      const match = defs.find((d) => d.name == M.name);
      if (match == undefined) {
        throw `reference not found: ${M.name}`;
      }
      return Redex(Erased.App(match.term, N));
    }
  }

  // runtime functions that take no arguments
  if (term._ == "ref") {
    if (term.name == "getchar") {
      // returns Unit -> Pair(String)(Unit)
      //
      // λn pair(String)(Unit)(Erased.StringLit("result"))(n)
      //
      // pair = λA λB λa λb λP λpair pair(a)(b)
      return Redex(
        Erased.Abs(
          "n",
          Erased.App(
            Erased.App(
              Erased.App(
                Erased.App(Erased.Ref("pair"), Erased.Ref("String")),
                Erased.Ref("Unit")
              ),
              Erased.StringLit(rt.getChar())
            ),
            Erased.Var("n", 0)
          )
        )
      );
    }

    const match = defs.find((d) => d.name == term.name);
    if (match == undefined) {
      throw `reference not found: ${term.name}`;
    }
    return Redex(match.term);
  }

  // throw "no rule applies";
  return NormalForm(term);
}

export function reduce(
  rt: Runtime,
  defs: Erased.Def[],
  t: Erased.Term
): Erased.Term {
  let normalForm = false;
  let prev: Erased.Term = t;
  while (!normalForm) {
    console.log(prettyC(t, false));
    const result = reduceOnce3(rt, defs, t);
    normalForm = result._ == "nf";

    // debug check
    if (!normalForm && prettyC(result.term) == prettyC(prev)) {
      throw "no forward progress";
    }
    prev = t;
    t = result.term;
  }
  return t;
}
