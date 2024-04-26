import { Term, identifier2str } from "./ast";
import * as Erased from "./erased";
import { prettyC } from "./pretty";
import { stringToUtf8ByteArray, utf8ByteArrayToString } from "./strings";

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
      return Erased.Abs(identifier2str(term.name), erase(term.body));
    case "app":
      return Erased.App(erase(term.func), erase(term.arg));
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
    case "syn":
      return erase(term.child);
    case "rel":
      return erase(term.term);
    case "par":
      throw "erase: unexpected par";
    case "id":
      throw "erase: unexpected id";
    case "key":
      throw "erase: unexpected key";
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

// in-order traversal of the term tree.
export const foldTree = <A>(
  f: (acc: A, curr: Erased.Term) => A,
  init: A,
  t: Erased.Term
): A => {
  switch (t._) {
    case "app":
      const left = foldTree(f, init, t.left);
      const curr = f(left, t);
      const rght = foldTree(f, curr, t.right);
      return rght;
    case "lam":
      return foldTree(f, f(init, t), t.body);
    case "ref":
    case "str":
    case "var":
      return f(init, t);
  }
};

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
  print: (s: string) => void;
}

export const nodeJsRuntime: Runtime = {
  getChar: getChar,
  print: (s: string) => process.stdout.write(s),
};

export const mockRuntime: Runtime = {
  getChar: () => "c",
  print: (s: string) => {},
};

// stringLiteralToTerm expands the given string literal into calls to scons
// of the utf-8 bytes in the string literal.
export const stringLiteralToTerm = (str: string) =>
  stringToUtf8ByteArray(str).reduceRight<Erased.Term>(
    (acc, curr) =>
      Erased.App(Erased.App(Erased.Ref("scons"), byteFromNumber(curr)), acc),
    Erased.Ref("snil")
  );

// converts a runtime Byte term to a javascript number.
export const byteToNumber = (P: any): number => {
  const body = P.body.body;

  const folded = foldTree(
    (acc: any, curr: any) => {
      if (curr._ == "var") {
        return [...acc, curr];
      } else {
        return acc;
      }
    },
    [],
    body
  );

  const b0 = 1 - folded[1].index;
  const b1 = 1 - folded[2].index;
  const b2 = 1 - folded[3].index;
  const b3 = 1 - folded[4].index;
  const b4 = 1 - folded[5].index;
  const b5 = 1 - folded[6].index;
  const b6 = 1 - folded[7].index;
  const b7 = 1 - folded[8].index;

  return (
    b7 |
    (b6 << 1) |
    (b5 << 2) |
    (b4 << 3) |
    (b3 << 4) |
    (b2 << 5) |
    (b1 << 6) |
    (b0 << 7)
  );
};

const numberToStringLiteral = (n: number): string => utf8ByteArrayToString([n]);

const byteFromNumber = (num: number): Erased.Term => {
  // 0 0 0 0 0 0 0 1 = 0x01
  // 0 0 0 0 0 0 1 0 = 0x02
  // 0 0 0 0 0 1 0 0 = 0x04
  // 0 0 0 0 1 0 0 0 = 0x08
  // 0 0 0 1 0 0 0 0 = 0x10
  // 0 0 1 0 0 0 0 0 = 0x20
  // 0 1 0 0 0 0 0 0 = 0x40
  // 1 0 0 0 0 0 0 0 = 0x80
  const b7 = (num & 0x01) == 0 ? Erased.Ref("o") : Erased.Ref("i");
  const b6 = (num & 0x02) == 0 ? Erased.Ref("o") : Erased.Ref("i");
  const b5 = (num & 0x04) == 0 ? Erased.Ref("o") : Erased.Ref("i");
  const b4 = (num & 0x08) == 0 ? Erased.Ref("o") : Erased.Ref("i");
  const b3 = (num & 0x10) == 0 ? Erased.Ref("o") : Erased.Ref("i");
  const b2 = (num & 0x20) == 0 ? Erased.Ref("o") : Erased.Ref("i");
  const b1 = (num & 0x40) == 0 ? Erased.Ref("o") : Erased.Ref("i");
  const b0 = (num & 0x80) == 0 ? Erased.Ref("o") : Erased.Ref("i");
  return Erased.App(
    Erased.App(
      Erased.App(
        Erased.App(
          Erased.App(
            Erased.App(Erased.App(Erased.App(Erased.Ref("byte"), b0), b1), b2),
            b3
          ),
          b4
        ),
        b5
      ),
      b6
    ),
    b7
  );
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
  term: Erased.Term,
  trace: boolean = false
): Step {
  // A term has one of three forms (x, λx M, and M(N)), and given each form, you
  // look for a rule that has the form in the conclusion.

  // The x form is not reduced by any rule, so the reducer always returns NormalForm.
  if (term._ == "var" || term._ == "str") {
    return NormalForm(term);
  }

  // The λx M form is reduced by exactly one of the rules above (Xi), and there’s a reduction judgment above the line, so the reducer always makes a recursive call to try to reduce M.
  if (term._ == "lam") {
    const M = term.body;
    // M → M'
    // ------------ xi (optimise code, e.g., by inlining)
    // λx M → λx M'
    const Mprime = reduceOnce3(rt, defs, M);
    if (prettyC(term.body) != prettyC(Mprime.term)) {
      if (trace) {
        console.log(`${prettyC(M)} → ${prettyC(Mprime.term)}
------------ xi (optimise code, e.g., by inlining)
${prettyC(term)} → ${prettyC(Erased.Abs(term.name, Mprime.term))}`);
      }

      if (Mprime._ == "nf") {
        return NormalForm(Erased.Abs(term.name, Mprime.term));
      } else {
        return Redex(Erased.Abs(term.name, Mprime.term));
      }
    }
    // If it's an abstraction and we can't reduce the body, then it's in
    // normal form.
    return NormalForm(Erased.Abs(term.name, term.body));
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

    // for debugging...
    const Md = prettyC(M);
    const Nd = prettyC(N);

    //
    // ------------------  beta (apply a function)
    // (λx M)N → M[x ↦ N]
    if (M._ == "lam") {
      if (trace) {
        console.log(`
------------------  beta (apply a function)
(${prettyC(term)} → ${prettyC(termSubstTop2(N, M.body))}`);
      }
      return Redex(termSubstTop2(N, M.body));
    }

    // M → M'
    // ------------ nu (evaluate to get a closure that can be applied)
    // M(N) → M'(N)
    const Mprime = reduceOnce3(rt, defs, M);
    if (prettyC(M) != prettyC(Mprime.term)) {
      if (trace) {
        console.log(`${prettyC(M)} → ${prettyC(Mprime.term)}
------------ nu (evaluate to get a closure that can be applied)
${prettyC(Erased.App(M, N))} → ${prettyC(Erased.App(Mprime.term, N))}`);
      }
      return Redex(Erased.App(Mprime.term, N));
    }

    // N → N'
    // ------------ mu (evaluate an actual parameter)
    // M(N) → M(N')
    const Nprime = reduceOnce3(rt, defs, N);
    // TODO: How do we know whether this rule applies? Surely it needs to be
    // known as part of the term.
    if (prettyC(N) != prettyC(Nprime.term)) {
      if (trace) {
        console.log(`${prettyC(N)} → ${prettyC(Nprime.term)}
------------ mu (evaluate an actual parameter)
${prettyC(Erased.App(M, N))} → ${prettyC(Erased.App(M, Nprime.term))}`);
      }
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
      if (HasFreeVariables(term)) {
        // debug check:
        throw "argument to print has free variables";
      } else {
        // beta-reduce the App, returning Unit -> Pair(String)(Unit)
        //
        // λs λn pair(String)(Unit)(Erased.StringLit("result"))(n)
        //
        // pair = λA λB λa λb λP λpair pair(a)(b)
        let argument = M.right;
        if (argument._ == "str") {
          // string literal
          rt.print(argument.str);
        } else if (argument._ == "lam") {
          // cons string
          rt.print(consStringToLiteral(argument));
        } else {
          throw "runtime error: unexpected argument to printf";
        }

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

    // Expand string literals that require elimination.
    if (M._ == "str") {
      return Redex(Erased.App(stringLiteralToTerm(M.str), N));
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
      const str = rt.getChar();
      return Redex(
        Erased.Abs(
          "n",
          Erased.App(
            Erased.App(
              Erased.App(
                Erased.App(Erased.Ref("pair"), Erased.Ref("String")),
                Erased.Ref("Unit")
              ),
              Erased.StringLit(str)
            ),
            Erased.Var("n", 0)
          )
        )
      );
    } else if (term.name == "println") {
      return Redex(term);
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
  t: Erased.Term,
  trace: boolean = false
): Erased.Term {
  let normalForm = false;
  let prev: Erased.Term = t;
  while (!normalForm) {
    if (trace) {
      console.log(prettyC(t, false));
    }
    const result = reduceOnce3(rt, defs, t, trace);
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

// Takes a runtime cons-string term and converts it to a javascript string literal.
export function consStringToLiteral(P: any): string {
  // quick hack for if it's not actually a cons-string.
  if (P._ == "str") return P.str;

  const snil = P.body;
  const scons = snil.body;
  const _ = scons.body;

  const folded = foldTree<Erased.Term[]>((acc, curr) => [...acc, curr], [], _);

  switch ((folded[0] as Erased.Var).name) {
    case "scons": {
      const head = P.body.body.body.left.right;
      const tail = P.body.body.body.right;

      const b = byteToNumber(head);
      const char = numberToStringLiteral(b);

      return char + consStringToLiteral(tail);
    }
    case "snil":
      return "";
    default:
      throw "bug";
  }
}
