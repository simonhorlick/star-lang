#!/usr/bin/env ./node_modules/.bin/ts-node-script

import { Def, Term } from "./ast";
import { pretty } from "./pretty";

var _ = require("lodash");

function isValue(term: Term): boolean {
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
function reduceOnce(ctx: Def[], term: Term): Term {
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

function GetEvaluationTestSuite() {
  // What are we testing here?
  // - beta reduction
  // - Under the normal order strategy, the leftmost, outermost redex is always reduced first
  // - Surely this should be on the untyped lambda calculus, i.e. after checking?

  //     t1 → t1'
  // ---------------- E-App1
  // t1(t2) → t1'(t2)

  //     t2 → t2'
  // ---------------- E-App2
  // v1(t2) → v1(t2')

  // (λx:T11.t12)(v2) → [x/v2]t12     E-AppAbs

  // (λx:X.x)(y)
  // --------- using E-AppAbs
  // y

  //     t1 → t1'
  // ---------------- E-TApp
  // t1(T2) → t1'(T2)

  // (ΛX.t12)(T2) → [X/T2]t12    E-TappTabs

  // "if" reduction
  //
  // ctx contains (after typecheck has passed):
  //
  // tru = λt. λf. t
  // fls = λt. λf. f
  // test = λl. λm. λn. (l(m))(n)
  //
  // ((test(tru))(v))(w)
  // ------------------- def "test"
  // (((λl. λm. λn. (l(m))(n))(tru))(v))(w)
  // -------------------------------------- E-AppAbs
  // ((λm. λn. (tru(m))(n))(v))(w)
  // ----------------------------- E-AppAbs
  // (λn. (tru(v))(n))(w)
  // -------------------- E-AppAbs
  // (tru(v))(w)
  // ----------- def "tru"
  // ((λt. λf. t)(v))(w)
  // ------------------- E-AppAbs
  // (λf. v)(w)
  // ---------- E-AppAbs
  // v

  // tru = λt. λf. t
  const tru: Def = {
    type: "def",
    name: "tru",
    typ: { type: "ers" },
    term: {
      type: "lam", // should this be called abs?
      name: "t",
      typ: { type: "ers" },
      body: {
        type: "lam",
        name: "f",
        typ: { type: "ers" },
        body: {
          type: "ref",
          name: "t",
          index: undefined,
          contextLength: undefined,
        },
      },
    },
  };

  // fls = λt. λf. f
  const fls: Def = {
    type: "def",
    name: "fls",
    typ: { type: "ers" },
    term: {
      type: "lam",
      name: "t",
      typ: { type: "ers" },
      body: {
        type: "lam",
        name: "f",
        typ: { type: "ers" },
        body: {
          type: "ref",
          name: "f",
          index: undefined,
          contextLength: undefined,
        },
      },
    },
  };

  // test = λl. λm. λn. (l(m))(n)
  const test: Def = {
    type: "def",
    name: "test",
    typ: { type: "ers" },
    term: {
      type: "lam",
      name: "l",
      typ: { type: "ers" },
      body: {
        type: "lam",
        name: "m",
        typ: { type: "ers" },
        body: {
          type: "lam",
          name: "n",
          typ: { type: "ers" },
          body: {
            type: "app",
            left: {
              type: "app",
              left: {
                type: "ref",
                name: "l",
                index: undefined,
                contextLength: undefined,
              },
              right: {
                type: "ref",
                name: "m",
                index: undefined,
                contextLength: undefined,
              },
            },
            right: {
              type: "ref",
              name: "n",
              index: undefined,
              contextLength: undefined,
            },
          },
        },
      },
    },
  };

  const ctx: Def[] = [tru, fls, test];

  // ((test(tru))(v))(w)
  const term: Term = {
    type: "app",
    left: {
      type: "app",
      left: {
        type: "app",
        left: {
          type: "ref",
          name: "test",
          index: undefined,
          contextLength: undefined,
        },
        right: {
          type: "ref",
          name: "tru",
          index: undefined,
          contextLength: undefined,
        },
      },
      right: {
        type: "ref",
        name: "v",
        index: undefined,
        contextLength: undefined,
      },
    },
    right: {
      type: "ref",
      name: "w",
      index: undefined,
      contextLength: undefined,
    },
  };

  console.log(reduceOnce(ctx, term));

  const evaluationTests = [
    {
      expected: null,
      actual: null,
    },
  ];

  return {
    name: "evaluation",
    tests: evaluationTests,
  };
}

function RunAllTests2() {
  let suites = [GetEvaluationTestSuite()];

  let passed = 0;
  let total = 0;
  for (const s of suites) {
    for (let i = 0; i < s.tests.length; i++) {
      const t = s.tests[i];
      if (!_.isEqual(t.expected, t.actual)) {
        let expected = JSON.stringify(t.expected);
        let actual = JSON.stringify(t.actual);

        // If the output is long place them on their own lines.
        if (expected.length > 60) {
          expected = `\n${expected}`;
          actual = `\n${actual}`;
        }

        console.log(
          `failed: ${s.name} test ${i} expected ${expected}; got ${actual}`
        );
      } else {
        passed++;
      }
    }
    total += s.tests.length;
  }

  console.log(`passed ${passed}/${total}`);
}

RunAllTests();
