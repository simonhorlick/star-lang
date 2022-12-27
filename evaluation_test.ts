#!/usr/bin/env ./node_modules/.bin/ts-node-script

import { Def, Term, transformDebriujin } from "./ast";
import { isValue, reduceOnce } from "./evaluation";
import { pretty } from "./pretty";

var _ = require("lodash");

function reduce(defs: Def[], t: Term): Term {
  while (true) {
    console.log(pretty(t));

    if (isValue(t)) {
      break;
    }

    t = reduceOnce(defs, t);
  }

  return t;
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

  // // tru = λt. λf. t
  // const tru: Def = {
  //   type: "def",
  //   name: "tru",
  //   typ: { type: "ers" },
  //   term: {
  //     type: "lam", // should this be called abs?
  //     name: "t",
  //     typ: { type: "ers" },
  //     body: {
  //       type: "lam",
  //       name: "f",
  //       typ: { type: "ers" },
  //       body: {
  //         type: "ref",
  //         name: "t",
  //         index: undefined,
  //         contextLength: undefined,
  //       },
  //     },
  //   },
  // };

  // // fls = λt. λf. f
  // const fls: Def = {
  //   type: "def",
  //   name: "fls",
  //   typ: { type: "ers" },
  //   term: {
  //     type: "lam",
  //     name: "t",
  //     typ: { type: "ers" },
  //     body: {
  //       type: "lam",
  //       name: "f",
  //       typ: { type: "ers" },
  //       body: {
  //         type: "ref",
  //         name: "f",
  //         index: undefined,
  //         contextLength: undefined,
  //       },
  //     },
  //   },
  // };

  // // test = λl. λm. λn. (l(m))(n)
  // const test: Def = {
  //   type: "def",
  //   name: "test",
  //   typ: { type: "ers" },
  //   term: {
  //     type: "lam",
  //     name: "l",
  //     typ: { type: "ers" },
  //     body: {
  //       type: "lam",
  //       name: "m",
  //       typ: { type: "ers" },
  //       body: {
  //         type: "lam",
  //         name: "n",
  //         typ: { type: "ers" },
  //         body: {
  //           type: "app",
  //           left: {
  //             type: "app",
  //             left: {
  //               type: "ref",
  //               name: "l",
  //               index: undefined,
  //               contextLength: undefined,
  //             },
  //             right: {
  //               type: "ref",
  //               name: "m",
  //               index: undefined,
  //               contextLength: undefined,
  //             },
  //           },
  //           right: {
  //             type: "ref",
  //             name: "n",
  //             index: undefined,
  //             contextLength: undefined,
  //           },
  //         },
  //       },
  //     },
  //   },
  // };

  // const ctx: Def[] = [tru, fls, test];

  // // ((test(tru))(v))(w)
  // const term: Term = {
  //   type: "app",
  //   left: {
  //     type: "app",
  //     left: {
  //       type: "app",
  //       left: {
  //         type: "ref",
  //         name: "test",
  //         index: undefined,
  //         contextLength: undefined,
  //       },
  //       right: {
  //         type: "ref",
  //         name: "tru",
  //         index: undefined,
  //         contextLength: undefined,
  //       },
  //     },
  //     right: {
  //       type: "ref",
  //       name: "v",
  //       index: undefined,
  //       contextLength: undefined,
  //     },
  //   },
  //   right: {
  //     type: "ref",
  //     name: "w",
  //     index: undefined,
  //     contextLength: undefined,
  //   },
  // };

  //console.log(reduceOnce(ctx, term));

  // (λx. x)(y)
  const id: Term = transformDebriujin([], {
    type: "app",
    left: {
      type: "lam",
      name: "x",
      body: {
        type: "ref",
        name: "x",
        index: undefined,
        contextLength: undefined,
      },
      typ: { type: "ers" },
    },
    right: {
      type: "ref",
      name: "y",
      index: undefined,
      contextLength: undefined,
    },
  });

  const evaluationTests = [
    // (λx. x)(y) -> y
    {
      expected: {
        type: "ref",
        name: "y",
        contextLength: 0,
        index: undefined,
      } as Term,
      actual: reduce([], id),
    },
  ];

  return {
    name: "evaluation",
    tests: evaluationTests,
  };
}

function RunAllTests() {
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
