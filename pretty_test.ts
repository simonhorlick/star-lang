#!/usr/bin/env ./node_modules/.bin/ts-node-script

import { Def, Term, Type } from "./ast";
import { pretty } from "./pretty";

var _ = require("lodash");

function GetPrettyTestSuite() {
  // tru = λt. λf. t
  const tru: Def = {
    type: "def",
    name: "tru",
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

  // fst: Nat = λn:Nat. λm:Nat. n
  const fst: Def = {
    type: "def",
    name: "fst",
    typ: {
      type: "ref",
      name: "Nat",
      index: undefined,
      contextLength: undefined,
    },
    term: {
      type: "lam",
      name: "n",
      typ: {
        type: "ref",
        name: "Nat",
        index: undefined,
        contextLength: undefined,
      },
      body: {
        type: "lam",
        name: "m",
        typ: {
          type: "ref",
          name: "Nat",
          index: undefined,
          contextLength: undefined,
        },
        body: {
          type: "ref",
          name: "n",
          index: undefined,
          contextLength: undefined,
        },
      },
    },
  };

  const id: Term = {
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
  };

  const prettyTests = [
    {
      expected: "λt. λf. t",
      actual: pretty(tru.term),
    },
    {
      expected: "λt. λf. f",
      actual: pretty(fls.term),
    },
    {
      expected: "λl. λm. λn. (l(m))(n)",
      actual: pretty(test.term),
    },
    {
      expected: "λn:Nat. λm:Nat. n",
      actual: pretty(fst.term),
    },
    {
      expected: "(λx. x)(y)",
      actual: pretty(id),
    },
  ];

  return {
    name: "pretty",
    tests: prettyTests,
  };
}

function RunAllTests() {
  let suites = [GetPrettyTestSuite()];

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
