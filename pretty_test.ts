#!/usr/bin/env ./node_modules/.bin/ts-node-script

import { Def as DefT, Term, Type } from "./ast";
import { Abs, App, Def, Ref, Var } from "./evaluation";
import { pretty } from "./pretty";

var _ = require("lodash");

function GetPrettyTestSuite() {
  // tru = λt. λf. t
  const tru = Def("tru", Abs("t", Abs("f", Ref("t"))));

  // fls = λt. λf. f
  const fls = Def("fls", Abs("t", Abs("f", Ref("f"))));

  // test = λl. λm. λn. (l(m))(n)
  const test = Def(
    "test",
    Abs("l", Abs("m", Abs("n", App(App(Ref("l"), Ref("m")), Ref("n")))))
  );

  // fst: Nat = λn:Nat. λm:Nat. n
  const fst = Def("fst", Abs("n", Abs("m", Ref("n"), Ref("Nat")), Ref("Nat")));

  const id = App(Abs("x", Ref("x")), Ref("y"));

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
      expected: "λl. λm. λn. l(m)(n)",
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
    {
      expected: "(λx. 0)(λz. 0)",
      actual: pretty(App(Abs("x", Var("x", 0)), Abs("z", Var("z", 0)))),
    },
    {
      expected: "λs. λz. 1(0)",
      actual: pretty(Abs("s", Abs("z", App(Var("s", 1, 2), Var("z", 0, 2))))),
    },
    {
      expected: "λs. λz. 1(1(0))",
      actual: pretty(
        Abs(
          "s",
          Abs("z", App(Var("s", 1, 2), App(Var("s", 1, 2), Var("z", 0, 2))))
        )
      ),
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
