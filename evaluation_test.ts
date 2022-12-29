#!/usr/bin/env ./node_modules/.bin/ts-node-script

import { Def, Term, transformDebriujin as transformDebruijin } from "./ast";
import { Abs, App, isValue, reduceOnce, Ref, Var } from "./evaluation";
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

// tru = λt. λf. t
const tru: Def = {
  type: "def",
  name: "tru",
  typ: { type: "ers" },
  term: transformDebruijin([], {
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
      },
    },
  }),
};

// fls = λt. λf. f
const fls: Def = {
  type: "def",
  name: "fls",
  typ: { type: "ers" },
  term: transformDebruijin([], {
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
      },
    },
  }),
};

// test = λl. λm. λn. (l(m))(n)
const test: Def = {
  type: "def",
  name: "test",
  typ: { type: "ers" },
  term: transformDebruijin([], {
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
            },
            right: {
              type: "ref",
              name: "m",
            },
          },
          right: {
            type: "ref",
            name: "n",
          },
        },
      },
    },
  }),
};

// λs. λz. z
const zero = Abs("s", Abs("z", Var("z", 0, 2)));

// λs. λz. s z
const one = Abs("s", Abs("z", App(Var("s", 1, 2), Var("z", 0, 2))));

// λs. λz. s (s z)
const two = Abs(
  "s",
  Abs("z", App(Var("s", 1, 2), App(Var("s", 1, 2), Var("z", 0, 2))))
);

// λx. x
const id: Def = {
  type: "def",
  name: "id",
  typ: { type: "ers" },
  term: transformDebruijin([], Abs("x", Ref("x"))),
};

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

class T {
  pass: boolean = true;
  msg: string = "";

  fail(msg: string) {
    this.pass = false;
    this.msg = msg;
  }

  compare<T>(expected: T, actual: T) {
    if (!equal(expected, actual)) {
      this.fail(dbg(expected, actual));
    }
  }
}

const equal = <T>(a: T, b: T) => _.isEqual(a, b) as boolean;

const dbg = <T>(expected: T, actual: T): string => {
  let e = JSON.stringify(expected);
  let a = JSON.stringify(actual);

  // If the output is long place them on their own lines.
  if (e.length > 60) {
    e = `\n${e}`;
    a = `\n${a}`;
  }

  return `expected ${e}; got ${a}`;
};

const DeBruijinTestSuite: ((t: T) => void)[] = [];

const TestComputeDebruijinIndicesSingleBinder = (t: T) => {
  // Γ = [t]; λx.t
  // λ.1
  const expected: Term = Abs("x", Var("t", 1, 2));

  const actual = transformDebruijin(
    [{ name: "t", typ: { type: "ers" } }],
    Abs("x", Ref("t"))
  );

  if (!equal(expected, actual)) {
    t.fail(dbg(expected, actual));
  }
};
DeBruijinTestSuite.push(TestComputeDebruijinIndicesSingleBinder);

const TestComputeDebruijinIndicesIdApp = (t: T) => {
  // (λx. x)(λz. z)
  // (λ. 0)(λ. 0)
  const expected: Term = App(
    Abs("x", Var("x", 0, 1)),
    Abs("z", Var("z", 0, 1))
  );
  const actual = transformDebruijin(
    [],
    App(Abs("x", Ref("x")), Abs("z", Ref("z")))
  );

  if (!equal(expected, actual)) {
    t.fail(dbg(expected, actual));
  }
};
DeBruijinTestSuite.push(TestComputeDebruijinIndicesIdApp);

const TestComputeDebruijinIndicesChurchNat = (t: T) => {
  // λs. λz. s (s z)
  // λ. λ. 1 (1 0)
  const expected = two;

  const actual = transformDebruijin(
    [],
    Abs("s", Abs("z", App(Ref("s"), App(Ref("s"), Ref("z")))))
  );

  if (!equal(expected, actual)) {
    t.fail(dbg(expected, actual));
  }
};
DeBruijinTestSuite.push(TestComputeDebruijinIndicesChurchNat);

const EvaluationTestSuite: ((t: T) => void)[] = [];

// (λx. x)(λz. z) -> (λz. z)
const TestReduceIdentity = (t: T) => {
  const identity = transformDebruijin(
    [],
    App(Abs("x", Ref("x")), Abs("z", Ref("z")))
  );

  const expected: Term = transformDebruijin([], Abs("z", Ref("z")));

  const actual = reduce([], identity);

  if (!equal(expected, actual)) {
    t.fail(dbg(expected, actual));
  }
};
EvaluationTestSuite.push(TestReduceIdentity);

// Test that substituting top level functions works properly.
const TestSubstituteDef = (t: T) =>
  t.compare(
    Abs("z", Var("z", 0, 1)),
    reduce([id], App(Ref("id"), Abs("z", Var("z", 0, 1))))
  );
EvaluationTestSuite.push(TestSubstituteDef);

// test(tru)(1)(2) -> 1
const TestReduceIfElse = (t: T) => {
  // ((test(tru))(1))(2)
  const ifElse: Term = transformDebruijin(
    [],
    App(App(App(Ref("test"), Ref("tru")), one), two)
  );

  const expected = one;
  const actual = reduce([tru, fls, test], ifElse);

  if (!equal(expected, actual)) {
    t.fail(dbg(expected, actual));
  }
};
EvaluationTestSuite.push(TestReduceIfElse);

function RunAllTests() {
  let suites = [
    { name: "DeBruijinTestSuite", tests: DeBruijinTestSuite },
    { name: "EvaluationTestSuite", tests: EvaluationTestSuite },
  ];

  let passed = 0;
  let total = 0;
  for (const s of suites) {
    for (let i = 0; i < s.tests.length; i++) {
      const test = s.tests[i];
      const t = new T();
      test(t);
      if (!t.pass) {
        console.log(`failed: ${s.name} test ${i}: ${t.msg}`);
      } else {
        passed++;
      }
    }
    total += s.tests.length;
  }

  console.log(`passed ${passed}/${total}`);
}

RunAllTests();
