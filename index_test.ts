#!/usr/bin/env ./node_modules/.bin/ts-node-script

var _ = require("lodash");
var util = require("util");

import {
  char,
  choice,
  and,
  str,
  many,
  optional,
  andThen,
  line,
  Result,
  Stream,
  abstraction,
  application,
  definition,
  indexToLineCol,
  parenthesis,
  parseFile,
  parseLineComment,
  parsePackage,
  reference,
  s,
  term,
  identifier,
  type,
  arrow,
} from ".";

const parseA = char("A");
const parseB = char("B");
const parseAorB = choice(parseA, parseB);

const parseAandB = and(parseA, parseB);

const parseAB = str("AB");

const parseManyA = many(char("a"));

const parseOptionalB = optional(char("b"));

const parseAoptionalB = andThen(char("a"), parseOptionalB, char("a"));

const success = (x: Result) => x.type == "outputvalue";

const ts = (s: string): Stream => ({
  src: `parsed${s}`,
  idx: 6,
  origins: false,
});

const result = (x: Result) => {
  if (x.type == "parseerror") {
    return x.error;
  } else {
    return x.value;
  }
};

const resultC = (x: Result) => {
  if (x.type == "parseerror") {
    return x.error;
  } else {
    if (x.stream.idx != x.stream.src.length) {
      return "stream not consumed";
    }
    return x.value;
  }
};

function GetParserTestSuite() {
  const parserTests = [
    {
      expected: true,
      actual: success(parseAB(ts("ABALONE"))),
    },
    {
      expected: true,
      actual: success(parseAorB(ts("Applesauce and orange juice"))),
    },
    { expected: true, actual: success(parseAorB(ts("Buckets of rain"))) },
    { expected: false, actual: success(parseAorB(ts("Canada oh Canada"))) },
    { expected: false, actual: success(parseAandB(ts("Argyle sweaters"))) },
    {
      expected: false,
      actual: success(parseAandB(ts("Beer battered bananas"))),
    },
    { expected: true, actual: success(parseAandB(ts("ABBA"))) },
    {
      expected: "one two three",
      actual: result(line(ts("one two three\nfour five six"))),
    },
    {
      expected: { type: "pkg", name: "abc" },
      actual: result(parsePackage(ts(`package abc`))),
    },
    {
      expected: ["a", "a", "a"],
      actual: result(parseManyA(ts("aaabbb"))),
    },
    {
      expected: "b",
      actual: result(parseOptionalB(ts("b"))),
    },
    {
      expected: null,
      actual: result(parseOptionalB(ts(""))),
    },
    {
      expected: ["a", null, "a"],
      actual: result(parseAoptionalB(ts("aa"))),
    },
    {
      expected: ["a", "b", "a"],
      actual: result(parseAoptionalB(ts("aba"))),
    },
    {
      expected: [
        { type: "com", text: " comment" },
        { type: "com", text: " comment 2" },
      ],
      actual: result(many(parseLineComment)(ts("// comment\n// comment 2"))),
    },
    // comment at EOF
    {
      expected: { type: "com", text: " comment" },
      actual: result(parseLineComment(ts("// comment"))),
    },
    {
      expected: "aaabbb",
      actual: result(identifier(ts("aaabbb"))),
    },
    {
      expected: "Abc",
      actual: result(identifier(ts("Abc"))),
    },
    {
      expected: false,
      actual: success(identifier(ts("0abc"))),
    },
    {
      expected: "abc0",
      actual: result(identifier(ts("abc0"))),
    },
    {
      expected: "a_b",
      actual: result(identifier(ts("a_b"))),
    },
    {
      expected: true,
      actual: success(parenthesis(char("a"))(ts("(a)"))),
    },
    {
      expected: {
        type: "lam",
        name: "x",
        typ: { type: "ref", name: "X" },
        body: { type: "ref", name: "t" },
      },
      actual: result(abstraction(() => term)(ts("λx:X.t"))),
    },
    {
      expected: {
        type: "app",
        name: { type: "ref", name: "f" },
        arg: { type: "ref", name: "x" },
      },
      actual: result(application(() => term)(ts("f(x)"))),
    },
    // want to parse `f(x)(y)` as the following tree:
    //
    //      ap
    //     /  \
    //    ap   y
    //   /  \
    //  f    x
    //
    {
      expected: {
        type: "app",
        name: {
          type: "app",
          name: { type: "ref", name: "f" },
          arg: { type: "ref", name: "x" },
        },
        arg: { type: "ref", name: "y" },
      },
      actual: result(application(() => term)(ts("f(x)(y)"))),
    },
    {
      expected: {
        type: "app",
        name: {
          type: "app",
          name: { type: "ref", name: "b" },
          arg: { type: "ref", name: "v" },
        },
        arg: { type: "ref", name: "w" },
      },
      actual: result(application(() => term)(ts("(b(v))(w)"))),
    },
    {
      expected: {
        type: "lam",
        name: "t",
        typ: { type: "ref", name: "Bool" },
        body: {
          type: "lam",
          name: "f",
          typ: { type: "ref", name: "Bool" },
          body: { type: "ref", name: "t" },
        },
      },
      actual: result(term(ts("λt:Bool. λf:Bool. t"))),
    },
    {
      expected: {
        type: "app",
        name: { type: "ref", name: "x" },
        arg: {
          type: "app",
          name: { type: "ref", name: "y" },
          arg: { type: "ref", name: "z" },
        },
      },
      actual: result(term(ts("x (y (z))"))),
    },
    {
      expected: {
        type: "lam",
        name: "z",
        typ: { type: "ref", name: "Z" },
        body: {
          type: "lam",
          name: "x",
          typ: { type: "ref", name: "X" },
          body: {
            type: "lam",
            name: "y",
            typ: { type: "ref", name: "Y" },
            body: {
              type: "app",
              name: { type: "ref", name: "x" },
              arg: {
                type: "app",
                name: { type: "ref", name: "y" },
                arg: { type: "ref", name: "z" },
              },
            },
          },
        },
      },
      actual: result(term(ts("λz:Z. λx:X. λy:Y. x (y (z))"))),
    },
    {
      expected: {
        type: "def",
        name: "id",
        term: {
          type: "lam",
          name: "x",
          body: { type: "ref", name: "x" },
          typ: { type: "ref", name: "X" },
        },
        typ: { type: "ref", name: "X" },
      },
      actual: result(definition(ts("func id:X = λx:X. x"))),
    },
    {
      expected: { type: "ref", name: "ex2" },
      actual: result(reference(ts("ex2"))),
    },
    {
      expected: { type: "ref", name: "Bool" },
      actual: result(type(ts("Bool"))),
    },
    {
      expected: { type: "ref", name: "Bool" },
      actual: result(type(ts("(Bool)"))),
    },
    {
      expected: {
        type: "arrow",
        from: { type: "ref", name: "A" },
        to: { type: "ref", name: "B" },
      },
      actual: result(arrow(() => type)(ts("A->B"))),
    },
    {
      expected: {
        type: "arrow",
        from: { type: "ref", name: "A" },
        to: {
          type: "arrow",
          from: { type: "ref", name: "B" },
          to: { type: "ref", name: "C" },
        },
      },
      actual: result(type(ts("A->B->C"))),
    },
    {
      expected: {
        type: "arrow",
        from: { type: "ref", name: "B" },
        to: { type: "ref", name: "C" },
      },
      actual: result(type(ts("B->C"))),
    },
    {
      expected: {
        type: "arrow",
        from: { type: "ref", name: "A" },
        to: {
          type: "arrow",
          from: { type: "ref", name: "B" },
          to: { type: "ref", name: "C" },
        },
      },
      actual: result(arrow(() => type)(ts("A->(B->C)"))),
    },
    {
      expected: {
        type: "arrow",
        from: {
          type: "arrow",
          from: { type: "ref", name: "A" },
          to: { type: "ref", name: "B" },
        },
        to: { type: "ref", name: "C" },
      },
      actual: resultC(arrow(() => type)(ts("(A->B)->C"))),
    },

    {
      expected: {
        type: "arrow",
        from: {
          type: "arrow",
          from: { type: "ref", name: "A" },
          to: { type: "ref", name: "B" },
        },
        to: {
          type: "arrow",
          from: { type: "ref", name: "C" },
          to: { type: "ref", name: "D" },
        },
      },
      actual: result(arrow(() => type)(ts("(A->B)->(C->D)"))),
    },
  ];

  return {
    name: "parser",
    tests: parserTests,
  };
}

function GetUtilTestSuite() {
  const file = `abcdefghijklmnopqrstuvwxyz\nabcdefghijklmnopqrstuvwxyz\nabcdefghijklmnopqrstuvwxyz\n`;

  const utilTests = [
    {
      expected: { line: 0, col: 0 },
      actual: indexToLineCol(file, 0),
    },
    {
      expected: { line: 0, col: 5 },
      actual: indexToLineCol(file, 5),
    },
    {
      expected: { line: 1, col: 0 },
      actual: indexToLineCol(file, 27),
    },
    {
      expected: { line: 1, col: 3 },
      actual: indexToLineCol(file, 30),
    },
  ];

  return {
    name: "util",
    tests: utilTests,
  };
}

function RunAllTests() {
  let suites = [GetParserTestSuite(), GetUtilTestSuite()];

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
