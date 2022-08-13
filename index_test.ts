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

const result = (x: Result) => x.type == "outputvalue" && x.value;

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
      expected: { type: "lam", name: "x", body: { type: "ref", name: "t" } },
      actual: result(abstraction(() => term)(ts("λx.t"))),
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
        body: { type: "lam", name: "f", body: { type: "ref", name: "t" } },
      },
      actual: result(term(ts("λt. λf. t"))),
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
    // {
    //   expected: {
    //     type: "lam",
    //     name: "z",
    //     body: {
    //       type: "lam",
    //       name: "x",
    //       body: {
    //         type: "lam",
    //         name: "y",
    //         body: {
    //           type: "app",
    //           name: { type: "ref", name: "x" },
    //           arg: {
    //             type: "app",
    //             name: { type: "ref", name: "y" },
    //             arg: { type: "ref", name: "z" },
    //           },
    //         },
    //       },
    //     },
    //   },
    //   actual: result(term(ts("λz. λx. λy. x (y (z))"))),
    // },
    {
      expected: {
        type: "def",
        name: "id",
        term: { type: "lam", name: "x", body: { type: "ref", name: "x" } },
      },
      actual: result(definition(ts("func id = λx. x"))),
    },
    {
      expected: { type: "ref", name: "ex2" },
      actual: result(reference(ts("ex2"))),
    },
  ];

  return {
    name: "parser",
    tests: parserTests,
  };
}

function RunAllTests() {
  let suites = [GetParserTestSuite()];

  let passed = 0;
  let total = 0;
  for (const s of suites) {
    for (let i = 0; i < s.tests.length; i++) {
      const t = s.tests[i];
      if (!_.isEqual(t.expected, t.actual)) {
        console.log(
          `failed: ${s.name} test ${i} expected ${JSON.stringify(
            t.expected
          )}; got ${JSON.stringify(t.actual)}`
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

const src = `// Package bool contains an implementation of Church booleans.
package bool

// The terms tru and fls can be viewed as representing the boolean values
// “true” and “false,” in the sense that we can use these terms to perform the
// operation of testing the truth of a boolean value. [quote from TAPL]
func tru = λt. λf. t
func fls = λt. λf. f

// test takes two arguments and chooses the first (if b is tru) or the second
// (if b is fls).
func test = λb. λv. λw. (b(v))(w)

// and is a function that, given two boolean values b and c, returns c if b is
// tru and fls if b is fls; thus and b c yields tru if both b and c are tru
// and fls if either b or c is fls. [quote from TAPL]
func and = λb. λc. b(c)(fls)

func ex2 = and(tru)(tru) // -> (λt. λf. t)

func ex3 = and(tru)(fls) // -> (λt. λf. f)

func main = test(ex2)(fls)(tru) // should be fls
`;

const t = parseFile(s(src));

if (t.type == "parseerror") {
  const lc = indexToLineCol(src, t.idx);
  console.log(`error at line ${lc.line} col ${lc.col}`);
}

// console.log(util.inspect(t, { showHidden: false, depth: null, colors: true }));

// const t = term(ts("λt. λf. t"));
// console.log(util.inspect(t, { showHidden: false, depth: null, colors: true }));
