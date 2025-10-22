import { describe, expect, test } from "vitest";
import {
  parseErrorDiagnostic,
  Stream,
  Result,
  char,
  bind,
  lspc,
} from "./parser";
import {
  abstraction,
  caseStatement,
  expression,
  identifier,
  identifier2,
  ifStatement,
  parenthesis,
  resync,
  serialise,
  strip,
} from "./pratt";

export const ts = (s: string): Stream => ({
  src: s,
  idx: 0,
});

export const result = <T>(x: Result<T>) => {
  if (x._ == "parseerror") {
    const msg = parseErrorDiagnostic(x);
    throw msg;
  } else {
    return x.value;
  }
};

const term = lspc(expression(0));

const st = (s: string): string => serialise(strip(result(term(ts(s)))));

const success = <T>(x: Result<T>) => x._ == "outputvalue";

describe("pratt", () => {
  test("should parse lambda body greedily", () => {
    const src = `λn n(λp Nat)`;
    const t = term({ src, idx: 0 });
    if (t._ == "parseerror") {
      throw parseErrorDiagnostic(t);
    }
    // Expect the parser to consume the input.
    expect(t.stream.idx).toBe(src.length);
  });

  test("should return an error node for unparseable terms", () =>
    expect(serialise(strip(result(identifier2(ts("&")))))).toBe(
      "ParseError(expected identifier; got &)"
    ));

  test("should return an error node for unparseable subtrees", () =>
    expect(st("λn &")).toBe(`Abs("n", ParseError(expected term; got &))`));

  test("should parse identifier", () =>
    expect(result(identifier(ts("aaabbb")))).toStrictEqual("aaabbb"));

  test("should parse identifier with upper case", () =>
    expect(result(identifier(ts("Abc")))).toStrictEqual("Abc"));

  test("should not parse identifier starting with numeral", () =>
    expect(success(identifier(ts("0abc")))).toStrictEqual(false));

  test("should parse identifier ending with numeral", () =>
    expect(result(identifier(ts("abc0")))).toStrictEqual("abc0"));

  test("should parse identifier with underscore", () =>
    expect(result(identifier(ts("a_b")))).toStrictEqual("a_b"));

  test("should parse parenthesis", () =>
    expect(success(parenthesis(char("a"))(ts("(a)")))).toStrictEqual(true));

  test("should parse lambda abstraction", () =>
    expect(serialise(strip(result(abstraction(ts("λx t")))))).toBe(
      `Abs("x", Ref("t"))`
    ));

  test("should parse true", () =>
    expect(st("λt λf t")).toBe(`Abs("t", Abs("f", Ref("t")))`));

  test("should parse application with space", () =>
    expect(st("f ( x )")).toBe(`App(Ref("f"), Ref("x"))`));

  test("should parse application within application", () =>
    expect(st("f(x(y))")).toBe(`App(Ref("f"), App(Ref("x"), Ref("y")))`));

  test("should parse bracketed application", () =>
    expect(st("x (y (z))")).toBe(`App(Ref("x"), App(Ref("y"), Ref("z")))`));

  test("should include origins in function application", () =>
    expect(serialise(result(term(ts("f(x)"))))).toBe(
      `App(Orig(0, 1, Ref("f")), Orig(2, 3, Ref("x")))`
    ));

  test("should parse term", () =>
    expect(st("λz λx λy x (y (z))")).toBe(
      `Abs("z", Abs("x", Abs("y", App(Ref("x"), App(Ref("y"), Ref("z"))))))`
    ));

  test("should parse reference", () => expect(st("ex2")).toBe(`Ref("ex2")`));

  test("should parse reference surrounded by spaces", () =>
    expect(st(`   r `)).toBe(`Ref("r")`));

  test("should parse type reference", () =>
    expect(serialise(strip(result(term(ts("Bool")))))).toBe(`Ref("Bool")`));

  test("should parse reference in parenthesis", () =>
    expect(serialise(strip(result(term(ts("(Bool)")))))).toBe(`Ref("Bool")`));

  test("should parse integer addition binary operator", () =>
    expect(st("1+2")).toBe(`IntPlus(IntLit(1), IntLit(2))`));

  test("should parse integer addition with left associativity", () =>
    // 1+2+3 === (1+2)+3
    expect(st("1+2+3")).toBe(
      `IntPlus(IntPlus(IntLit(1), IntLit(2)), IntLit(3))`
    ));

  test("should parse integer subtraction binary operator", () =>
    expect(st("1-2")).toBe(`IntSub(IntLit(1), IntLit(2))`));

  test("should parse integer subtraction with left associativity", () =>
    // 1-2-3 === (1-2)-3
    expect(st("1-2-3")).toBe(
      `IntSub(IntSub(IntLit(1), IntLit(2)), IntLit(3))`
    ));

  test("should parse integer multiplication binary operator", () =>
    expect(st("1*2")).toBe(`IntMul(IntLit(1), IntLit(2))`));

  test("should parse integer multiplication with left associativity", () =>
    // 1*2*3 === (1*2)*3
    expect(st("1*2*3")).toBe(
      `IntMul(IntMul(IntLit(1), IntLit(2)), IntLit(3))`
    ));

  test("should parse integer multiplication with higher associativity than addition", () =>
    // 1+2*3 === 1+(2*3)
    expect(st("1+2*3")).toBe(
      `IntPlus(IntLit(1), IntMul(IntLit(2), IntLit(3)))`
    ));

  test("should parse integer multiplication with higher associativity than addition 2", () =>
    // 1*2+3 === (1*2)+3
    expect(st("1*2+3")).toBe(
      `IntPlus(IntMul(IntLit(1), IntLit(2)), IntLit(3))`
    ));

  test("should parse parenthesis with the highest precedence", () =>
    expect(st("1*(2+3)")).toBe(
      `IntMul(IntLit(1), IntPlus(IntLit(2), IntLit(3)))`
    ));

  test("should parse integer division binary operator", () =>
    expect(st("1/2")).toBe(`IntDiv(IntLit(1), IntLit(2))`));

  test("should parse multiple parenthesis", () =>
    expect(st("((1))")).toBe(`IntLit(1)`));

  test("should parse unary negation", () =>
    expect(st("-1")).toBe(`IntNeg(IntLit(1))`));

  test("should parse multiple unary negation", () =>
    expect(st("--1")).toBe(`IntNeg(IntNeg(IntLit(1)))`));

  test("should parse unary negation with parenthesis", () =>
    expect(st("-(-1)")).toBe(`IntNeg(IntNeg(IntLit(1)))`));

  test("should parse function composition with right associativity", () =>
    // f . g . h === f . (g . h)
    expect(st("f . g . h")).toBe(`Comp(Ref("f"), Comp(Ref("g"), Ref("h")))`));

  test("should parse function application", () =>
    expect(st("f(x)")).toBe(`App(Ref("f"), Ref("x"))`));

  test("should parse function application with multiple arguments", () =>
    // f(x)(y) === (f(x))(y)
    expect(st("f(x)(y)")).toBe(`App(App(Ref("f"), Ref("x")), Ref("y"))`));

  test("should parse function application with multiple arguments using commas", () =>
    // f(x,y) === (f(x))(y)
    expect(st("f(x,y)")).toBe(`App(App(Ref("f"), Ref("x")), Ref("y"))`));

  test("should parse function application with three comma-separated arguments", () =>
    // This is the same as the previous test.
    expect(st("f(x,y,z)")).toBe(
      `App(App(App(Ref("f"), Ref("x")), Ref("y")), Ref("z"))`
    ));

  test("should parse function application with additional parens", () =>
    expect(st("(b(v))(w)")).toBe(`App(App(Ref("b"), Ref("v")), Ref("w"))`));

  test("should parse empty list", () => expect(st("[]")).toBe(`Nil()`));

  test("should parse list literal", () =>
    // [1,2,3]
    expect(st("[1,2,3]")).toBe(
      `Cons(IntLit(1), Cons(IntLit(2), Cons(IntLit(3), Nil())))`
    ));

  test("should parse arrow", () =>
    expect(st("A->B")).toBe(`Pi("", Ref("A"), Ref("B"))`));

  test("should parse arrow operator with right associativity", () =>
    // a -> b -> c === a -> (b -> c)
    expect(st("a->b->c")).toBe(`Pi("", Ref("a"), Pi("", Ref("b"), Ref("c")))`));

  test("should parse arrow with left bracketing", () =>
    expect(st("A->(B->C)")).toBe(
      `Pi("", Ref("A"), Pi("", Ref("B"), Ref("C")))`
    ));

  test("should parse arrow with right bracketing", () =>
    expect(st("(A->B)->C")).toStrictEqual(
      `Pi("", Pi("", Ref("A"), Ref("B")), Ref("C"))`
    ));

  test("should parse arrow with multiple bracketing", () =>
    expect(st("(A->B)->(C->D)")).toStrictEqual(
      `Pi("", Pi("", Ref("A"), Ref("B")), Pi("", Ref("C"), Ref("D")))`
    ));

  test("should parse arrow ending with star", () =>
    expect(st("A->*")).toBe(`Pi("", Ref("A"), Star())`));

  test("should parse arrow type * -> *", () =>
    expect(st(`* -> *`)).toBe(`Pi("", Star(), Star())`));

  test("should parse type annotation", () =>
    // a:A:B === (a:A):B
    expect(st("a:A:B")).toBe(`Ann(Ann(Ref("a"), Ref("A")), Ref("B"))`));

  test("should parse type annotation with high precedence", () =>
    // a:Int + b:Int === (a:Int) + (b:Int)
    expect(st("a:Int+b:Int")).toBe(
      `IntPlus(Ann(Ref("a"), Ref("Int")), Ann(Ref("b"), Ref("Int")))`
    ));

  test("should parse list indexing operator", () =>
    expect(st("a[i]")).toBe(`Idx(Ref("a"), Ref("i"))`));

  test("should parse list concatenation operator with left associativity", () =>
    expect(st("as++bs++cs")).toBe(`Cat(Cat(Ref("as"), Ref("bs")), Ref("cs"))`));

  test("should parse greater-than binary operator", () =>
    expect(st("a>b")).toBe(`Gt(Ref("a"), Ref("b"))`));

  test("should parse greater-than-or-equal binary operator", () =>
    expect(st("a>=b")).toBe(`Gte(Ref("a"), Ref("b"))`));

  test("should parse less-than binary operator", () =>
    expect(st("a<b")).toBe(`Lt(Ref("a"), Ref("b"))`));

  test("should parse less-than-or-equal binary operator", () =>
    expect(st("a<=b")).toBe(`Lte(Ref("a"), Ref("b"))`));

  test("should parse less-than and greater-than with the same precedence", () =>
    // a<b>c === (a<b)>c
    expect(st("a<b>c")).toBe(`Gt(Lt(Ref("a"), Ref("b")), Ref("c"))`));

  test("should parse logical equals binary operator", () =>
    expect(st("a==b")).toBe(`Eq(Ref("a"), Ref("b"))`));

  test("should parse logical not equals binary operator", () =>
    expect(st("a!=b")).toBe(`Neq(Ref("a"), Ref("b"))`));

  test("should parse logical and binary operator", () =>
    expect(st("a&&b")).toBe(`And(Ref("a"), Ref("b"))`));

  test("should parse logical or binary operator", () =>
    expect(st("a||b")).toBe(`Or(Ref("a"), Ref("b"))`));

  test("should parse logical and at a higher precedence than logical or", () =>
    expect(st("a||b&&c")).toBe(`Or(Ref("a"), And(Ref("b"), Ref("c")))`));

  test("should parse if statement", () => {
    expect(st("if x then y else z")).toBe(
      `If(Ann(Ref("x"), Ref("Bool")), Ref("y"), Ref("z"))`
    );
  });

  test("should parse multiline if statement", () =>
    expect(
      serialise(
        strip(
          result(
            term(
              ts(`if x then
      y
    else
      z
    `)
            )
          )
        )
      )
    ).toBe(`If(Ann(Ref("x"), Ref("Bool")), Ref("y"), Ref("z"))`));

  test("should return an error node for unparseable if statement", () =>
    expect(st("if = then y else z")).toBe(
      `If(Ann(ParseError(expected term; got =), Ref("Bool")), Ref("y"), Ref("z"))`
    ));

  test("should return error nodes for unparseable if statement", () =>
    expect(st("if = then = else =")).toBe(
      `If(Ann(ParseError(expected term; got =), Ref("Bool")), ParseError(expected term; got =), ParseError(expected term; got =))`
    ));

  test("should return error nodes for empty if statement", () =>
    expect(st("if  then  else ")).toBe(
      `If(Ann(ParseError(expected term; got ), Ref("Bool")), ParseError(expected term; got ), ParseError(expected term; got ))`
    ));

  test("should return an error node for then keyword if a term was expected", () =>
    // When parsing the condition of an if statement, if it's empty we'll
    // immediately hit "then" so make sure this is parsed correctly as a
    // missing term.
    expect(st(" then y else z")).toBe(`ParseError(expected term; got )`));

  test("should return an error node for else keyword if a term was expected", () =>
    expect(st(" else z")).toBe(`ParseError(expected term; got )`));

  test("should return an error node for if statement with empty condition", () =>
    expect(st("if then y else z")).toBe(
      `If(Ann(ParseError(expected term; got ), Ref("Bool")), Ref("y"), Ref("z"))`
    ));

  test("should return an error node for unparseable true branch", () =>
    expect(st("if x then @ else z")).toBe(
      `If(Ann(Ref("x"), Ref("Bool")), ParseError(expected term; got @), Ref("z"))`
    ));

  test("should return an error node for unparseable false branch", () =>
    expect(st("if x then y else @")).toBe(
      `If(Ann(Ref("x"), Ref("Bool")), Ref("y"), ParseError(expected term; got @))`
    ));

  test("should parse type constructor", () =>
    expect(serialise(strip(result(term(ts("List(Nat)")))))).toBe(
      `App(Ref("List"), Ref("Nat"))`
    ));

  test("should parse type constructor on the left of an arrow", () =>
    expect(st("List(Nat)->Nat")).toBe(
      `Pi("", App(Ref("List"), Ref("Nat")), Ref("Nat"))`
    ));

  test("should parse app with parenthesis on the left", () =>
    expect(st("(x)((y)(z))")).toBe(`App(Ref("x"), App(Ref("y"), Ref("z")))`));

  test("should parse arrow with lots of parenthesis", () =>
    expect(st("(x)((y)(z))->(x)")).toBe(
      `Pi("", App(Ref("x"), App(Ref("y"), Ref("z"))), Ref("x"))`
    ));

  test("pi: should parse named pi types", () => {
    const parser = term;
    const res = parser(ts("(A:*) -> A"));
    expect(serialise(strip(result(res)))).toBe(`Pi("A", Star(), Ref("A"))`);
  });

  test("pi: should expose ParseError for bad from annotation", () => {
    const parser = term;
    const res = parser(ts("(A:(&)) -> A"));
    expect(serialise(strip(result(res)))).toBe(
      `Pi("A", ParseError(expected term; got &), Ref("A"))`
    );
  });

  test("pi: should parse multiple named pi types", () =>
    expect(st("(A:*) -> (B:*) -> (a:A) -> (b:B) -> b")).toBe(
      `Pi("A", Star(), Pi("B", Star(), Pi("a", Ref("A"), Pi("b", Ref("B"), Ref("b")))))`
    ));

  test("should parse case", () => {
    const src = `case n of
          |  zero => true
          |  succ => false`;
    const ast = strip(result(term(ts(src))));
    expect(serialise(ast)).toBe(
      `Case(Par("n"),[Branch(Identifier("zero"), Ref("true")),Branch(Identifier("succ"), Ref("false"))])`
    );
  });

  test("should parse case with annotation", () => {
    const src = `(case n of
          |  zero => true
          |  succ => false
          ):Bool`;
    const ast = strip(result(term(ts(src))));
    expect(serialise(ast)).toBe(
      `Ann(Case(Par("n"),[Branch(Identifier("zero"), Ref("true")),Branch(Identifier("succ"), Ref("false"))]), Ref("Bool"))`
    );
  });

  test("should parse nested case", () => {
    const src = `case n of
          | zero => (case m of
            | zero => false
            | succ => true)
          | succ => (case m of
            | zero => false
            | succ => lt(n.x,m.x))`;
    const ast = strip(result(term(ts(src))));
    expect(serialise(ast)).toBe(
      `Case(Par("n"),[Branch(Identifier("zero"), Case(Par("m"),[Branch(Identifier("zero"), Ref("false")),Branch(Identifier("succ"), Ref("true"))])),Branch(Identifier("succ"), Case(Par("m"),[Branch(Identifier("zero"), Ref("false")),Branch(Identifier("succ"), App(App(Ref("lt"), Ref("n.x")), Ref("m.x")))]))])`
    );
  });

  test("should parse empty case branch", () => {
    // The body of a case branch can be empty (for example when the user
    // hasn't finished typing it) in this case the parser encounters a bar
    // indicating the next case branch. Make sure the parser doesn't consume
    // the bar and returns an empty error node for this case branch.
    const src = `
          | succ => zero`;
    const ast = strip(result(term(ts(src))));
    expect(serialise(ast)).toBe("ParseError(expected term; got )");
  });

  test("should parse partial case branch", () => {
    const src = `case b of
          | zero =>
          | succ => zero`;
    const ast = strip(result(caseStatement(ts(src))));
    expect(serialise(ast)).toBe(
      `Case(Par("b"),[Branch(Identifier("zero"), ParseError(expected term; got )),Branch(Identifier("succ"), Ref("zero"))])`
    );
  });

  test("should parse case with empty final branch", () => {
    const src = `case n of
          | zero => zero
          | succ => `;
    const ast = strip(result(term(ts(src))));
    expect(serialise(ast)).toBe(
      `Case(Par("n"),[Branch(Identifier("zero"), Ref("zero")),Branch(Identifier("succ"), ParseError(expected term; got ))])`
    );
  });

  test("should parse empty string literal", () => {
    const src = `""`;
    const ast = strip(result(term(ts(src))));
    expect(serialise(ast)).toBe(`StringLit("")`);
  });

  test("should parse string literal", () => {
    const src = `"hello"`;
    const ast = strip(result(term(ts(src))));
    expect(serialise(ast)).toBe(`StringLit("hello")`);
  });

  test("should parse let expression", () => {
    const ast = strip(result(term(ts("let g = f(x) in h(g,g)"))));
    expect(serialise(ast)).toBe(
      `Let(Identifier("g"), App(Ref("f"), Ref("x")), App(App(Ref("h"), Ref("g")), Ref("g")))`
    );
  });

  test("should allow ParseError on the rhs of App", () => {
    const src = `f("hello )`;
    const ast = strip(result(term(ts(src))));
    expect(serialise(ast)).toBe(
      `App(Ref("f"), ParseError(failed to parse string literal))`
    );
  });

  test("should parse app with string literal", () => {
    const src = `elimIO(println("hello))`;
    const ast = strip(result(term(ts(src))));
    expect(serialise(ast)).toBe(
      `App(Ref("elimIO"), App(Ref("println"), ParseError(failed to parse string literal)))`
    );
  });

  test("should skip unparsable areas", () => {
    const src = `######)one`;
    // resync should skip past all the hashes and successfully parse a closing
    // parenthesis.
    const r = result(bind(resync, (_) => char(")"))(ts(src)));
    expect(r).toBe(`)`);
  });

  test("should parse star", () => {
    const src = `*`;
    const tm = strip(result(term(ts(src))));
    expect(serialise(tm)).toBe(`Star()`);
  });

  test("should allow star as an annotation", () => {
    const src = `x:*`;
    const tm = strip(result(term(ts(src))));
    expect(serialise(tm)).toBe(`Ann(Ref("x"), Star())`);
  });

  test("should allow star with arrows", () => {
    const src = `* -> *`;
    const tm = strip(result(term(ts(src))));
    expect(serialise(tm)).toBe(`Pi("", Star(), Star())`);
  });

  test("should parse simple pi type with named parameter", () => {
    const src = `(b:Bool) -> *`;
    const tm = strip(result(term(ts(src))));
    expect(serialise(tm)).toBe(`Pi("b", Ref("Bool"), Star())`);
  });

  test("should parse simple pi type that's used dependently", () => {
    const src = `(a:A) -> B(a)`;
    const tm = strip(result(term(ts(src))));
    expect(serialise(tm)).toBe(`Pi("a", Ref("A"), App(Ref("B"), Ref("a")))`);
  });

  test("should parse annotation containing type constructor", () => {
    const src = `t:P(true)`;
    const tm = strip(result(term(ts(src))));
    expect(serialise(tm)).toBe(`Ann(Ref("t"), App(Ref("P"), Ref("true")))`);
  });

  test("should parse pi types correctly", () => {
    const src = `(t:P(true)) -> P(t)`;
    const tm = strip(result(term(ts(src))));
    expect(serialise(tm)).toBe(
      `Pi("t", App(Ref("P"), Ref("true")), App(Ref("P"), Ref("t")))`
    );
  });

  test("should parse more compliated pi types correctly", () => {
    const src = `(b:Bool) -> (P:((x:Bool) -> *)) -> (t:P(true)) -> (f:P(false)) -> P(b)`;
    const tm = strip(result(term(ts(src))));
    expect(serialise(tm)).toBe(
      `Pi("b", Ref("Bool"), Pi("P", Pi("x", Ref("Bool"), Star()), Pi("t", App(Ref("P"), Ref("true")), Pi("f", App(Ref("P"), Ref("false")), App(Ref("P"), Ref("b"))))))`
    );
  });
});
