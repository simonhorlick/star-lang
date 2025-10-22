import { describe, expect, test } from "vitest";
import {
  ASTNode,
  parsePackage,
  stripAST,
  parseLineComment,
  definition,
  parseFile,
  Def,
  adt,
} from "./ast";
import {
  bind,
  char,
  many,
  parseErrorDiagnostic,
  Stream,
  Result,
  lspc,
} from "./parser";
import {
  abstraction,
  caseStatement,
  expression,
  identifier,
  identifier2,
  identifier2str,
  listLiteral,
  parenthesis,
  pi,
  resync,
  serialise,
} from "./pratt";
import { strip } from "./pratt";

export const ts = (s: string): Stream => ({
  src: `parsed${s}`,
  idx: 6,
});

// deserialise term and serialise the result.
const st = (s: string): string => serialise(strip(result(term(ts(s)))));

export const result = <T>(x: Result<T>) => {
  if (x._ == "parseerror") {
    const msg = parseErrorDiagnostic(x);
    throw msg;
  } else {
    return x.value;
  }
};

export function serialiseAST(n: ASTNode): string {
  switch (n._) {
    case "pkg":
      return `Pkg(${n.name})`;
    case "com":
      return `Com(${n.text})`;
    case "def":
      return `Def(name=${n.name}, term=${serialise(n.term)})`;
    case "adt":
      return `ADT(${identifier2str(n.name)}, constructors=${n.constructors
        .map(
          (c) =>
            `${identifier2str(c.name)}(${c.args
              .map((a) => `${a.name}:${serialise(a.type)}`)
              .join(",")})${c.typ ? `:${serialise(c.typ)}` : ""}`
        )
        .join("|")})`;
    case "err":
      return `Err(${n.msg})`;
    case "orig2":
      return serialiseAST(n.child);
    case "sp":
    case "nl":
      return "";
  }
}

const success = <T>(x: Result<T>) => x._ == "outputvalue";

const resultC = <T>(x: Result<T>) => {
  if (x._ == "parseerror") {
    throw x.error;
  } else {
    if (x.stream.idx != x.stream.src.length) {
      throw "stream not consumed";
    }
    return x.value;
  }
};

const term = lspc(expression(0));
const type = term;

describe("ast", () => {
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

  test("should parse package", () =>
    expect(stripAST(result(parsePackage(ts(`package abc`))))).toStrictEqual({
      _: "pkg",
      name: "abc",
    }));

  test("should parse multi-line comments", () =>
    expect(
      result(many(parseLineComment)(ts("// comment\n// comment 2")))
    ).toStrictEqual([
      { _: "orig2", start: 6, end: 17, child: { _: "com", text: " comment" } },
      {
        _: "orig2",
        start: 17,
        end: 29,
        child: { _: "com", text: " comment 2" },
      },
    ]));

  test("should parse comment at EOF", () =>
    expect(result(parseLineComment(ts("// comment")))).toStrictEqual({
      _: "orig2",
      start: 6,
      end: 16,
      child: {
        _: "com",
        text: " comment",
      },
    }));

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

  test("should parse function application", () =>
    expect(st("f(x)")).toBe(`App(Ref("f"), Ref("x"))`));

  // want to parse `f(x)(y)` as the following tree:
  //
  //      ap
  //     /  \
  //    ap   y
  //   /  \
  //  f    x
  //
  // test("should parse function application with two arguments", () =>
  //   expect(st("f(x)(y)")).toBe(`App(App(Ref("f"), Ref("x")), Ref("y"))`));

  test("should parse function application with two comma-separated arguments", () =>
    // This is the same as the previous test.
    expect(st("f(x,y)")).toBe(`App(App(Ref("f"), Ref("x")), Ref("y"))`));

  // Should we allow this syntax, or enforce the comma syntax?
  // test("should parse function application with three arguments", () =>
  //   expect(st("f(x)(y)(z)")).toBe(
  //     `App(App(App(Ref("f"), Ref("x")), Ref("y")), Ref("z"))`
  //   ));

  test("should parse function application with three comma-separated arguments", () =>
    // This is the same as the previous test.
    expect(st("f(x,y,z)")).toBe(
      `App(App(App(Ref("f"), Ref("x")), Ref("y")), Ref("z"))`
    ));

  test("should parse function application with additional parens", () =>
    expect(st("(b(v))(w)")).toBe(`App(App(Ref("b"), Ref("v")), Ref("w"))`));

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
      `App(Orig(6, 7, Ref("f")), Orig(8, 9, Ref("x")))`
    ));

  test("should parse term", () =>
    expect(st("λz λx λy x (y (z))")).toBe(
      `Abs("z", Abs("x", Abs("y", App(Ref("x"), App(Ref("y"), Ref("z"))))))`
    ));

  test("should parse reference", () => expect(st("ex2")).toBe(`Ref("ex2")`));

  test("should parse type reference", () =>
    expect(serialise(strip(result(type(ts("Bool")))))).toBe(`Ref("Bool")`));

  test("should parse reference in parenthesis", () =>
    expect(serialise(strip(result(type(ts("(Bool)")))))).toBe(`Ref("Bool")`));

  test("should parse arrow", () =>
    expect(st("A->B")).toBe(`Pi("", Ref("A"), Ref("B"))`));

  test("should parse arrow with correct precedence", () =>
    expect(serialise(strip(result(type(ts("A->B->C")))))).toBe(
      `Pi("", Ref("A"), Pi("", Ref("B"), Ref("C")))`
    ));

  test("should parse arrow type", () =>
    expect(serialise(strip(result(type(ts("B->C")))))).toBe(
      `Pi("", Ref("B"), Ref("C"))`
    ));

  test("should parse arrow with bracketing", () =>
    expect(st("A->(B->C)")).toBe(
      `Pi("", Ref("A"), Pi("", Ref("B"), Ref("C")))`
    ));

  test("should parse arrow with bracketing", () =>
    expect(serialise(strip(resultC(term(ts("(A->B)->C")))))).toStrictEqual(
      `Pi("", Pi("", Ref("A"), Ref("B")), Ref("C"))`
    ));

  test("should parse arrow with bracketing", () =>
    expect(st("(A->B)->(C->D)")).toStrictEqual(
      `Pi("", Pi("", Ref("A"), Ref("B")), Pi("", Ref("C"), Ref("D")))`
    ));

  test("should parse empty list", () => expect(st("[]")).toBe(`Nil()`));

  test("should parse list literal with integers", () =>
    expect(st("[1,2,3]")).toBe(
      `Cons(IntLit(1), Cons(IntLit(2), Cons(IntLit(3), Nil())))`
    ));

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
    expect(serialise(strip(result(type(ts("List(Nat)")))))).toBe(
      `App(Ref("List"), Ref("Nat"))`
    ));

  test("should parse type constructor on the left of an arrow", () =>
    expect(st("List(Nat)->Nat")).toBe(
      `Pi("", App(Ref("List"), Ref("Nat")), Ref("Nat"))`
    ));

  test("should parse arrow with lots of parenthesis", () =>
    expect(st("(x)((y)(z))->(x)")).toBe(
      `Pi("", App(Ref("x"), App(Ref("y"), Ref("z"))), Ref("x"))`
    ));

  test("pi: should parse named pi types", () => {
    const parser = pi;
    const res = parser(ts("ΠA:* A"));
    expect(serialise(strip(result(res)))).toBe(`Pi("A", Star(), Ref("A"))`);
  });

  test("pi: should expose ParseError for bad from annotation", () => {
    const parser = pi;
    const res = parser(ts("ΠA:(&) A"));
    expect(serialise(strip(result(res)))).toBe(
      `Pi("A", ParseError(expected term; got &), Ref("A"))`
    );
  });

  test("pi: should parse multiple named pi types", () =>
    expect(st("ΠA:* ΠB:* Πa:A Πb:B b")).toBe(
      `Pi("A", Star(), Pi("B", Star(), Pi("a", Ref("A"), Pi("b", Ref("B"), Ref("b")))))`
    ));

  test("should parse definition containing list literal", () => {
    const ast = stripAST(
      result(definition(ts("func abc:List(Nat) = zero\n\n")))
    );
    if (ast._ != "def") {
      throw `unexpected ${ast._}`;
    }
    expect(serialise(ast.term.type)).toBe(`App(Ref("List"), Ref("Nat"))`);
    expect(serialise(ast.term.term)).toBe(`Ref("zero")`);
  });

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

  test("should parse definition containing partial case", () => {
    const ast = parseFile(
      ts(`func abc:Bool->Bool = λn case n of
      | zero => zero
      | succ =>
      func def:Nat = zero
      `)
    );
    if (ast._ != "outputvalue") {
      throw `unexpected ${ast._}`;
    }

    expect(serialiseAST(stripAST(ast.value.content[0]))).toBe(
      `Def(name=abc, term=Ann(Abs("n", Case(Par("n"),[Branch(Identifier("zero"), Ref("zero")),Branch(Identifier("succ"), ParseError(expected term; got ))])), Pi("", Ref("Bool"), Ref("Bool"))))`
    );
    expect(serialiseAST(stripAST(ast.value.content[1]))).toBe(
      `Def(name=def, term=Ann(Ref("zero"), Ref("Nat")))`
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

  test("should parse definition containing string literal", () => {
    const ast = stripAST(result(definition(ts(`func abc:String = ""`))));
    if (ast._ != "def") {
      throw `unexpected ${ast._}`;
    }
    expect(serialise(ast.term.type)).toBe(`Ref("String")`);
    expect(serialise(ast.term.term)).toBe(`StringLit("")`);
  });

  test("should include origins for type annotations of definitions", () => {
    const ast = result(definition(ts(`func abc:String = ""`)));
    if (ast._ != "def") {
      throw `unexpected ${ast._}`;
    }
    // Here there are two origins - one for the term and one for the Ref.
    expect(serialise(ast.term.type)).toBe(
      `Origin(15, 21, Origin(15, 21, Ref("String")))`
    );
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

  test("should resync to next keyword", () => {
    const src = `junkherefunc x:Nat = zero`;
    // skip all the junk then parse a definition.
    const ast = stripAST(result(bind(resync, (_) => definition)(ts(src))));
    expect(serialiseAST(ast)).toBe(
      `Def(name=x, term=Ann(Ref("zero"), Ref("Nat")))`
    );
  });

  test("should parse simple pi type", () => {
    const src = `
    Πb:Bool
     *
    `;
    const tm = strip(result(type(ts(src))));
    expect(serialise(tm)).toBe(`Pi("b", Ref("Bool"), Star())`);
  });

  test("should parse pi types correctly", () => {
    const src = `Πb:Bool ΠP:(Πx:Bool *) Πt:P(true) Πf:P(false) P(b)`;
    const tm = strip(result(type(ts(src))));
    expect(serialise(tm)).toBe(
      `Pi("b", Ref("Bool"), Pi("P", Pi("x", Ref("Bool"), Star()), Pi("t", App(Ref("P"), Ref("true")), Pi("f", App(Ref("P"), Ref("false")), App(Ref("P"), Ref("b"))))))`
    );
  });

  test("should parse pi types in function type", () => {
    const src = `func bool_match : Πb:Bool ΠP:(Πx:Bool *) Πt:P(true) Πf:P(false) P(b) =
    λb λP λt λf b(P,t,f)
`;
    const ast = stripAST(result(definition(ts(src)))) as Def;
    // const ast = result(definition(ts(src))) as Def;

    // console.log(`checking for parse errors in tree`);
    // const errs = foldTreeCtx(
    //   (acc, curr) => {
    //     if (curr.term._ !== "err") return acc;
    //     const err = {
    //       msg: curr.term.msg,
    //       start: curr.start ?? 0,
    //       end: curr.end ?? 0,
    //     } as TypecheckError;
    //     console.log(printDiagnostic(src, err));
    //     return acc.concat(err);
    //   },
    //   [] as TypecheckError[],
    //   ast.term
    // );

    expect(serialiseAST(ast)).toBe(
      `Def(name=bool_match, term=Ann(Abs("b", Abs("P", Abs("t", Abs("f", App(App(App(Ref("b"), Ref("P")), Ref("t")), Ref("f")))))), Pi("b", Ref("Bool"), Pi("P", Pi("x", Ref("Bool"), Star()), Pi("t", App(Ref("P"), Ref("true")), Pi("f", App(Ref("P"), Ref("false")), App(Ref("P"), Ref("b"))))))))`
    );
  });

  test("should parse unannotated data types", () => {
    const ast = stripAST(result(adt(ts(`type Bool = true | false`))));
    if (ast._ != "adt") {
      throw `unexpected ${ast._}`;
    }
    expect(serialiseAST(ast)).toBe(`ADT(Bool, constructors=true()|false())`);
  });

  test("should parse data type with arguments", () => {
    const ast = stripAST(
      result(adt(ts(`type List(A *) = nil | cons(head A, tail List(A))`)))
    );
    if (ast._ != "adt") {
      throw `unexpected ${ast._}`;
    }
    expect(serialiseAST(ast)).toBe(
      `ADT(List, constructors=nil()|cons(head:Ref("A"),tail:App(Ref("List"), Ref("A"))))`
    );
  });

  test("should parse data types with annotations", () => {
    const ast = stripAST(
      result(
        adt(
          ts(
            `type List(A *) = nil:List(A) | cons(head A, tail List(A)):List(A)`
          )
        )
      )
    );
    if (ast._ != "adt") {
      throw `unexpected ${ast._}`;
    }
    expect(serialiseAST(ast)).toBe(
      `ADT(List, constructors=nil():App(Ref("List"), Ref("A"))|cons(head:Ref("A"),tail:App(Ref("List"), Ref("A"))):App(Ref("List"), Ref("A")))`
    );
  });

  // TODO: implement
  //   test("should parse data types with dependent annotations", () => {
  //     // TODO: Figure out syntax.
  //     // TODO: Need the return type to be arguments to Vector, not some other
  //     //  random type, i.e. App(Ref("Vector"), ...)
  //     const ast = stripAST(
  //       result(
  //         adt(
  //           ts(`
  //             type Vector(T ★, n Nat) =
  //               | vnil : Vector(T, 0)
  //               | ext(head T, tail Vector(T, n)) : Vector(T, succ(n))`)
  //         )
  //       )
  //     );
  //     if (ast._ != "adt") {
  //       throw `unexpected ${ast._}`;
  //     }
  //     expect(serialiseAST(ast)).toBe(`ADT(List)`);
  //   });
});
