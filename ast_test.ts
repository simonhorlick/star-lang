import { describe, expect, test } from "@jest/globals";
import {
  Abs,
  abstraction,
  App,
  application,
  arrow,
  ASTNode,
  Def,
  definition,
  identifier,
  identifier2,
  If,
  orFail,
  Par,
  parenthesis,
  ParseError,
  parseFile,
  parseLineComment,
  parsePackage,
  Pi,
  Ref,
  reference,
  resync,
  stringLiteral,
  term,
  type,
} from "./ast";
import { logFull, serialise, strip, stripAST, identifier as id } from "./check";
import {
  bind,
  char,
  either,
  many,
  many1,
  newline,
  parseErrorDiagnostic,
  pure,
  Result,
  str,
  whitespace,
} from "./parser";
import { result, ts } from "./parser_test";

export function serialiseAST(n: ASTNode): string {
  switch (n._) {
    case "pkg":
      return `Pkg(${n.name})`;
    case "com":
      return `Com(${n.text})`;
    case "def":
      return `Def(name=${n.name}, term=${serialise(n.term)})`;
    case "adt":
      return `ADT(${id(n.name)})`;
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

  test("should return an error node for unparseable terms", () => {
    expect(serialise(strip(result(identifier2(ts("&")))))).toBe(
      "ParseError(expected identifier)"
    );
  });

  test("should return an error node for unparseable subtrees", () => {
    expect(serialise(strip(result(term(ts("λn &")))))).toBe(
      'Abs("n", ParseError(expected term))'
    );
  });

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

  test("should parse identifier", () =>
    expect(result(identifier(ts("Abc")))).toStrictEqual("Abc"));

  test("should parse identifier", () =>
    expect(success(identifier(ts("0abc")))).toStrictEqual(false));

  test("should parse identifier", () =>
    expect(result(identifier(ts("abc0")))).toStrictEqual("abc0"));

  test("should parse identifier", () =>
    expect(result(identifier(ts("a_b")))).toStrictEqual("a_b"));

  test("should parse parenthesis", () =>
    expect(success(parenthesis(char("a"))(ts("(a)")))).toStrictEqual(true));

  test("should parse lambda abstraction", () =>
    expect(serialise(strip(result(abstraction(() => term)(ts("λx t")))))).toBe(
      'Abs("x", Ref(t))'
    ));

  test("should parse function application", () =>
    expect(serialise(strip(result(term(ts("f(x)")))))).toBe(
      "App(Ref(f), Ref(x))"
    ));

  // want to parse `f(x)(y)` as the following tree:
  //
  //      ap
  //     /  \
  //    ap   y
  //   /  \
  //  f    x
  //
  test("should parse function application with two arguments", () =>
    expect(serialise(strip(result(term(ts("f(x)(y)")))))).toBe(
      "App(App(Ref(f), Ref(x)), Ref(y))"
    ));

  test("should parse function application with three arguments", () =>
    expect(serialise(strip(result(term(ts("f(x)(y)(z)")))))).toBe(
      "App(App(App(Ref(f), Ref(x)), Ref(y)), Ref(z))"
    ));

  test("should parse function application with additional parens", () =>
    expect(serialise(strip(result(term(ts("(b(v))(w)")))))).toBe(
      "App(App(Ref(b), Ref(v)), Ref(w))"
    ));

  test("should parse true", () =>
    expect(serialise(strip(result(term(ts("λt λf t")))))).toBe(
      'Abs("t", Abs("f", Ref(t)))'
    ));

  test("should parse application with space", () =>
    expect(serialise(strip(result(term(ts("f ( x )")))))).toBe(
      "App(Ref(f), Ref(x))"
    ));

  test("should parse application within application", () =>
    expect(serialise(strip(result(term(ts("f(x(y))")))))).toBe(
      "App(Ref(f), App(Ref(x), Ref(y)))"
    ));

  test("should parse bracketed application", () =>
    expect(serialise(strip(result(term(ts("x (y (z))")))))).toBe(
      "App(Ref(x), App(Ref(y), Ref(z)))"
    ));

  test("should parse term", () =>
    expect(serialise(strip(result(term(ts("λz λx λy x (y (z))")))))).toBe(
      'Abs("z", Abs("x", Abs("y", App(Ref(x), App(Ref(y), Ref(z))))))'
    ));

  test("should parse reference", () =>
    expect(serialise(strip(result(term(ts("ex2")))))).toBe("Ref(ex2)"));

  test("should parse reference", () =>
    expect(serialise(strip(result(type(ts("Bool")))))).toBe("Ref(Bool)"));

  test("should parse reference in parenthesis", () =>
    expect(serialise(strip(result(type(ts("(Bool)")))))).toBe("Ref(Bool)"));

  test("should parse arrow", () =>
    expect(serialise(strip(result(term(ts("A->B")))))).toBe(
      'Pi("", Ref(A), Ref(B))'
    ));

  test("should parse arrow with correct precedence", () =>
    expect(serialise(strip(result(type(ts("A->B->C")))))).toBe(
      'Pi("", Ref(A), Pi("", Ref(B), Ref(C)))'
    ));

  test("should parse arrow type", () =>
    expect(serialise(strip(result(type(ts("B->C")))))).toBe(
      'Pi("", Ref(B), Ref(C))'
    ));

  test("should parse arrow with bracketing", () =>
    expect(serialise(strip(result(term(ts("A->(B->C)")))))).toBe(
      'Pi("", Ref(A), Pi("", Ref(B), Ref(C)))'
    ));

  test("should parse arrow with bracketing", () =>
    expect(serialise(strip(resultC(term(ts("(A->B)->C")))))).toStrictEqual(
      'Pi("", Pi("", Ref(A), Ref(B)), Ref(C))'
    ));

  test("should parse arrow with bracketing", () =>
    expect(serialise(strip(result(term(ts("(A->B)->(C->D)")))))).toStrictEqual(
      'Pi("", Pi("", Ref(A), Ref(B)), Pi("", Ref(C), Ref(D)))'
    ));

  test("should parse empty list", () =>
    expect(serialise(strip(result(term(ts("[]")))))).toBe(
      "App(Ref(nil), Hole())"
    ));

  test("should parse list literal with integers", () =>
    expect(serialise(strip(result(term(ts("[1,2,3]")))))).toBe(
      "App(App(App(Ref(cons), Hole()), 1), App(App(App(Ref(cons), Hole()), 2), App(App(App(Ref(cons), Hole()), 3), App(Ref(nil), Hole()))))"
    ));

  test("should parse if statement", () => {
    expect(serialise(strip(result(term(ts("if x then y else z")))))).toBe(
      "If(Ref(x), Ref(y), Ref(z))"
    );
  });

  test("should parse multiline if statement", () => {
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
    ).toBe("If(Ref(x), Ref(y), Ref(z))");
  });

  test("should return an error node for unparseable if statement", () => {
    expect(serialise(strip(result(term(ts("if = then y else z")))))).toBe(
      "ParseError(if statment not well formed)"
    );
  });

  test("should return an error node for unparseable true branch", () => {
    expect(serialise(strip(result(term(ts("if x then @ else z")))))).toBe(
      "ParseError(if statment not well formed)"
    );
  });

  test("should return an error node for unparseable false branch", () => {
    expect(serialise(strip(result(term(ts("if x then y else @")))))).toBe(
      "ParseError(if statment not well formed)"
    );
  });

  test("should parse type constructor", () =>
    expect(serialise(strip(result(type(ts("List(Nat)")))))).toBe(
      "App(Ref(List), Ref(Nat))"
    ));

  test("should parse type constructor on the left of an arrow", () =>
    expect(serialise(strip(result(term(ts("List(Nat)->Nat")))))).toBe(
      'Pi("", App(Ref(List), Ref(Nat)), Ref(Nat))'
    ));

  test("should parse arrow with lots of parenthesis", () =>
    expect(serialise(strip(result(term(ts("(x)((y)(z))->(x)")))))).toBe(
      'Pi("", App(Ref(x), App(Ref(y), Ref(z))), Ref(x))'
    ));

  // TODO: Implement.
  test("should parse named pi types", () =>
    expect(serialise(strip(result(term(ts("(A *)->A")))))).toBe(
      'Pi("A", *, Var(A))'
    ));

  test("should parse definition containing list literal", () => {
    const ast = stripAST(
      result(definition(ts("func abc:List(Nat) = zero\n\n")))
    );
    if (ast._ != "def") {
      throw `unexpected ${ast._}`;
    }
    expect(serialise(ast.term.typ)).toBe("App(Ref(List), Ref(Nat))");
    expect(serialise(ast.term.term)).toBe("Ref(zero)");
  });

  test("should parse case", () => {
    const src = `case n of
    |  zero -> true
    |  succ -> false`;
    const ast = strip(result(term(ts(src))));
    expect(serialise(ast)).toBe(
      "Case(Par(n),[Branch(Identifier(zero), Ref(true)),Branch(Identifier(succ), Ref(false))])"
    );
  });

  test("should parse case with annotation", () => {
    const src = `(case n of
    |  zero -> true
    |  succ -> false
    ):Bool`;
    const ast = strip(result(term(ts(src))));
    expect(serialise(ast)).toBe(
      "Ann(Case(Par(n),[Branch(Identifier(zero), Ref(true)),Branch(Identifier(succ), Ref(false))]), Ref(Bool))"
    );
  });

  test("should parse nested case", () => {
    const src = `case n of
    | zero -> (case m of
      | zero -> false
      | succ -> true)
    | succ -> (case m of
      | zero -> false
      | succ -> lt(n.x)(m.x))`;
    const ast = strip(result(term(ts(src))));
    expect(serialise(ast)).toBe(
      "Case(Par(n),[Branch(Identifier(zero), Case(Par(m),[Branch(Identifier(zero), Ref(false)),Branch(Identifier(succ), Ref(true))])),Branch(Identifier(succ), Case(Par(m),[Branch(Identifier(zero), Ref(false)),Branch(Identifier(succ), App(App(Ref(lt), Ref(n.x)), Ref(m.x)))]))])"
    );
  });

  test("should parse case with empty branch", () => {
    const src = `case n of
    | zero -> 
    | succ -> zero`;
    const ast = strip(result(term(ts(src))));
    expect(serialise(ast)).toBe(
      "Case(Par(n),[Branch(Identifier(zero), ParseError(expected term)),Branch(Identifier(succ), Ref(zero))])"
    );
  });

  test("should parse case with empty final branch", () => {
    const src = `case n of
    | zero -> zero
    | succ -> `;
    const ast = strip(result(term(ts(src))));
    expect(serialise(ast)).toBe(
      "Case(Par(n),[Branch(Identifier(zero), Ref(zero)),Branch(Identifier(succ), ParseError(expected term))])"
    );
  });

  test("should parse definition containing partial case", () => {
    const ast = parseFile(
      ts(`func abc:Bool->Bool = λn case n of
    | zero -> zero
    | succ -> 
    func def:Nat = zero
    `)
    );
    if (ast._ != "outputvalue") {
      throw `unexpected ${ast._}`;
    }

    expect(serialiseAST(stripAST(ast.value.content[0]))).toBe(
      `Def(name=abc, term=Ann(Abs("n", Case(Par(n),[Branch(Identifier(zero), Ref(zero)),Branch(Identifier(succ), ParseError(expected term))])), Pi("", Ref(Bool), Ref(Bool))))`
    );
    expect(serialiseAST(stripAST(ast.value.content[1]))).toBe(
      `Def(name=def, term=Ann(Ref(zero), Ref(Nat)))`
    );
  });

  /*
   */
  test("should parse definitions following error node", () => {
    const ast = parseFile(
      ts(`type Bool = false | true
          func not:Bool->Bool = err if b then false else true
f         unc zz:Bool = false`)
    );
    if (ast._ != "outputvalue") {
      throw `unexpected ${ast._}`;
    }

    // expect(serialiseAST(stripAST(ast.value.content[0]))).toBe(
    //   ``
    // );
    expect(serialiseAST(stripAST(ast.value.content[1]))).toBe(``);
  });

  test("should parse empty string literal", () => {
    const src = `""`;
    const ast = strip(result(term(ts(src))));
    expect(serialise(ast)).toBe('""');
  });

  test("should parse string literal", () => {
    const src = `"hello"`;
    const ast = strip(result(term(ts(src))));
    expect(serialise(ast)).toBe('"hello"');
  });

  test("should parse definition containing string literal", () => {
    const ast = stripAST(result(definition(ts('func abc:String = ""'))));
    if (ast._ != "def") {
      throw `unexpected ${ast._}`;
    }
    expect(serialise(ast.term.typ)).toBe("Ref(String)");
    expect(serialise(ast.term.term)).toBe('""');
  });

  test("should parse let expression", () => {
    const ast = strip(result(term(ts("let g = f(x) in h(g)(g)"))));
    expect(serialise(ast)).toBe(
      "Let(Identifier(g), App(Ref(f), Ref(x)), App(App(Ref(h), Ref(g)), Ref(g)))"
    );
  });

  test("should allow ParseError on the rhs of App", () => {
    const src = `f("hello )`;
    const ast = strip(result(term(ts(src))));
    expect(serialise(ast)).toBe(
      `App(Ref(f), ParseError(failed to parse string literal))`
    );
  });

  test("should parse app with string literal", () => {
    const src = `elimIO(println("hello))`;
    const ast = strip(result(term(ts(src))));
    expect(serialise(ast)).toBe(
      `App(Ref(elimIO), App(Ref(println), ParseError(failed to parse string literal)))`
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
    const src = `loadsofstuffherethenfunc x:Nat = zero`;
    // skip all the junk then parse a definition.
    const ast = stripAST(result(bind(resync, (_) => definition)(ts(src))));
    expect(serialiseAST(ast)).toBe(
      `Def(name=x, term=Ann(Ref(zero), Ref(Nat)))`
    );
  });
});
