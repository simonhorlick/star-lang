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
  Origin2,
} from "./ast";
import { bind, many, parseErrorDiagnostic, Stream, Result } from "./parser";
import { identifier2str, resync, serialise } from "./pratt";

export const ts = (s: string): Stream => ({
  src: `parsed${s}`,
  idx: 6,
});

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

describe("ast", () => {
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

  test("should parse definition containing string literal", () => {
    const ast = stripAST(result(definition(ts(`func abc:String = ""`))));
    if (ast._ != "def") {
      throw `unexpected ${ast._}`;
    }
    expect(serialise(ast.term.type)).toBe(`Ref("String")`);
    expect(serialise(ast.term.term)).toBe(`StringLit("")`);
  });

  test("should include origins for type annotations of definitions", () => {
    const ast = result(definition(ts(`func abc:String = ""`))) as Origin2;
    const term = (ast.child as Def).term;
    // Here there are two origins - one for the term and one for the Ref.
    expect(serialise(term.type)).toBe(`Orig(15, 21, Ref("String"))`);
  });

  test("should resync to next keyword", () => {
    const src = `junkherefunc x:Nat = zero`;
    // skip all the junk then parse a definition.
    const ast = stripAST(result(bind(resync, (_) => definition)(ts(src))));
    expect(serialiseAST(ast)).toBe(
      `Def(name=x, term=Ann(Ref("zero"), Ref("Nat")))`
    );
  });

  test("should parse pi types in function type", () => {
    const src = `func bool_match : (b:Bool) -> (P:((x:Bool) -> *)) -> (t:P(true)) -> (f:P(false)) -> P(b) =
    λb λP λt λf b(P,t,f)
`;
    const ast = stripAST(result(definition(ts(src)))) as Def;

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

  test("should parse indexed types with type annotations on constructors", () => {
    const ast = stripAST(
      result(
        adt(
          ts(
            `type VectBool(sz Nat) = vbnil:VectBool(zero) | vbext(n Nat, head Bool, tail VectBool(n)):VectBool(succ(n))`
          )
        )
      )
    );
    if (ast._ != "adt") {
      throw `unexpected ${ast._}`;
    }
    expect(serialiseAST(ast)).toBe(
      `ADT(VectBool, constructors=vbnil():App(Ref("VectBool"), Ref("zero"))|vbext(n:Ref("Nat"),head:Ref("Bool"),tail:App(Ref("VectBool"), Ref("n"))):App(Ref("VectBool"), App(Ref("succ"), Ref("n"))))`
    );
  });
});
