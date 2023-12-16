import { describe, test } from "vitest";
import { ADT, Def, parseFile, identifier2str, stripAST } from "./ast";
import { relevance } from "./relevance";
import { desugar, processADTs } from "./process";

const preCheck = (src: string) => {
  const t = parseFile({ src, idx: 0 });

  // TODO: Expose any parse errors to the user.

  if (t._ != "outputvalue") {
    return t;
  }

  // logFull(t.value.content);

  // generate syntax nodes for ADTs, etc
  const f = processADTs(t.value);

  // desugar definitions
  const adtList = t.value.content.filter((c) => c._ == "adt") as ADT[];
  const adts = new Map<string, ADT>();
  for (const adt of adtList) {
    adts.set(identifier2str(adt.name), adt);
  }
  const defs = (f.content.filter((c) => c._ == "def") as Def[])
    .map((def) => {
      return stripAST(def) as Def;
    })
    .map((def) => desugar(def, adts));
  const nondefs = f.content.filter((c) => c._ != "def") as Def[];

  let defsMap: Map<string, Def> = new Map();
  for (const def of defs) {
    defsMap.set(def.name, def);
  }

  return {
    _: "buildresult",
    file: { _: "file", content: [...nondefs, ...defsMap.values()] },
    defs: defsMap,
  };
};

describe("relevance", () => {
  test("should count occurances", () => {
    const src = `
      type X = x
      type Y = y
      func id:X->X = λx x
      // test plain var
      func f:X->Y->X = λx λy x
      // test pass through app
      func g:X->Y->X = λx λy id(x)
      // some examples
      //func g:X = f(x)(y)
      //func h:X = let n = f(x) in n(y)
  `;
    const ast = preCheck(src);
    if (ast._ !== "buildresult") throw "failed to build";

    const rel = relevance((ast.defs.get("g") as Def).term, []);

    // now lift the lambda annotations to the type level? is it necessary? won't we just walk the term tree anyway?

    // Should this happen before typecheck? Because we essentially need to redo
    // the typecheck anyway.

    // const simplified = simplify();

    // TODO: Now I have an AST with Rel nodes, but I'm not sure how to use
    // these to simplify callsites. I think it needs to be part of the type,
    // then we re-run the typechecker and each app we encounter we check the
    // type of the argument - i.e. Rel(X,n) == X and if it's zero we rewrite
    // the callsite. Further question - how can this method be used for editor
    // code->code transformations (we want to edit, remove and add arguments to
    // functions trivially).
    // Can we enumerate all of the possibilities and write tests?

    console.log(rel);
  });

  // test("should determine P as runtime irrelevant", () => {
  //   const src = `
  //   //type Bool = true | false
  //   //func not:Bool->Bool = λb b(λP Bool)(false)(true)
  //   type X = x
  //   type Y = y
  //   type Z = z
  //   func f:X->Y->Z = λx λy z
  //   func g:Z = f(x)(y)
  //   // in the function f, the arguments x and y are never used, so we can safely
  //   // omit them from the runtime code.
  //   // TODO: Annotate type signature with relevance. Calculate this in a
  //   //  separate pass.
  //   `;
  //   const ast = build(src, true);
  //   if (ast._ !== "buildresult") throw "failed to build";

  //   for (const def of ast.defs.values()) {
  //     // TODO: Relevance pass.
  //     // TODO: Simplification pass.

  //     const relpass = Def(def.name, simplify(relevance(def.term)), def.typ);

  //     console.log(`${relpass.name}\n${tree(relpass.term, "  ", relpass.typ)}`);
  //   }
  // });
});
