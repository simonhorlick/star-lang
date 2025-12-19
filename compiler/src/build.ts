// build is a library for orchestrating builds of source files for this language.

import {
  parseFile,
  ADT,
  Def,
  File,
  stripAST,
  ASTNode,
  Def2,
  Origin2,
} from "./ast";
import { TypecheckError, check, fill, infer } from "./typecheck";
import { foldTreeCtx, typecheckErrorDiagnostic } from "./inspect";
import { pretty } from "./pretty";
import { processADTs, desugar } from "./adts";
import { identifier2str } from "./pratt";

// What's the MVP for this?
// - parse all files recursively
// - create a map <Uri, File>

// TODO: Read module file
//  - figure out the module path, i.e. github.com/simonhorlick/compiler
// TODO: Parse all files
//  - list all star files recursively from the module root directory
// TODO: Build package graph (transitive closure of imports)
// TODO: Find targets

// TODO: Fetch dependencies (from github)

export type BuildResult = {
  _: "buildresult";
  file: File;
  defs: Map<string, Def2>;
  nondefs: ASTNode[];
  adts: Map<string, ADT>;
  checkerErrors: TypecheckError[];
  parseErrors: TypecheckError[];
};

// build takes a source file as a string, attempts to parse the file then
// typechecks each top level definition. It will always return something. In
// the case of a parse error an error node will be present in the parse tree.
// If there are any typecheck failures they will be returned in the result.
export const build = (src: string, stripDefs: boolean = false): BuildResult => {
  const t = parseFile({ src, idx: 0 });

  console.log(`building...`);

  if (t._ == "parseerror") {
    // parsing should never fail
    throw "unexpected parse error";
  }

  const adtList = t.value.content.filter((c) => c._ == "adt") as ADT[];
  const adts = new Map<string, ADT>();
  for (const adt of adtList) {
    adts.set(identifier2str(adt.name), adt);
  }

  // generate syntax nodes for ADTs, etc
  const f = processADTs(t.value);

  // desugar each definition, keeping track of Origin nodes so we can assign
  // origins to the defs.
  const go = (node: ASTNode): Def2 | null => {
    if (node._ == "def") {
      // This can happen for definitions that are generated.
      return desugar(node, undefined, undefined);
    } else if (node._ == "orig2" && node.child._ == "def") {
      return desugar(node.child, node.start, node.end);
    } else {
      return null;
    }
  };
  const defs = f.content
    .map((def) => {
      if (stripDefs) return stripAST(def) as Def;
      else return def;
    })
    .map(go)
    .filter((n): n is Def2 => n !== null);

  const nondefs = f.content.filter((c) => c._ != "def") as ASTNode[];

  let defsMap: Map<string, Def2> = new Map();
  let checkedMap: Map<string, Def2> = new Map();
  for (const def of defs) {
    defsMap.set(def.name, def);
  }

  let checkerErrors: TypecheckError[] = [];
  for (const def of defs) {
    // console.log(`\n# checking definition ${def.name}: ${pretty(def.term)}`);
    let checks = true;
    try {
      const result = infer(defsMap, adts, [], def.term, 0, src.length);
      const filled = fill(result);
      if (filled.term._ != "ann") {
        throw "expected annotated term for definition body";
      }
      checkedMap.set(def.name, Def2(def.name, filled.term, def.start, def.end));
    } catch (e) {
      checks = false;
      if ((e as any)._ !== undefined) {
        const result = e as TypecheckError;
        console.error(typecheckErrorDiagnostic(src, result));
        checkerErrors.push(result);
      } else {
        console.error(e);
        checkerErrors.push(TypecheckError(e as string, 0, src.length));
      }
      // add the original term to the map so we can at least get some
      // information when inspecting.
      checkedMap.set(def.name, Def2(def.name, def.term, def.start, def.end));
    }
    console.log(checks ? `✅ ${def.name}` : `❌ ${def.name}`);
  }

  const parseErrors: TypecheckError[] = [];
  for (const def of defs) {
    const errs = foldTreeCtx(
      (acc, curr) => {
        if (curr.term._ !== "err") return acc;
        return acc.concat({
          msg: curr.term.msg,
          start: curr.start ?? 0,
          end: curr.end ?? 0,
        } as TypecheckError);
      },
      [] as TypecheckError[],
      def.term
    );
    parseErrors.push(...errs);
  }

  return {
    _: "buildresult",
    file: { _: "file", content: [...nondefs, ...checkedMap.values()] },
    defs: checkedMap,
    nondefs: nondefs,
    adts: adts,
    checkerErrors: checkerErrors,
    parseErrors: parseErrors,
  };
};
