// build is a library for orchestrating builds of source files for this language.

import { identifier2str, parseFile, ADT, Def, File, stripAST } from "./ast";
import { TypecheckError, fill, infer } from "./typecheck";
import { foldTreeCtx, typecheckErrorDiagnostic } from "./inspect";
import { pretty } from "./pretty";
import { processADTs, desugar } from "./adts";

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
  defs: Map<string, Def>;
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
      if (stripDefs) return stripAST(def) as Def;
      else return def;
    })
    .map((def) => desugar(def, adts));
  const nondefs = f.content.filter((c) => c._ != "def") as Def[];

  let defsMap: Map<string, Def> = new Map();
  let checkedMap: Map<string, Def> = new Map();
  for (const def of defs) {
    defsMap.set(def.name, def);
  }

  let checkerErrors: TypecheckError[] = [];
  for (const def of defs) {
    console.log(`\n# checking definition ${def.name}: ${pretty(def.term)}`);
    try {
      const result = infer(defsMap, adts, [], def.term, 0, src.length);
      const filled = fill(result);
      if (filled.term._ != "ann") {
        throw "expected annotated term for definition body";
      }
      checkedMap.set(def.name, Def(def.name, filled.term));
    } catch (e) {
      const result = e as TypecheckError;
      console.error(typecheckErrorDiagnostic(src, result));
      checkerErrors.push(result);
      // add the original term to the map so we can at least get some
      // information when inspecting.
      checkedMap.set(def.name, Def(def.name, def.term));
    }
  }

  const parseErrors: TypecheckError[] = [];
  for (const def of defs) {
    // FIXME: need source locations.
    console.log(`checking for parse errors in tree`);
    const errs = foldTreeCtx(
      (acc, curr) => {
        if (curr.term._ !== "err") return acc;
        console.log(`curr is ${JSON.stringify(curr)}`);
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
    checkerErrors: checkerErrors,
    parseErrors: parseErrors,
  };
};
