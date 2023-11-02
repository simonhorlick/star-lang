// build is a library for orchestrating builds of source files for this language.

import { parseFile, ADT, Def, ASTNode, File, Type, Ann } from "./ast";
import {
  TypecheckError,
  identifier,
  infer,
  logFull,
  strip,
  stripAST,
  typecheck,
} from "./check";
import { typecheckErrorDiagnostic, foldTree } from "./inspect/inspect";
import { FatalParseError, parseErrorDiagnostic } from "./parser";
import { processADTs, desugar } from "./process";

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
export const build = (src: string, stripDefs: boolean = true): BuildResult => {
  const t = parseFile({ src, idx: 0 });

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
    adts.set(identifier(adt.name), adt);
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
    // console.log(`\n# checking definition ${def.name}`);
    const result = infer(defsMap, adts, [], def.term, 0, src.length);
    if (result._ == "typecheckerror") {
      // console.error(typecheckErrorDiagnostic(src, result));
      checkerErrors.push(result);
    } else {
      checkedMap.set(def.name, Def(def.name, Ann(result.term, result.type)));
    }
  }

  const parseErrors: TypecheckError[] = [];
  for (const def of defs) {
    // FIXME: need source locations.
    const errs = foldTree(
      (acc, curr) =>
        curr._ == "err"
          ? acc.concat({
              msg: curr.msg,
              start: 0,
              end: 0,
            } as TypecheckError)
          : acc,
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
