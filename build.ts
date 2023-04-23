// build is a library for orchestrating builds of source files for this language.

import { parseFile, ADT, Def, ASTNode, File } from "./ast";
import { TypecheckError, identifier, typecheck } from "./check";
import { typecheckErrorDiagnostic } from "./inspect";
import { ParseError, parseErrorDiagnostic } from "./parser";
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
};

export const build = (
  src: string
): BuildResult | ParseError | TypecheckError => {
  const t = parseFile({ src, idx: 0 });

  if (t._ != "outputvalue") {
    return t;
  }

  // generate syntax nodes for ADTs, etc
  const f = processADTs(t.value);

  // desugar definitions
  const adtList = t.value.content.filter((c) => c._ == "adt") as ADT[];
  const adts = new Map<string, ADT>();
  for (const adt of adtList) {
    adts.set(identifier(adt.name), adt);
  }
  const defs = (f.content.filter((c) => c._ == "def") as Def[]).map((def) =>
    desugar(def, adts)
  );
  const nondefs = f.content.filter((c) => c._ != "def") as Def[];

  let defsMap: Map<string, Def> = new Map();
  let checkedMap: Map<string, Def> = new Map();
  for (const def of defs) {
    defsMap.set(def.name, def);
  }

  let checkerErrors: TypecheckError[] = [];
  for (const def of defs) {
    console.log(`\n# checking definition ${def.name}`);
    const result = typecheck(
      defsMap,
      adts,
      [],
      def.term,
      def.typ,
      0,
      src.length
    );
    if (result._ == "typecheckerror") {
      console.error(typecheckErrorDiagnostic(src, result));
      checkerErrors.push(result);
    } else {
      checkedMap.set(def.name, Def(def.name, result.term, result.type));
    }
  }

  if (checkerErrors.length > 0) {
    return checkerErrors[0];
  }

  return {
    _: "buildresult",
    file: { _: "file", content: [...nondefs, ...checkedMap.values()] },
    defs: checkedMap,
  };
};
