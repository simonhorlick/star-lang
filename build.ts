// build is a library for orchestrating builds of source files for this language.

import { parseFile, ADT, Def } from "./ast";
import { typecheck } from "./check";
import { typecheckErrorDiagnostic } from "./inspect";
import { parseErrorDiagnostic } from "./parser";
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

export const build = (src: string): Def[] => {
  const t = parseFile({ src, idx: 0 });

  if (t.type != "outputvalue") {
    throw `build failed: ${parseErrorDiagnostic(t)}`;
  }

  // generate syntax nodes for ADTs, etc
  const f = processADTs(t.value);

  // desugar definitions
  const adts = t.value.content.filter((c) => c._ == "adt") as ADT[];
  const defs = (f.content.filter((c) => c._ == "def") as Def[]).map((def) =>
    desugar(def, adts)
  );

  let checks = true;
  let checked: Def[] = [];
  for (const def of defs) {
    // typecheck
    console.log(`\n# checking definition ${def.name}`);
    const result = typecheck(defs, adts, [], def.term, def.typ, 0, src.length);
    if (result._ == "typecheckerror") {
      console.error(typecheckErrorDiagnostic(src, result));
      checks = false;
    } else {
      checked.push(Def(def.name, result.term, result.type));
    }
  }

  if (!checks) {
    throw "failed check";
  }

  return checked;
};
