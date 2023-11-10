#!/usr/bin/env ./node_modules/.bin/ts-node-script

import { BuildResult, build } from "./build";
import { printNodeAsDotGraph } from "./pretty";

const ensureBuild = (src: string): BuildResult => {
  const result = build(src, false);
  if (result.checkerErrors.length) throw "build failed";
  return result;
};

const src = `
type Bool = false | true
func not:Bool->Bool = λb
  case b of
  | false -> true
  | true -> false
`;
const result = ensureBuild(src);
const def = result.defs.get("not")!;
console.log(printNodeAsDotGraph(def.term));
