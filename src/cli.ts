#!/usr/bin/env ./node_modules/.bin/ts-node-script
//
// The star command line interface.
//

import { promises as fs } from "fs";
import { BuildResult, build } from "./build";
import { pretty, prettyC } from "./pretty";
import * as Erased from "./erased";
import { erase, nodeJsRuntime, reduce } from "./evaluation";
import { parseErrorDiagnostic, typecheckErrorDiagnostic } from "./inspect";

async function check(uri: string): Promise<void> {
  let src: string;
  try {
    src = await fs.readFile(uri, "utf8");
  } catch (e) {
    console.error(`failed to open file ${uri}: ${e}`);
    return;
  }

  let b: BuildResult;
  try {
    b = build(src);
  } catch (e) {
    // This should only happen in the case of a compiler bug.
    console.error(`failed to build: ${e}`);
    return;
  }

  if (b.parseErrors.length > 0) {
    for (const e of b.parseErrors) {
      console.log(parseErrorDiagnostic(src, e, uri));
    }
    return;
  }

  if (b.checkerErrors.length > 0) {
    for (const e of b.checkerErrors) {
      console.log(typecheckErrorDiagnostic(src, e));
    }
    return;
  }

  console.log(`finished checking`);
}

// Parses, builds and runs the given star source file.
async function run(uri: string, trace: boolean): Promise<void> {
  let src: string;
  try {
    src = await fs.readFile(uri, "utf8");
  } catch (e) {
    console.error(`failed to open file ${uri}: ${e}`);
    return;
  }

  let b: BuildResult;
  try {
    b = build(src);
  } catch (e) {
    // This should only happen in the case of a compiler bug.
    console.error(`failed to build: ${e}`);
    return;
  }

  if (b.parseErrors.length > 0) {
    for (const e of b.parseErrors) {
      console.log(parseErrorDiagnostic(src, e, uri));
    }
    return;
  }

  if (b.checkerErrors.length > 0) {
    for (const e of b.checkerErrors) {
      console.log(typecheckErrorDiagnostic(src, e));
    }
    return;
  }

  const defs = b.defs;
  const checked = [...defs.values()];

  const erased = checked.map((def) => {
    if (def.term.typ._ == "star") {
      // replace types with id
      // TODO: Remove from runtime entirely.
      console.log(`erasing ${def.name} ${pretty(def.term)}`);
      const e = Erased.Def(def.name, Erased.Abs("x", Erased.Var("x", 0)));
      console.log(`erased ${def.name} to ${prettyC(e.term, false)}`);
      return e;
    } else {
      console.log(`erasing ${def.name} ${pretty(def.term)}`);
      const e = Erased.Def(def.name, erase(def.term));
      console.log(`erased ${def.name} to ${prettyC(e.term, false)}`);
      return e;
    }
  });

  const main = erased.find((def) => def.name == "main");
  if (!main) {
    console.error(`main function not found`);
    return;
  }

  let evaluated = reduce(nodeJsRuntime, erased, main.term, trace);
  if (trace) {
    console.log(prettyC(evaluated, false));
  }
}

const usage = () =>
  console.log(`usage:\n  star run <options> <file>\n  star check <file>`);

const handleCommandLineArgs = (args: string[]) => {
  if (args.length == 0) {
    usage();
    return;
  }

  const command = args[0];
  switch (command) {
    case "check": {
      let remainingArgs: string[] = args.slice(1);
      // require file argument
      if (remainingArgs.length != 1) {
        usage();
        return;
      }
      check(remainingArgs[0]);
      break;
    }
    case "run": {
      let remainingArgs: string[] = [];
      let trace = false;
      for (const arg of args.slice(1)) {
        if (arg == "-t") {
          trace = true;
        } else {
          // not handled
          remainingArgs.push(arg);
        }
      }
      // require file argument
      if (remainingArgs.length != 1) {
        usage();
        return;
      }
      run(remainingArgs[0], trace);
      break;
    }
    default:
      usage();
  }
};

handleCommandLineArgs(process.argv.slice(2));
