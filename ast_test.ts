import { describe, expect, test } from "@jest/globals";
import { Abs, App, parenthesis, parseFile, Ref, term, Term, Var } from "./ast";
import { erase } from "./evaluation";
import { parseErrorDiagnostic } from "./parser";

describe("ast", () => {
  test("should parse lambda body greedily", () => {
    const src = `λn n(λp Nat)`;
    const t = term({ src, idx: 0 });
    if (t.type == "parseerror") {
      throw parseErrorDiagnostic(t);
    }
    // Expect the parser to consume the input.
    expect(t.stream.idx).toBe(src.length);
  });
});
