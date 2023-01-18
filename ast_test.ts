import { describe, expect, test } from "@jest/globals";
import { Abs, App, Ref, Term, transformDebruijin, Var } from "./ast";
import { erase } from "./evaluation";

// describe("debruijin", () => {
//   test("TestComputeDebruijinIndicesSingleBinder", () => {
//     // Γ = [t]; λx.t
//     // λ.1
//     const expected: Term = Abs("x", Var("t", 1));

//     const actual = transformDebruijin(Abs("x", Ref("t")), [
//       { type: "bind", name: "t", typ: Ref("T") },
//     ]);

//     expect(actual).toStrictEqual(expected);
//   });

//   test("TestComputeDebruijinIndicesIdApp", () => {
//     // (λx. x)(λz. z)
//     // (λ. 0)(λ. 0)
//     const expected: Term = App(Abs("x", Var("x", 0)), Abs("z", Var("z", 0)));
//     const actual = transformDebruijin(
//       App(Abs("x", Ref("x")), Abs("z", Ref("z")))
//     );

//     expect(actual).toStrictEqual(expected);
//   });

//   // λs. λz. s (s z)
//   const two = Abs(
//     "s",
//     Abs("z", App(Var("s", 1), App(Var("s", 1), Var("z", 0))))
//   );

//   test("TestComputeDebruijinIndicesChurchNat", () => {
//     // λs. λz. s (s z)
//     // λ. λ. 1 (1 0)
//     const expected = two;

//     const actual = transformDebruijin(
//       Abs("s", Abs("z", App(Ref("s"), App(Ref("s"), Ref("z")))))
//     );
//     expect(actual).toStrictEqual(expected);
//   });
// });
