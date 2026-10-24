Star roadmap

Basic requirements for a first release version.

Compiler bugs found in the 2026-10-24 review

Every item below was reproduced against the build pipeline (compiler/src/build.ts); the repro program is given where it is short. Fix each one with a failing unit test first (see AGENTS.md). "Fix verified" means the one-line change was applied locally, left all 328 tests green, and was reverted.

Type checker

- [ ] bug: hole filling never checks consistency, so heterogeneous lists typecheck: `func xs:List(Nat) = [true]` and `func xs:List(Nat) = [1, true]` build with no errors. `equate` records a binding for every hole and `fill` (typecheck.ts) substitutes them in order without detecting conflicts or re-checking (see the TODO in `fill`).
- [ ] bug: undefined references are accepted in checking position: `func main:Nat = foo` builds clean and `star check` prints "finished checking"; the program then dies at runtime with "reference not found". The `ref` branch of `check` returns an annotated term for tooling but never records an error.
- [ ] bug: duplicate definitions are silently overwritten: `func f:Nat = zero` followed by `func f:Bool = true` builds with no errors (`defsMap.set` in build.ts). A constructor name colliding with a function name is silent too.
- [ ] bug: `let` desugaring doesn't shift the expected type under the new binder: `func f:(A:*) -> A -> A = λA λx let y = x in y` fails with "name mismatch: looking up A@1; got x@1". In `check` (typecheck.ts) the desugared pi should be `Pi("", expressionType.type, shift(1, 0, tty))`. Fix verified.
- [ ] bug: `shift` and `subst` (substitution.ts) don't traverse the type inside `Ann` nodes, and `subst` doesn't substitute the scrutinee of a `Case` although `shift` shifts it. A user annotation in a case branch with constructor arguments gets wrong indices: `| succ => (x : A)` in a polymorphic function fails with a name mismatch while the same annotation in the `zero` branch passes. Fix for `Ann` verified.
- [ ] bug: `if` never performs dependent elimination. `ifStatement` (pratt.ts) wraps the condition in `Ann(cond, Bool)` and `desugarCaseStatement` only treats a bare `Var` scrutinee as dependent, so `func i:(b:Bool)->F(b) = λb if b then false else 2` fails with "(λ F(b))(true) is not Bool" while the `case` form passes. Fix: unwrap `Ann` nodes when computing `strippedName`. Fix verified.
- [ ] bug: type-level `case` and `let` can't be reduced, so dependent types only work through helper type functions defined earlier in the file. `reduce` (equal.ts) returns `Case` nodes unchanged and throws "TODO - reduce let", and the `ann` rule of `infer` checks the body against the original annotation instead of the checked one.
  - [ ] an inline signature `(b:Bool)->(if b then Bool else Nat)` fails
  - [ ] a `case` in a pi domain crashes with "dbgCheckIndices: unexpected case" (context.ts)
  - [ ] definition order matters: `F` before `i` passes, `i` before `F` fails, because the unchecked forward reference still contains its `Case` node (see the dependency graph item under "Stable version improvements")
  - [ ] `let n = (case ...) in n` fails with the bare error "TODO" because `infer` has no rule for `case`
- [ ] bug: reference equality is nominal only at the top level. `equate` returns false for two refs with different names without unfolding them, but does unfold after other structural mismatches, so with `func N:* = Nat` the definition `x:N = zero` passes while `xs:List(N) = nil(Nat)` fails with "List(N) is not List(Nat)". Either unfold refs before giving up or document aliases as unsupported.
- [ ] bug: name capture in the generated ADT encoding (adts.ts). The eliminator uses the fixed binder names `P` and `t` plus the constructor names and resolves `Par` nodes by name, so a constructor argument named `P`, a type parameter named `t`, or an argument named like another constructor (`type T = a | b(a Nat)`) all produce type errors on the generated definitions. Use fresh names or resolve to indices before wrapping.
- [ ] bug: a non-terminating type-level function (`func Loop:*->* = λA Loop(A)` then `func x:Loop(Nat) = zero`) overflows the stack inside `reduce` and is reported as "RangeError: Maximum call stack size exceeded" over the whole file. Give `reduce` a fuel limit and a real diagnostic.

Parser

- [ ] bug: the binding powers in `getBindingPower` (pratt.ts) are inverted for every operator added after arithmetic: `++`, the comparisons, `==`, `||` and `&&` bind tighter than application and indexing.
  - `a + b == c` parses as `a + (b == c)`
  - `a == b && c` parses as `a == (b && c)`
  - `a < b || c > d` parses as `(a < (b || c)) > d`
  - `f(x) ++ g(y)` parses as `(f(x) ++ g)(y)`
  - `a && f(x)` parses as `(a && f)(x)`
  - `a == xs[i]` parses as `(a == xs)[i]`
  - application and indexing should bind tightest, then `* /`, `+ -`, `++`, comparisons, `== !=`, `&&`, `||`. The tests only cover each operator alone plus `a||b&&c`; add mixed-operator tests.
- [ ] bug: unary minus parses its operand with `expression(0)`, so `-a + b` parses as `-(a + b)` and `-a - b` as `-(a - b)`.
- [ ] bug: the index in `xs[...]` is parsed with `expression(12)`, so `xs[i + 1]` is a fatal parse error (expected "]"). Parse it with `expression(0)` like the application argument list.
- [ ] bug: everything after the first unparseable top-level token is silently dropped. `parseFile` (ast.ts) is `many` over the alternatives and `build` never checks that the input was consumed (`consumeAll` in parser.ts is unused). An empty `//` line, CRLF line endings, the typo `fun`, a stray `}` or trailing whitespace after `case x of` all truncate the file and `star check` reports success; a CRLF file with an undefined reference and an ill-typed call built with zero errors.
- [ ] bug: type declarations have no error recovery: `type Foo = bar |` makes `build` throw the raw string "expected identifier; got err".
- [ ] bug: SYNTAX.md documents `func not(b Bool) Bool = ...` but `definition` requires a colon after the name; the form yields a garbage definition and truncates the file. Implement it or drop it from SYNTAX.md.
- [ ] bug: `pretty` (pretty.ts) drops parentheses on the left of an arrow: `(A→B)→C` and `A→(B→C)` both print as `A→B→C`, so type errors involving function arguments are ambiguous.

Evaluator

- [ ] bug: `reduceOnce3` normalises under lambdas and unfolds every global reference it meets, so a recursive function left under a binder never terminates: `func main:Nat->Nat = λx add(x, succ(zero))` unfolds `add` forever (614 steps in 20s with the term still growing) while `add(1,1)` normalises in 22 steps. Reduce to weak head normal form and only continue under constructors, or stop unfolding references under binders.
- [ ] perf: every evaluation step pretty-prints both sides of each application to detect change, and `Md`/`Nd` are computed unconditionally, so steps slow down quadratically as the term grows (0.75s, 5.6s and 18.7s per 200 steps at term sizes 500, 1000 and 1500). Compare structurally.
- [ ] bug: the "no forward progress" check in `reduce` (evaluation.ts) compares against the term from two steps back because `prev` is assigned after the comparison, so a one-step cycle isn't detected.

Diagnostics and housekeeping

- [ ] internal failures are thrown as bare strings or JavaScript errors and reported over the whole file: "TODO", "name mismatch ...", "dbgCheckIndices: unexpected case", RangeError. Throw `TypecheckError` with a position everywhere and stop `build` from using an `Error` object as a message.
- [ ] too many arguments to a constructor reports "Nat→★ is not Nat" because every value is an eliminator under the self-type encoding; detect the case and explain it.
- [ ] "statment" is misspelled in two parser messages (pratt.ts).
- [ ] package.json exports `./print_ast` and `./relevance`, which don't exist.
- [ ] `build` logs "building..." and a tick per definition, and `check` prints "debug check failed" to stderr, from library code the language server runs on every edit.
- [ ] `addTermToCtx` runs `dbgCheckIndices` on every binding: quadratic, and it is where the pi-domain crash above comes from. Gate it behind a debug flag.
- [ ] `equate` pretty-prints both sides at every recursive call for cycle detection; the strings ignore indices, so distinct terms can collide and compare unequal.
- [ ] hole ids come from `Math.random()`; use a counter.
- [ ] `reserved` (pratt.ts) lacks `in` and `type`.
- [ ] `identifier` accepts trailing dots, so `λx.x` lexes as a single identifier.
- [ ] `inspect` gives let-bound variables the type `Ref("TODO")` (FIXME in inspect.ts).

Design

- [ ] type-in-type plus unrestricted recursion means every type is inhabited: `func bad:Equal(Nat, zero, succ(zero)) = bad` builds with no errors. Acceptable for a programming language, but it contradicts the README's "sound" claim, and the proof items under "Stable version improvements" need a termination or guardedness check first.

Tooling

- [x] Inspect shouldn’t need to calculate the type of a lambda abstraction (it should be annotated by the checker) (`check` wraps every lambda it checks in `Ann(λ, Π)` and `inspect` reads that annotation)

Syntax


Documentation

- [ ] Examples:
  - [ ] Fib
  - [ ] Quicksort
  - [ ] Wordcount
- [ ] Initial website
  - [ ] define rationale, purpose for the project, key points that drive the design
  - [ ] interactive examples in the browser

Stable version improvements

- [x] Add final AST syntax for “indexed” types like Vector (constructors declare their return type, see SYNTAX.md; parameters and indices are classified in ast.ts)
- [ ] auto-infer function properties (functor, applicative, semigroup) and display in the editor
- [ ] ide: apply function to term: select a term, type the function name, term is now passed as an argument to that function and the function is inserted correctly in the source. (see codeaction in lsp)
- [ ] ide: rename symbols (see https://microsoft.github.io/language-server-protocol/specifications/specification-3-15/#textDocument_rename)
- [ ] have the editor insert "todo"s when writing (i.e. try and keep the AST syntax reasonable)
- [ ] ide: constructors in case statements don't have syntax highlighting (inspect gives branch constructors no type, so they get no span and no semantic token)
- [ ] ide: find references
- [x] ide: jump to definition (`definitionLocation` in inspect.ts, `onDefinition` in the server)
- [x] bug: infinite loops in the checker when argument length mismatch or type mismatch. (`equate` has cycle detection and a depth limit; argument-count, argument-type and self-application mistakes fail in milliseconds. A non-terminating type-level function still overflows the stack, see the review section above.)
- [ ] feat: Benchmark programs
  - [ ] sum 1..n (n in ascending powers of 10)
  - [ ] fib n (for the first 10 or so)
  - [ ] float parsing
  - [ ] ieee float to string
  - [ ] json parsing
  - [ ] measure and store performance stats (can be stored in the repo)
- [ ] feat: manual erasure of P arguments during erase transformation
- [ ] automatic inlining of functions only used once (auto-inline constructors)
- [ ] web-based language implementation debugger
  - [ ] allow user to explore AST through evaluation
- [x] implement an Equal type (user-definable as `type Equal(A *, a A, b A) = refl : Equal(A, a, a)`; symmetry, transitivity, congruence and substitution proofs are tested)
- [x] double negation proof (tested in typecheck.test.ts)
- [ ] have a flag for enabling parsing of self types (for debugging)
- [ ] do notation
- [ ] Pipeline syntax using a ▷ (I.e. |>)
- [x] IDE: autocomplete should suggest values from the context whose types fit the hole first (`complete` filters context bindings by type and sorts them before definitions)
- [ ] Fix compile errors with AI suggestions
- [ ] AST-aware diffs for git (i.e. don’t show the diff for reformatted lines)
- [ ] FunSearch (Google)
- [ ] erase type arguments (Rel nodes) start with unit tests
- [ ] Use LLM trained on star to implement functions from their type signatures
  - [ ] Or, perhaps more interesting, generate proofs of properties automatically
  - [ ] div : \a \b mul(div(a,b),b) == a
  - [ ] plus: \a \b plus(a,0)==a; plus(a,b)==plus(b,a); plus(0,a)==a; plus(plus(a,b),c)==plus(a,plus(b,c))
- [ ] Look at competitive programming to figure out what to optimise (for-n macros, etc)
- [ ] Network io
- [ ] File io
- [ ] Begin work on standard library (maps, lists, stacks, queues - have multiple implementations with a shared interface)
- [ ] Can datatypes be encoded into bytes? I.e. Bool = 0 or 1.
- [ ] Allow `type String = List(Byte)`
- [ ] Add a snippet for functions so the user can fill in the arguments
- [ ] Modules
  - [ ] Modules maintain the Liskov Substitution Principle
- [ ] refactorings:
  - [ ] Rename function
  - [ ] Rename variable
  - [ ] Inline function
  - [ ] Re-order function arguments
  - [ ] Wrap selection in function
  - [ ] Add a new argument with default value
  - [ ] Change type of function argument? How would we fix up the callsites? (e.g. add(int) to add(float) and callsites must be add(toFloat($1)))
  - [ ] Continuous testing - for each edit figure out what tests are impacted and re-run them
- [ ] Add a todo keyword that always checks (and hover reveals its inferred type)
- [ ] Literals
  - [x] Integers (should have type base.Integer)
  - [ ] Strings (should have type base.String)
  - [ ] Floats (should have type base.Float)
  - [ ] Sets
  - [ ] Maps
  - [ ] arithmetic operators (infer based on argument type, promote int to float in case they’re different) (+,-,/,\*)
- [ ] Optimisations
  - [ ] Relevance checker (eliminate arguments that are irrelevant at runtime by counting the number of times they’re used)
  - [ ] Count the number of times a definition is referenced
    - [ ] If zero, omit
    - [ ] If once, then inline into the caller
- [ ] Interfaces
  - [ ] e.g. Set -> HashSet / LinkedHashSet / TreeSet
  - [ ] Java-style interface+implementation
- [ ] Integrated time travel debugger (state snapshotting)
- [ ] Hot reloading code
- [ ] Calculate a dependency graph of references s.t. when typechecking we can do a topological sort so we never need to re-check terms. (Also needed for correctness: see the definition-order bug in the review section.)
- [ ] Add formal typing rules to GitHub repo.
