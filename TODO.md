Star roadmap

Basic requirements for a first release version.

Tooling

- [ ] Inspect shouldn’t need to calculate the type of a lambda abstraction (it should be annotated by the checker)

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

- [ ] Add final AST syntax for “indexed” types like Vector
- [ ] auto-infer function properties (functor, applicative, semigroup) and display in the editor
- [ ] ide: apply function to term: select a term, type the function name, term is now passed as an argument to that function and the function is inserted correctly in the source. (see codeaction in lsp)
- [ ] ide: rename symbols (see https://microsoft.github.io/language-server-protocol/specifications/specification-3-15/#textDocument_rename)
- [ ] have the editor insert "todo"s when writing (i.e. try and keep the AST syntax reasonable)
- [ ] ide: constructors in case statements don't have syntax highlighting
- [ ] ide: find references
- [ ] ide: jump to definition
- [ ] bug: infinite loops in the checker when argument length mismatch or type mismatch.
  - [ ] probably need kind check of some sort
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
- [ ] implement an Equal type
- [ ] double negation proof
- [ ] have a flag for enabling parsing of self types (for debugging)
- [ ] do notation
- [ ] Pipeline syntax using a ▷ (I.e. |>)
- [ ] IDE: autocomplete should suggest values from the context whose types fit the hole first
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
- [ ] Calculate a dependency graph of references s.t. when typechecking we can do a topological sort so we never need to re-check terms.
- [ ] Add formal typing rules to GitHub repo.
