# star

Star is a fast, modern and sound programming language.

## Syntax

### Functions

```
func not:Bool->Bool = λb if b then false else true
```

```
not(true) // is false
```

### Abstract data types

ADTs allow for user-defined data types. In fact, all types in Star are
user-defined.

```
type <Type name>(<Type arguments>) = <Constructor1> | <Constructor2>(<Constructor2 args>) | ... | <ConstructorN>
```

Example:

```
// Nat is the type of Church numerals. It's either zero, or the successor of
// some lower numeral.
type Nat = zero | succ(x Nat)
```

Star creates constructor functions for each constructor of an ADT. For example,
the functions `zero` and `succ` are provided to allow you to create values of
type Nat.

```
let z = zero
let one = succ(z)
let two = succ(one)
let three = succ(two)
```

You can eliminate values of types by pattern matching over their constructors.
In each branch of the case statement the constructor arguments are available
using the dot notation. In the succ constructor for Nat, succ takes an argument
`x`, so now in the succ branch of the case statement we can access n.x. In the
zero branch no such argument is available, so n.x in that branch would result in
a compile error.

```
func prev:Nat->Nat = λn
  case n of
  | zero => zero
  | succ => n.x
```

### Literals

```
0,1,2 - numeric literals
"hello" - string literals
[1,2,3] - list literals
```
