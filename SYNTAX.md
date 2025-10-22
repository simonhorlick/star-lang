# SYNTAX

```
1
↑
integer literal
```

```
[1,2]
↑
list literal
```

```
a
↑
reference
```

```
a + b
  ↑
integer addition
left associative: a + b + c == (a + b) + c  [== a + (b + c)]
```

```
a - b
  ↑
integer subtraction
left associative: a - b - c == (a - b) - c
```

```
a * b
  ↑
integer multiplication
left associative: a * b * c == (a * b) * c  [== a * (b * c)]
```

```
a / b
  ↑
integer division
left associative: a * b * c == (a * b) * c  [== a * (b * c)]
```

```
-a
↑
unary negation
```

```
a * (b + c)
    ↑
parenthesis
```

```
a(b)
 ↑
infix application operator
left associative: a(b)(c) == (a(b))(c)
```

```
f(x,y)
   ↑
commas to separate arguments
```

```
a : b
  ↑
infix type annotation
left associative: a : b : c == (a : b) : c
```

The following is another syntax for the pi type `Π_:a -> b`.

```
a -> b
  ↑
infix arrow
right associative: a -> b -> c == a -> (b -> c)
```

```
(a:A) -> B(a)
↑
dependent function type
```

```
f . g
  ↑
infix function composition
right associative: f . g . h == f . (g . h)
```

```
xs[i]
  ↑
list indexing operator
```

```
as ++ bs
   ↑
list concatenation operator
[not important] left associative: a ++ b ++ c == (a ++ b) ++ c
```

```
a && b
  ↑
logical and operator
[not important] left associative: a && b && c == (a && b) && c
```

```
a || b
  ↑
logical or operator
[not important] left associative: a || b || c == (a || b) || c
```

```
a < b
a <= c
a > d
a >= e
numeric comparison operators
```

```
if x then y else z
↑
if-then-else expression
```

```
case x of
  a => y
  b => z
↑
case destructuring
```

```
case returnTy of
  a => y => z
  b => z =>
  a => c
↑
ambiguous case? (mandate parentheses for multi-line expressions?)
```

```
case returnTy of
  a => y => z
  b => (z =>
  a => c)
```

```gleam
  let result = case x {
    // Match specific values
    0 -> "Zero"
    1 -> "One"

    // Match any other value
    _ -> "Other"
  }
```

```
let b = f(x) in a
↑
let binding
```

```
"hello"
↑
string literal
```

```
*
↑
type-of-types
```

```
ιx t
↑
self type
[internal only: to be removed]
```

```
type Bool = true | false
↑
sum type

type Nat = zero | succ(x Nat)
↑
with constructor arguments

type List(A \*) = nil | cons(head A, tail List(A))
↑
with type parameters

```

```

func not:Bool->Bool = λb if b then false else true
func not(b Bool) Bool = if b then false else true
↑
definition

```

```

func sub(n Nat, m Nat) Nat =
  case m of
    zero => n
    succ => (
      case n of
        zero => 0
        succ => sub(n.x,m.x)
    )
↑
nested case expressions

```
