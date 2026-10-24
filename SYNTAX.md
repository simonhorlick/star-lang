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
branches are matched to constructors by name, so they may be written in any
order; every constructor must have exactly one branch.
```

```
case n of
  | zero => true
  | succ => (
    case m of
      | zero => false
      | succ => lte(n.n,m.n))
    ↑
    nested case destructuring
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
type Bool = true | false
↑
sum type

type Nat = zero | succ(x Nat)
↑
with constructor arguments

type List(A \*) = nil | cons(head A, tail List(A))
↑
with type parameters

type List(A \*) = nil | cons(head A, tail List(A))
↑
with type parameters

type VectBool(sz Nat) = 
  vbnil : VectBool(zero) | 
  vbext(n Nat, head Bool, tail VectBool(n)) : VectBool(succ(n))
↑
indexed type

type Equal(A *, a A, b A) = refl : Equal(A, a, a)
↑
indexed type with parameters
a type argument that every constructor returns unchanged (A and a) is a
parameter and is in scope in every constructor; one that varies between
constructors (b) is an index, which every constructor must supply in its
return type.
```

```
func not:Bool->Bool = λb if b then false else true
func not(b Bool) Bool = if b then false else true
↑
definition
```
