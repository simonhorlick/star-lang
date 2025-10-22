# Rules

reference: https://www.cs.tufts.edu/comp/105-2019f/reduction.pdf

The evaluation of a function application `((x) <body>)(<arg>)` is the function's `<body>`, with all occurrences of x replaced by `<arg>`

```
((x) f)(a)
---------- beta-reduction
f[x <- a]
```

Example:

Bool is a dependent function with three inputs:

Another function P that takes a Bool value and returns a Type (like Foo.type). Functions that take values of a type and return Type are also called "propositions" (hence the name P) over that type.

A value that is the type of proposition P over Bool.true

A value that is the type of proposition P over Bool.false

The value returned by Bool is proposition P over whatever the value of the bool :: Bool is.

```
type Bool = ιx. (P: Bool -> Type) -> P(true) -> P(false) -> P(x)
true() Bool = (P) (t) (f) t
false() Bool = (P) (t) (f) f
not(b Bool) Bool = b(false)(true)
```

true is typeable as Bool

```
true() Bool = (P) (t) (f) t
true() ιx. (P: Bool -> Type) -> P(true) -> P(false) -> P(x) = (P) (t) (f) t
```

beta reduction:

```
not(true)
((b) b(false)(true))(true) -- deref `not`
true(false)(true)          -- subst `b` by `true`
((t) (f) t)(false)(true)   -- deref `true`
((f) false)(true)          -- subst `t` by `false`
false                      -- subst `f` by `true`
(t) (f) f                  -- deref `false`
```
