#import "./proof-tree.typ": *
#import "./vars.typ": *
= CFG Based System

Basic rules for Uniqueness and Borrowing won't change here,
but adapted to fit the CFG representation of Kotlin.

The key gap between the CFG version and the type rules is at the function call.
Type checking at function calls need adjustment so that it can be done in control flow order.
The support for recursive function all is alse missing is previous typing rules.

== Formalization

We follow the original lattice for control flow analysis.
#figure(image(width: 25%, "./img/lattice.svg"), caption: [Lattice in Control Flow Analysis])<CFA-lattice>

The context for CFA $Gamma$ is defined as: a mapping from path to the lattice:
$ Gamma : p -> U $, $U$ for uniqueness and borrowing level.

In Kotlin CFG, $"$"i = "eval" e$, is a common pattern that appears everywhere, we distinguish this case with assignment statement when rhs is a path: define context $Delta$ for case $"$"i = "eval" p$ temp variables to the corresponding path and lattice, to make it simple here, we define it as a list:
$ Delta : (i, p, U) $
When the rhs is not a variable or path, we store $(i, *, U)$.

Rule for CFA are as follows on different nodes in CFG:
#prooftree(
  axiom($Delta'= (i, p, Gamma(p)) :: Delta$),
  rule(label: "Temp assignment path", $Gamma, Delta tack.r "$"i := p tack.l Gamma, Delta'$),
)

#prooftree(
  axiom($Delta'= (i*, "Eval"(f)) :: Delta$),
  rule(label: "Temp assignment non-path", $Gamma, Delta tack.r "$"i := f tack.l Gamma, Delta'$),
)

#prooftree(
  axiom($Delta("$"i).3 <= "U"i$),
  axiom("Do normalization with alias infomation in Delta"),
  rule(n: 2, label: "Function call", $Gamma, Delta tack.r f("$"1: "U"1, ..., "$"n: "U"n) tack.l Gamma', Delta$),
)

#prooftree(
  axiom($"Unification "Gamma_1, Gamma_2$),
  axiom($Delta'= ("result", ("$"1, "$"2), Gamma("$"1) lub Gamma("$"2)) :: Delta$),
  rule(n:2, label: "CFG Join Node for Expression(if/when)", $Gamma_1, Delta_1 tack.r "$result" := "$2" join Gamma_2, Delta_2 tack.r "$result" := "$2" tack.l Gamma', Delta'$),
)

Here $("$"1, "$"2)$ means we keep both alias, when one of them is $*$, we keep the other one.

== Examples for recursive function call
- Example with multiple call with unique
```kt
// Should report error
fun f(x: unique, y: unique)
fun use_f(x: unique) {
  f (x, x)
}
```
- Example with multiple call with shared
```kt
// Should report error
fun f(x: shared, y: unique)
fun use_f(x: unique) {
  f (x, x)
}
```
- Example with unique and borrowed
```kt
// Should report error
fun f(x: unique, y: b) // b for either shared or unique borrow
fun use_f(x: unique) {
  f (x, x)
}
```
- Example with unique and nested borrowed
```kt
// Should pass
fun f(x: unique, y) // no notation for any uniqueness or borrowing
fun g(x: b)
fun use_f(x: unique) {
  f (x, g(x))
}
```
- Example with unique and nested share
```kt
// Should report error
fun f(x: unique, y)
fun g(x: shared)
fun use_f(x: unique) {
  f (x, g(x))
}
```
- Example with Shared and nested unique or borrowed unique
```kt
// Should report error for first, but not second
fun f(x: shared, y)
fun g1(x: unique)
fun g2(x: b unique)
fun use_f(x: unique) {
  f (x, g1(x))
  f (x, g2(x))
}
```
- Example with b unique and anything
```kt
// Should report error
fun f(x: b unique, y)
fun use_f(x: unique) {
  f (x, x)
}
```

== CFG for function call

CFG for function call is represented first eval the arguments sequentially and then call the function.
Consider the following example:

```kt
fun use_f (x: Unique) {
    f(x, g(h(x)), l(x), x)
}
```

The CFG looks like:
$ &"$1" := x \
  &-> "$2" := x -> "$3" := h("$2") -> "$4" := g("$3") \
  &-> "$5" := x -> "$6" := l("$5") \
  &-> "$7" := x \
  &-> "$result" := f("$1", "$4", "$6", "7") $

Checking, unification(in terms of typing rule) and uniqueness update does not happen at assign stage, but on the function evaluation.

This tells that the sequence of nested functions affect the final result:
```kt
fun g1(x: b Unique)
fun g2(x: Unique)
fun f(x, y)
fun use_f(x: Unique) {
    f (g1(x), g2(x)) // Ok
    f (g2(x), g1(x)) // Fail
}
```

Ths issue here is that Kotlin CFA might not be able to distinguish normal assignment and this particular case.
Consider the following example:
```kt
fun f(x: Unique, y)
fun g(x: b Unique)
fun use_f(x: Unique) {
    f(x, g(x))
}
```

The CFG for this will look like:
$ &"$1" := x \
  &-> "$2" := x \
  &-> "$3" := g("$2") \
  &-> "$result" := f("$1", "$3") $

Suppose we use the rules for assignment here:

$ & &{x: "Unique"} \
  &"$1" := x &{x: top, "$1": "Unique"} \ 
  &-> "$2" := x &{"Error"} \
  &-> "$3" := g("$2") \
  &-> "$result" := f("$1", "$3") $

While what we really want is:
$ & &{x: "Unique"} \
  &"$1" := x &{x: "Unique", "$1": "Unique"} \ 
  &-> "$2" := x &{x : "Unique", "$2": "Unique"} \
  &-> "$3" := g("$2") &{x : "Unique", "$2": "Unique", "$3": bot}\
  &-> "$result" := f("$1", "$3") &{x: top} $

Three possible ways to solve this:
1. Is it possible to infer this case
2. SSA this case
3. Fully disable this behavior

