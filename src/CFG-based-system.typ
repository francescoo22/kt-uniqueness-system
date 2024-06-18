= CFG Based System

Basic rules for Uniqueness and Borrowing won't change here,
but adapted to fit the CFG representation of Kotlin.

The key gap between the CFG version and the type rules is at the function call.
Type checking at function calls need adjustment so that it can be done in control flow order.
The support for recursive function all is alse missing is previous typing rules.

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

