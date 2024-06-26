#import "./proof-tree.typ": *
#import "./vars.typ": *
= CFG Based System

Basic rules for Uniqueness and Borrowing won't change here,
but adapted to fit the CFG representation of Kotlin.

The key gap between the CFG version and the type rules is at the function call.
Type checking at function calls need adjustment so that it can be done in control flow order.
The support for nested function call is alse missing is previous typing rules.

== Formalization
#grid(
  columns: (auto, auto),
  column-gutter: 2em,
  row-gutter: 1em,
  [*CFG nodes not covered in Grammar*],[*Context*],
  frame-box(
    $
      af &::= unique | shared \
      beta &::= dot | borrowed \
      p &::= x | p.f \
      "TA" &::= "$"i := p, "TA for temp assignment" \
      "F" &::= f("$"1: af beta, ..., "$"n: af beta): af \
      "Join" &::= j \
    $
  ),
  frame-box(
    $
      alpha &::= unique | shared | top \
      beta &::= dot | borrowed \
      Delta &::= dot | p : alpha beta, Delta \
      Gamma &::= dot | i : Delta, Gamma
    $
  )
)


We follow the original lattice for control flow analysis.
#figure(image(width: 25%, "./img/lattice.svg"), caption: [Lattice in Control Flow Analysis])<CFA-lattice>

In Kotlin CFG, $"$"i = "eval" e$, is a common pattern that appears everywhere,
we distinguish this case with assignment statement and call this temp assignment.
We introduce an extra context $Gamma$ for CFA to track aliasing happening at temp assignment.
Notice that $Gamma$ is a list of aliasing information, as we might have multiple aliasing possibilities.

Rule for CFA are as follows on different nodes in CFG that does not appear in the grammar.
#display-rules(row-size: 1,
prooftree(
  axiom($Gamma'= i: (p, Delta(p), dot), Gamma$),
  rule(label: "Temp assignment path", $Gamma, Delta tack.r "$"i := p tack.l Gamma', Delta$),
),
prooftree(
  axiom($Gamma'= i:, Gamma(j), Gamma$),
  rule(label: "Temp assignment temp", $Gamma, Delta tack.r "$"i := "$"j tack.l Gamma', Delta$),
),
prooftree(
  axiom($forall i, j: exists p_i in Gamma("$"i) p_j in Gamma("$"j), p_i subset.sq p_j => (a_i^m = a_j^m = shared)$),
  axiom($Gamma' Delta' = "normalize'" Gamma Delta$),
  axiom($Lub Gamma'("$"i).alpha beta <= alpha_i beta_i$),
  rule(n: 3, label: "Function call", $Gamma, Delta tack.r f("$"1: alpha_1 beta_1, ..., "$"n: alpha_n beta_n) tack.l Gamma', Delta'$),
),
prooftree(
  axiom($Delta' = "unify "Delta_1, Delta_2$),
  axiom($Gamma' = "$2": Gamma_1("$2") lub' Gamma_2("$2")$),
  rule(n:2, label: "join",
    $Gamma_1, Delta_1, Gamma_2, Delta_2 tack.r "$result" = "$2" tack.l Gamma', Delta'$),
)
)

=== Unification
Unification for full $Gamma$ is never needed, as all temp assignment variables are local.

$lub' Delta_1 Delta_2$ does pointwise $lub$, but *keep* $x: alpha_x beta_x$ if it appears in only one of $Delta_1$ or $Delta_2$.

=== Normalization with $Gamma$ and $Delta$
#display-rules(
    prooftree(
      axiom($Delta' = "normalize"(p_1: alpha_1 beta_1, ..., p_n: alpha_n beta_n)$),
      rule(label: "N-Finish", $Gamma, Delta tack.r "normalize"'(p_1: alpha_1 beta_1, ..., p_n: alpha_n beta_n) = Delta'$)
    ),
    prooftree(
      axiom($Lub_(k in Gamma("$"i.p)) "normalize"'(p_1: alpha_1 beta_1, ..., k: alpha_1 beta_1, ..., "$"n: alpha_n beta_n)$),
      rule(label: "N-rec", $Gamma, Delta tack.r "normalize'"(p_1: alpha_1 beta_1, ... "$"i: alpha_i beta_i, ... "$"n: alpha_n beta_n)$),
    ),
)

== Examples for nested function calls

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

From our CFA, we have
$ & &{x: "Unique"} \
  &"$1" := x &{x: "Unique", "$1": "Unique"} \ 
  &-> "$2" := x &{x : "Unique", "$2": "Unique"} \
  &-> "$3" := g("$2") &{x : "Unique", "$2": "Unique", "$3": bot}\
  &-> "$result" := f("$1", "$3") &{x: top} $

== Examples with multiple branches

