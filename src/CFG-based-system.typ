#import "./proof-tree.typ": *
#import "./vars.typ": *
#import "@preview/commute:0.2.0": node, arr, commutative-diagram
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
      "TA" &::= "$"i := p, "$i for implicit registers" \
      "F" &::= f("$"1: af beta, ..., "$"n: af beta): af \
      "Join" &::= j \
    $
  ),
  frame-box(
    $
      alpha &::= unique | shared | top \
      beta &::= dot | borrowed \
      Delta &::= dot | p : alpha beta, Delta \
      l &:== dot | (p | alpha beta , l) \
      Gamma &::= dot | i : l, Gamma
    $
  )
)

Rules for CFA is defined on control flow graph, where edges are associated with contexts, and nodes for expressions or statements.

We follow the original lattice for control flow analysis.
#figure(image(width: 25%, "./img/lattice.svg"), caption: [Lattice in Control Flow Analysis])<CFA-lattice>

In Kotlin CFG, $"$"i = "eval" e$, is a common pattern that appears everywhere.
In #link("https://kotlinlang.org/spec/control--and-data-flow-analysis.html#control-flow-graph")[Kotlin specification],
the left hand side of such an assignment is an implicit register.

The best property of the implicit register is that it should be assigned only once, unless it appears in two disjoint branches across the whole CFG,
thus there is no need for us to track its scope, or care about update.

We distinguish this case with assignment statement and call this implicit assignment.
The implicit registers does not take the ownership of the value, but just store an aliasing information.
We introduce an extra context $Gamma$ for CFA to track aliasing happening at implicit assignment.
Notice that $Gamma$ is a list of aliasing information or uniqueness level, as we might have multiple aliasing possibilities from different branches of CFG.

Rule for CFA are as follows on different nodes in CFG that does not appear in the grammar.
#display-rules(row-size: 1,
prooftree(
  axiom($Gamma'= i: (p, dot), Gamma$),
  rule(label: "implicit assign path", $Gamma, Delta tack.r "$"i := p tack.l Gamma', Delta$),
),
prooftree(
  axiom($Gamma'= i:, Gamma(j), Gamma$),
  rule(label: "implicit assign implicit", $Gamma, Delta tack.r "$"i := "$"j tack.l Gamma', Delta$),
),
prooftree(
  axiom($Gamma'= i:, (alpha beta, dot), Gamma$),
  rule(label: "implicit assign function call", $Gamma, Delta tack.r "$"i := f(...) alpha beta tack.l Gamma', Delta$),
),
prooftree(
  axiom($forall i, j: exists p_i in Gamma("$"i) p_j in Gamma("$"j), p_i subset.sq p_j => (a_i^m = a_j^m = shared)$),
  axiom($Gamma' Delta' = "normalize'" Gamma Delta$),
  axiom($Lub Gamma'("$"i).alpha beta <= alpha_i beta_i$),
  rule(n: 3, label: "Function call", $Gamma, Delta tack.r f("$"1: alpha_1 beta_1, ..., "$"n: alpha_n beta_n) tack.l Gamma', Delta'$),
),
prooftree(
  axiom($Delta' = "unify "Delta_1, Delta_2$),
  axiom($Gamma' = lub' Gamma_1, Gamma_2$),
  axiom($Gamma'' = "$result": Gamma'("$2"), Gamma'$),
  rule(n:3, label: "join",
    $(Gamma_1, Delta_1) | (Gamma_2, Delta_2) tack.r "$result" = "$2" tack.l Gamma'', Delta'$),
)
)

=== Unification
#align(left)[#commutative-diagram(
  node-padding: (50pt, 50pt),
  node((0, 0), $I$),
  node((1, 0), $L$),
  node((1, 1), $R$),
  node((2, 1), $"$result=$2"$),
  node((3, 1), $O$),
  arr($I$, $L$, $Gamma_0, Delta_0$),
  arr($I$, $R$, $Gamma_0, Delta_0$),
  arr($L$, (2,1), $Gamma_1, Delta_1$),
  arr($R$, (2,1), $Gamma_2, Delta_2$),
  arr((2,1), $O$, $Gamma'', Delta'$),
)]

Unification for full $Gamma$ don't need to care about scope too much, as each implicit register is assigned only once.

$lub' Gamma_1 Gamma_2$ does pointwise $lub$, if both $Gamma_1("$i"), Gamma_2("$i")$ are uniqueness level,
otherwise, it concatenates the two lists $Gamma_1("$i"), Gamma_2("$i")$
but *keep* $x: alpha_x beta_x$ if it appears in only one of $Delta_1$ or $Delta_2$.

=== Normalization with $Gamma$ and $Delta$
#display-rules(
    prooftree(
      axiom($Delta' = "normalize"(p_1: alpha_1 beta_1, ..., p_n: alpha_n beta_n)$),
      rule(label: "N-finish", $Gamma, Delta tack.r "normalize"'(p_1: alpha_1 beta_1, ..., p_n: alpha_n beta_n) tack.r Gamma Delta'$)
    ),
    prooftree(
      axiom($Delta' = Lub_(k in Gamma("$"i.p)) "normalize"'(p_1: alpha_1 beta_1, ..., k: alpha_1 beta_1, ..., "$"n: alpha_n beta_n)$),
      rule(label: "N-rec", $Gamma, Delta tack.r "normalize'"(p_1: alpha_1 beta_1, ... "$"i: alpha_i beta_i, ... "$"n: alpha_n beta_n tack.r Gamma, Delta'$),
    ),
)

== Examples for nested function calls

CFG for function call is represented first eval the arguments sequentially and then call the function.
Consider the following example:

```kt
fun l(x: b shared) shared
fun h(x: b shared) shared
fun g(x: b shared) shared
fun f(x: b shared, y: shared, z: shared, w: shared) shared
fun use_f (x: unique) {
    f(x, g(h(x)), l(x), x)
}
```
#commutative-diagram(
    node-padding: (50pt, 40pt),
    node((0, 0), $I$),
    node((1, 0), $"$1:=x"$),
    node((2, 0), $"$2:=x"$),
    node((3, 0), $"$3:=h($2)"$),
    node((4, 0), $"$4:=g($3)"$),
    node((5, 0), $"$5:=l($1)"$),
    node((6, 0), $"$6:=x"$),
    node((7, 0), $"$result:=f($1, $4, $5, $6)"$),
    node((8, 0), $O$),
    arr($I$, (1, 0), ${}_Gamma, {x:unique}_Delta$),
    arr((1,0), (2, 0), ${"$1":x}_Gamma, {x:unique}_Delta$),
    arr((2,0), (3, 0), ${"$2":x, "$1":x}_Gamma, {x:unique}_Delta$),
    arr((3,0), (4, 0), ${"$3":shared, "$2":x, "$1":x}_Gamma, {x:unique}_Delta$),
    arr((4,0), (5, 0), ${"$4":shared, "$3":shared, "$2":x, "$1":x}_Gamma, {x:unique}_Delta$),
    arr((5,0), (6, 0), ${"$5":shared, "$4":shared, "$3":shared, "$2":x, "$1":x}_Gamma, {x:unique}_Delta$),
    arr((6,0), (7, 0), ${"$6":x, "$5":shared, "$4":shared, "$3":shared, "$2":x, "$1":x}_Gamma, {x:unique}_Delta$),
    arr((7,0), (8, 0), ${"$result":shared, "$6":x, "$5":shared, "$4":shared, "$3":shared, "$2":x, "$1":x}_Gamma\ {x:shared}_Delta$),
)

== Examples with multiple branches
```kt
fun f(x: unique): shared
fun use_f(x: unique, y: unique, z: shared) {
    f(if (x) y else z)
}
```

#align(center)[#commutative-diagram(
    node-padding: (50pt, 50pt),
    node((0, 1), $I$),
    node((1, 1), $"$1:=x"$),
    node((2, 1), "assume $1"),
    node((1, 3), $""$),
    node((2, 3), "assume !$1"),
    node((3, 1), $"$2:=y"$),
    node((3, 3), $"$2:=z"$),
    node((4, 1), $"$3:=$2"$),
    node((4, 3), $""$),
    node((5, 1), $"$result:=f($3)"$),
    node((6, 1), $O$),

    arr(label-pos:right, $I$,   (1, 1), ${}_Gamma\ {x:unique, y:unique, z:shared}_Delta$),
    arr(label-pos:right, (1,1), (2, 1), ${"$1":x}_Gamma\ {x:unique, y:unique, z:shared}_Delta$),
    arr(label-pos:right, (2,1), (3, 1), ${"$1":x}_Gamma\ {x:unique, y:unique, z:shared}_Delta$),
    arr(label-pos:right, (3,1), (4, 1), ${"$2":y, "$1":x}_Gamma\ {x:unique, y:unique, z:shared}_Delta$),

    arr((1,1), (1, 3), ""),
    arr((1,3), (2, 3), ${"$1":x}_Gamma\ {x:unique, y:unique, z:shared}_Delta$),
    arr((2,3), (3, 3), ${"$1":x}_Gamma\ {x:unique, y:unique, z:shared}_Delta$),
    arr((3,3), (4, 3), ${"$2":z, "$1":x}_Gamma\ {x:unique, y:unique, z:shared}_Delta$),
    arr((4,3), (4, 1), $$),
    arr((4,1), (5, 1), ${"$3":[x, z], "$2":[x,z], "$1":x}_Gamma\ {x:unique, y:unique, z:shared}_Delta$),
    arr((5,1), (6, 1), $"Error: $3 is " unique "or" shared ", while expected to be " unique$),
)]
