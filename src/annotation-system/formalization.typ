#import "rules/base.typ": *
#import "rules/relations.typ": *
#import "rules/unification.typ": *
#import "rules/statements.typ": *
#import "../vars.typ": *
#show raw.where(block: true): frame-box
#show link: set text(fill: rgb(0, 0, 255))
#show link: underline
#set heading(numbering: "1.")

= Formalization

// TODO: be more precise when an annotation cannot be borrowed (e.g. method type can be ... -> alpha)
// TODO: since there isn't a borrowed-Top, maybe the context can be re defined in a way s.t. borrowed top doesn't even exist
#v(1em)
#grid(
  columns: (auto, auto),
  column-gutter: 2em,
  row-gutter: 1em,
  [*Grammar*],[*Context*],
  frame-box(
    $
      CL &::= class C(overline(f\: alpha_f)) \
      af &::= unique | shared \
      beta &::= dot | borrowed \
      M &::= m(overline(af beta space x)): af {begin_m; overline(s); ret_m e} \
      p &::= x | p.f \
      e &::= null | p | m(overline(p)) \
      s &::= var x | p = e |  fi p_1 == p_2 then overline(s_1) els overline(s_2) | m(overline(p)) \ &| loop p_1 == p_2 do overline(s)
    $
  ),
  frame-box(
    $
      alpha &::= unique | shared | top \
      beta &::= dot | borrowed \
      Delta &::= dot | p : alpha beta, Delta
    $
  )
)

- Only *fields*, *method parameters*, and *return values* have to be annotated.
- A reference annotated as `unique` may either be `null` or point to an object, and it is the sole *accessible* reference pointing to that object.
- A reference marked as `shared` can point to an object without being the exclusive reference to that object.
- `T` is an annotation that can only be inferred and means that the reference is *not accessible*.
- $borrowed$ (borrowed) indicates that the function receiving the reference won't create extra aliases to it, and on return, its fields will maintain at least the permissions stated in the class declaration. 
- Annotations on fields indicate only the default permissions, in order to understand the real permissions of a fields it is necessary to look at the context. This concept is formalized by rules in @cap:paths and shown in @field-annotations.
- Primitive fields are not considered
- `this` can be seen as a parameter
- constructors can be seen as functions returning a `unique` value

== General

#display-rules(
  M-Type, M-Args
)

== Context

- The same variable/field cannot appear more than once in a context.
- Contexts are always *finite*
- If not present in the context, fields have a default annotation that is the one written in the class declaration

#display-rules(
  Not-In-Base, Not-In-Rec,
  Ctx-Base, Ctx-Rec,
  Root-Base, Root-Rec,
  Lookup-Base, Lookup-Rec,
  Lookup-Default, "",
  Remove-Empty, Remove-Base,
  Remove-Rec, "",
)

== SubPaths

If $p_1 subset.sq p_2$ holds, we say that 
- $p_1$ is a *sub*-path of $p_2$
- $p_2$ is a *sup*-path of $p_1$

#display-rules(
  SubPath-Base, SubPath-Rec,
  SubPath-Eq-1, SubPath-Eq-2,
  Remove-SupPathsEq-Empty, Remove-SupPathsEq-Discard,
  Remove-SupPathsEq-Keep, Replace,
  Get-SupPaths-Empty, "",
  Get-SupPaths-Discard, "",
  Get-SupPaths-Keep, "",
)

== Annotations relations

- $alpha beta rel alpha' beta'$ means that $alpha beta$ can be passed where $alpha' beta'$ is expected.

- $alpha beta ~> alpha' beta' ~> alpha'' beta''$ means that after passing a reference annotated with $alpha beta$ as argument where $alpha' beta'$ is expected, the reference will be annotated with $alpha'' beta''$ right after the method call.

#display-rules(
  row-size: 3,
  A-id, A-trans, A-bor-sh,
  A-sh, A-bor-un, A-un-1,
  A-un-2, Pass-Bor, Pass-Un,
  Pass-Sh
)

#figure(image(width: 25%, "../img/lattice.svg"), caption: [Lattice obtained by annotations relations rules])<annotation-lattice>

== Paths
<cap:paths>

- $Lub{alpha_0 beta_0, ..., alpha_n beta_n}$ identifies the least upper bound of the annotations based on the lattice in @annotation-lattice.
- Note that even if $p.f$ is annotated as unique in the class declaration, $Delta(p.f)$ can be shared (or $top$) if $Delta(p) = shared$ (or $top$)
- Note that fields of a borrowed parameter are borrowed too and they need to be treated carefully in order to avoid unsoundness. Specifically, borrowed fields:
  - Can be passed as arguments to other functions (if relation rules are respected).
  - Have to become `T` after being read (even if shared).
  - Can only be reassigned with a `unique`.
- Note that $(Delta(p) = alpha beta) => (Delta inangle(root(p)) = alpha' beta')$ i.e. the root is present in the context.
- $Delta tr std(p, alpha beta)$ means that paths rooted in $p$ have the right permissions when passing $p$ where $alpha beta$ is expected. To understand better why these rules are necessary look at the example in @path-permissions.
- Note that in the rule "Std-Rec-2" the premise $(x : alpha beta) (p') = alpha'' beta''$ means that the evaluation of $p'$ in a context in which there is only $x : alpha beta$ is $alpha'' beta''$

#display-rules(
  Get-Var, Get-Path,
  Std-Empty, Std-Rec-1,
  Std-Rec-2, "",
)

== Unification

- $Delta_1 lub Delta_2$ is the pointwise lub of $Delta_1$ and $Delta_2$
  - If a variable $x$ is present in only one context, it will be annotated with $top$ in $Delta_1 lub Delta_2$.
  - If a path $p.f$ is missing in one of the two contexts, we can just consider the annotation in the class declaration.
- $Delta sect.dot Delta_1$ is used to remove the paths that are locally declared in $Delta$
- $unify(Delta, Delta_1, Delta_2)$ means that we want to unify $Delta_1$ and $Delta_2$ starting from a parent environment $Delta$.
  - A path $p$ contained in $Delta_1$ or $Delta_2$ such that $root(p) = x$ is not contained $Delta$ will not be included in the unfication.
  - The annotation of variables contained in the unfication is the least upper bound of the annotation in $Delta_1$ and $Delta_2$.

#display-rules(
  // U-Empty, U-Sym,
  // U-Local, U-Rec,
  Ctx-Lub-Empty, Ctx-Lub-Sym,
  Ctx-Lub-1, "",
  Ctx-Lub-2, "",
  Ctx-Lub-3, "",
  Remove-Locals-Base, Remove-Locals-Keep,
  Remove-Locals-Discard, "",
  Unify, ""
)

== Normalization

- Normalization takes a list of annotated $p$ and retruns a list in which duplicates are substituted with the least upper bound.
- Normalization is required for method calls in which the same variable is passed more than once.

```kt
fun f(x: ♭ shared, y: shared)
fun use_f(x: unique) {
  // Δ = x: unique
  f(x, x)
  // Δ = normalize(x: unique, x:shared) = x: shared
}
```

#display-rules(
  N-Empty, "",
  N-Rec, ""
)

== Statements

#display-rules(
  Begin, "",
  Decl, Assign-Null,
  Seq-Base, Seq-Rec,
  If, "",
  Assign-Unique, "",
  Assign-Shared, "",
  Assign-Borrowed-Field, "",
  Assign-Call, "",
  Call, "",
  // Return-Null, "",
  Return-p, "",
  // Return-m, "",
)

*Note:* Since they can be easily desugared, there are no rules for returnning `null` or a method call.
- `return null` $equiv$ `var fresh ; fresh = null ; return fresh`
- `return m(...)` $equiv$ `var fresh ; fresh = m(...) ; return fresh`

The same can be done for the guard of if statements:
- `if (p1 == null) ...` $equiv$ `var p2 ; p2 = null ; if(p1 == p2) ...`
- `if (p1 == m(...)) ...` $equiv$ `var p2 ; p2 = m(...) ; if(p1 == p2) ...`

// #include "while-loops.typ"

#pagebreak()
= Examples

== Paths-permissions:

#figure(
```kt
class C()
class A(var f: @Unique C)

fun use_a(a: @Unique A)

fun f1(a: @Shared A){
  //  Δ = a: Shared 
  // ==>  Δ(a.f) = shared even if `f` is annotated ad unique
}

fun f2(a: @Unique A){
  //  Δ = a: Unique 
  // ==>  Δ(a.f) = Unique
  use_a(a)
  // after passing `a` to `use_a` it can no longer be accessed
  // Δ = a: T
  // Δ(a.f) = T even if `f` is annotated ad unique
}
```
)<field-annotations>

#figure(
```kt
class C()
class A(var f: @Unique C)

fun f(a: @Unique A)
fun use_f(x: @Unique A, y: @Unique A){
  // Δ = x: Unique, y: Unique
  y.f = x.f
  // Δ = x: Unique, y: Unique, x.f: T
  f(x) // error: 'x.f' does not have standard permissions when 'x' is passed
}
```
)<path-permissions>


== Call premises explaination:

- $forall 0 <= i <= n : Delta tr std(p_i, alpha^m_i beta^m_i)$ : \ We need all the arguments to have at least standard permissions for their fields.


- $forall 0 <= i, j <= n : (i != j and p_i = p_j) => alpha_i^m = shared$ : \ If the same variable/field is passed more than once, it can only be passed where shared is expected.
```kt
class C()
class A(var f: @Unique C)

fun f1(x: @Unique A, y: @Borrowed @Shared A)
fun f2(x: @Borrowed @Shared A, y: @Borrowed @Shared A)
fun f3(x: @Shared A, y: @Borrowed @Shared A)

fun use_f1(x: @Unique A){
  // Δ = x: Unique
  f1(x, x) // error: 'x' is passed more than once but is also expected to be unique
}

fun use_f2_f3(x: @Unique A){
  // Δ = x: Unique
  f2(x, x) // ok, uniqueness is also preserved since both the args are borrowed
  // Δ = x: Unique
  f3(x, x) // ok, but uniqueness is lost since one of the args is not borrowed
  // Δ = x: Shared
}
```

- $forall 0 <= i, j <= n : p_i subset.sq p_j => (Delta(p_j) = shared or a_i^m = a_j^m = shared)$ : \ Fields of an object that has been passed to a method can be passed too, but only if the nested one is shared or they are both expected to be shared.

```kt
class C()
class A(var f: @Shared C)
class B(var f: @Unique C)

fun f1(x: @Unique A, y: @Shared C) {}
fun use_f1(x: @Unique A) {
// Δ = x: Unique
    f1(x, x.f) // ok
// Δ = x: T, x.f: Shared
// Note that even if x.f is marked shared in the context,
// it is not accessible since Δ(x.f) = T
}

fun f2(x: @Unique B, y: @Shared C) {}
fun use_f2(b: @Unique B) {
// Δ = b: Unique
    f2(b, b.f) // error: 'b.f' cannot be passed since 'b' is passed as Unique and Δ(b.f) = Unique
// Δ(b.f) = Unique
// It is correct to raise an error since f2 expects x.f to be unique
}

fun f3(x: @Shared B, y: @Shared C) {}
fun use_f3(x: @Unique B) {
// Δ = x: Unique
    f3(x, x.f) // ok
// Δ = x: Shared, x.f: Shared
}
```

== Borrowed fields

Fields of a borrowed variable are borrowed too. But differently from variables, they can be read/written and so these operation require special rules.
- `Assign-Borrowed-Field` tells us what happens when reading a borrowed field. The most important thing to notice is that after being read, the field will be annotated with $top$, even if it is shared. Doing this is necessary to guarantee soundness while passing unique variables to functions expecting a borrowed shared argument.
- For the same reason, borrowed fields can only be re-assigned to something that is unique. Otherwise passing a unique to a function expecting a borrowed shared argument cannot guarantee that uniqueness is preserved.

```kt
class A(var n: Int)
class B(var a: @Unique A)

fun f(b: @Shared @Borrowed B) {
//    Δ = b : Shared Borrowed
    var temp = b.a
//    Δ = b : Shared Borrowed, b.a : T, temp: Shared

    // before returning, b needs to be in std form
    // but at this point it can only be re-assigned with a unique
    // re-assigning b.a with a shared would cause unsoundness to a caller passing a unique

    b.a = A(0)
//    Δ = b : Shared Borrowed, b.a : Unique, temp: Shared

    // now the function can return with no problems
}

fun use_f(b: @Unique B) {
//    Δ = b : Unique
    // also Δ(b.f) = Unique
    f(b)
//    Δ = b : Unique
    // moreover it is guaranteed that also Δ(b.a) = Unique
}
```

== Smart casts

Since if-statements guards cannot create new aliases, having a variable or a field access in the guard will not modify its uniqueness.

```kt
class T
class A(var t: @Unique T?)

fun use_t(t : @Shared @Borrowed T){
    
}

fun f(a1: @Unique @Borrowed A, a2 : @Shared @Borrowed A) {
//    Δ = a1 : Unique Borrowed, a2 : Shared Borrowed
    if (a1.t != null) {
    //    Δ = a1 : Unique Borrowed, a2 : Shared Borrowed
        use_t(a1.t) // here it is safe to smart cast because Δ(a1.t) = Unique (Borrowed)
    //    Δ = a1 : Unique Borrowed, a2 : Shared Borrowed
    }
    
//    Δ = a1 : Unique Borrowed, a2 : Shared Borrowed
    if(a2.t != null){
    //    Δ = a1 : Unique Borrowed, a2 : Shared Borrowed
        use_t(a2.t!!) // here it is NOT safe to smart cast because Δ(a2.t) = Shared (Borrowed)
    //    Δ = a1 : Unique Borrowed, a2 : Shared Borrowed
    }
}
```

== Stack example
This shows how the example presented in #link("https://arxiv.org/pdf/2309.05637.pdf")[LATTE] paper works with this system.
```kt
class Node(var value: @Unique Any?, var next: @Unique Node?)

class Stack(var root: @Unique Node?) {
    @Borrowed @Unique
    fun push(value: @Unique Any?) {
        // Δ = this: borrowed unique, value: unique

        val r = this.root
        // Δ = this: borrowed unique, this.root: T, value: unique, r: unique

        val n = Node(value, r)
        // Δ = this: borrowed unique, this.root: T, value: T, r: T, n: unique

        this.root = n
        // Δ = this: borrowed unique, this.root: unique, value: T, r: T, n: T
    }

    @Borrowed @Unique
    fun pop(): @Unique Any? {
        // Δ = this: borrowed unique
        
        val value: Any?
        // Δ = this: borrowed unique, value: T
        if (this.root == null) {
            value = null
            // Δ = this: borrowed unique, value: unique
        } else {
            value = this.root.value // Note: smart cast 'this.root' to Node
            // Δ = this: borrowed unique, this.root.value: T, value: unique

            val next = this.root.next  // Note: smart cast 'this.root' to Node
            // Δ = this: borrowed unique, this.root.value: T, this.root.next: T, value: unique, next: unique

            this.root = next
          // Δ = this: borrowed unique, this.root: unique, value: unique, next: T

            // Note: doing this.root = this.root.next works too
        }
        // Unification...
        // Δ = this: borrowed unique, this.root: unique, value: unique
        return value
    }
}
```