#import "../../proof-tree.typ": *
#import "../../vars.typ": *

// ************** Annotations Relations **************

#let A-id = prooftree(
  axiom($$),
  rule(label: "A-Id", $alpha beta rel alpha beta$),
)

#let A-trans = prooftree(
  axiom($alpha beta rel alpha' beta'$),
  axiom($alpha' beta' rel alpha'' beta''$),
  rule(n:2, label: "A-Trans", $alpha beta rel alpha'' beta''$),
)

#let A-bor-sh = prooftree(
  axiom($$),
  rule(label: "A-Bor-Sh", $shared borrowed rel top$),
)

#let A-sh = prooftree(
  axiom($$),
  rule(label: "A-Sh", $shared rel shared borrowed$),
)

#let A-bor-un = prooftree(
  axiom($$),
  rule(label: "A-Bor-Un", $unique borrowed rel shared borrowed$),
)

#let A-un-1 = prooftree(
  axiom($$),
  rule(label: "A-Un-1", $unique rel shared$),
)

#let A-un-2 = prooftree(
  axiom($$),
  rule(label: "A-Un-2", $unique rel unique borrowed$),
)

// ************** Parameters Passing **************

#let Pass-Bor = prooftree(
  axiom($alpha beta rel alpha' borrowed$),
  rule(label: "Pass-Bor", $alpha beta ~> alpha' borrowed ~> alpha beta$)
)

#let Pass-Un = prooftree(
  axiom($$),
  rule(label: "Pass-Un", $unique ~> unique ~> top$)
)

#let Pass-Sh = prooftree(
  axiom($alpha rel shared$),
  rule(label: "Pass-Sh", $alpha ~> shared ~> shared$)
)