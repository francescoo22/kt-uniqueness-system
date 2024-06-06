#import "../../proof-tree.typ": *
#import "../../vars.typ": *

// *********** Unify ***********

// #let U-Empty = prooftree(
//   axiom($$),
//   rule(label: "U-Empty", $unify(Delta, dot, dot) = dot$),
// )

// #let U-Sym = prooftree(
//   axiom($$),
//   rule(label: "U-Sym", $unify(Delta, Delta_1, Delta_2) = unify(Delta, Delta_2, Delta_1)$),
// )

// #let U-Local = {
//   let a1 = $root(p) = x$
//   let a2 = $x in.not Delta$
//   let a3 = $unify(Delta, Delta_1, Delta_2) = Delta'$
//   prooftree(
//     stacked-axiom(
//       (a1, a2),
//       (a3, ),
//     ),
//     rule(label: "U-Local", $unify(Delta, (p: alpha beta, Delta_1), Delta_2) = Delta'$),
//   )
// }

// #let U-Rec = {
//   let a1 = $root(p) = x$
//   let a2 = $x in Delta$
//   let a3 = $Delta_1 without p = Delta'_1$
//   let a4 = $Delta_2 without p = Delta'_2$
//   let a5 = $Delta_1(p) = alpha_1 beta_1$
//   let a6 = $Delta_2(p) = alpha_2 beta_2$
//   let a7 = $Lub{alpha_1 beta_1, alpha_2 beta_2} = alpha' beta'$
//   let a8 = $unify(Delta, Delta'_1, Delta'_2) = Delta'$
//   prooftree(
//     stacked-axiom(
//       (a1, a2),
//       (a3, a4),
//       (a5, a6),
//       (a7, a8)
//     ),
//     rule(label: "U-Rec", $unify(Delta, (p: alpha beta, Delta'_1), Delta'_2) = p: alpha' beta', Delta'$),
//   )
// }


#let Ctx-Lub-Empty = prooftree(
  axiom($$),
  rule(label: "Ctx-Lub-Empty", $dot space lub space dot space = space dot$),
)

#let Ctx-Lub-Sym = prooftree(
  axiom($$),
  rule(label: "Ctx-Lub-Sym", $Delta_1 lub Delta_2 = Delta_2 lub Delta_1$),
)

#let Ctx-Lub-1 = prooftree(
  axiom($Delta_2 inangle(p.f) = alpha'' beta''$),
  axiom($Delta_2 without p.f = Delta'_2$),
  axiom($Delta_1 lub Delta'_2 = Delta'$),
  axiom($Lub{alpha beta, alpha'' beta''} = alpha' beta'$),
  rule(n:4, label: "Ctx-Lub-1", $(p.f : alpha beta, Delta_1) lub Delta_2 = p.f : alpha' beta', Delta'$),
)

#let Ctx-Lub-2 = prooftree(
  axiom($x in.not Delta_2$),
  axiom($Delta_1 lub Delta_2 = Delta'$),
  rule(n:2, label: "Ctx-Lub-2", $(x : alpha beta, Delta_1) lub Delta_2 = x : top, Delta'$),
)

#let Ctx-Lub-3 = prooftree(
  axiom($Delta_2 inangle(x) = alpha'' beta''$),
  axiom($Delta_2 without x = Delta'_2$),
  axiom($Delta_1 lub Delta'_2 = Delta'$),
  axiom($Lub{alpha beta, alpha'' beta''} = alpha' beta'$),
  rule(n:4, label: "Ctx-Lub-3", $(x : alpha beta, Delta_1) lub Delta_2 = x : alpha' beta', Delta'$),
)

#let Remove-Locals-Base = prooftree(
  axiom($$),
  rule(label: "Remove-Locals-Base", $dot triangle.filled.small.l Delta = dot$),
)

#let Remove-Locals-Keep = prooftree(
  axiom($root(p) = x$),
  axiom($Delta_1 inangle(x) = alpha beta$),
  axiom($Delta triangle.filled.small.l Delta_1 = Delta'$),
  rule(n:3, label: "Remove-Locals-Keep", $p : alpha beta, Delta triangle.filled.small.l Delta_1 = p : alpha beta, Delta'$),
)

#let Remove-Locals-Discard = prooftree(
  axiom($root(p) = x$),
  axiom($x in.not Delta_1$),
  axiom($Delta triangle.filled.small.l Delta_1 = Delta'$),
  rule(n:3, label: "Remove-Locals-Keep", $p : alpha beta, Delta triangle.filled.small.l Delta_1 = Delta'$),
)

#let Unify = prooftree(
  axiom($Delta_1 lub Delta_2 = Delta_lub$),
  axiom($Delta_lub triangle.filled.small.l Delta = Delta'$),
  rule(n:2, label: "Unify", $unify(Delta, Delta_1, Delta_2) = Delta'$),
)

// *********** Normalize ***********

#let N-Empty = prooftree(
  axiom($$),
  rule(label: "N-Empty", $norm(dot) = dot$)
)

#let N-Rec = prooftree(
  axiom($Lub(alpha_i beta_i | p_i = p_0 and 0 <= i <= n) = ablub$),
  axiom($norm(p_i: alpha_i beta_i | p_i != p_0 and 0 <= i <= n) = p'_0 : alpha'_0 beta'_0, ..., p'_m : alpha'_m beta'_m$),
  rule(n:2, label: "N-rec", $norm(p_0\: alpha_0 beta_0, ..., p_n\: alpha_n beta_n) = p_0 : ablub, p'_0 : alpha'_0 beta'_0, ..., p'_m : alpha'_m beta'_m$)
)
