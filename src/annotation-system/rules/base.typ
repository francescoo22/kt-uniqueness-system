#import "../../proof-tree.typ": *
#import "../../vars.typ": *

// ****************** General ******************

#let M-Type = prooftree(
  axiom($m(alpha_0 beta_0 x_0, ..., alpha_n beta_n x_n): alpha {begin_m; overline(s); ret_m e}$),
  rule(label: "M-Type", $mtype(m) = alpha_0 beta_0, ..., alpha_n beta_n -> alpha$),
)
  
#let M-Args = prooftree(
  axiom($m(alpha_0 beta_0 x_0, ..., alpha_n beta_n x_n): alpha {begin_m; overline(s); ret_m e}$),
  rule(label: "M-Args", $args(m) = x_0, ..., x_n$),
)

// ****************** Context ******************

#let Not-In-Base = prooftree(
  axiom(""),
  rule(label: "Not-In-Base", $p in.not dot$),
)

#let Not-In-Rec = prooftree(
  axiom($p != p'$),
  axiom($p in.not Delta$),
  rule(n:2, label: "Not-In-Rec", $p in.not (p' : alpha beta, Delta)$),
)

#let Root-Base = prooftree(
  axiom(""),
  rule(label: "Root-Base", $root(x) = x$),
)

#let Root-Rec = prooftree(
  axiom($root(p) = x$),
  rule(label: "Root-Rec", $root(p.f) = x$),
)

#let Ctx-Base = prooftree(
  axiom(""),
  rule(label: "Ctx-Base", $dot ctx$),
)

#let Ctx-Rec = prooftree(
  axiom($Delta ctx$),
  axiom($p in.not Delta$),
  rule(n:2, label: "Ctx-Rec", $p: alpha beta, Delta ctx$),
)

#let Lookup-Base = prooftree(
  axiom($(p: alpha beta, Delta) ctx$),
  rule(label: "Lookup-Base", $(p: alpha beta, Delta) inangle(p) = alpha beta$),
)

#let Lookup-Rec = prooftree(
  axiom($(p: alpha beta, Delta) ctx$),
  axiom($p != p'$),
  axiom($Delta inangle(p') = alpha' beta'$),
  rule(n:3, label: "Lookup-Rec", $(p: alpha beta, Delta) inangle(p') = alpha' beta'$),
)

#let Lookup-Default = prooftree(
  axiom($type(p) = C$),
  axiom($class C(overline(f': alpha'_f), f: alpha, overline(f'': alpha''_f))$),
  rule(n:2, label: "Lookup-Default", $dot inangle(p.f) = alpha$),
)

// #let In = prooftree(
//   axiom($root(p) = x$),
//   axiom($Delta inangle(x) = alpha beta$),
//   rule(n:2, label: "In", $p in Delta$),
// )

#let Remove-Empty = prooftree(
  axiom(""),
  rule(label: "Remove-Empty", $dot without p = dot$),
)

#let Remove-Base = prooftree(
  axiom(""),
  rule(label: "Remove-Base", $(p: alpha beta, Delta) without p = Delta$),
)

#let Remove-Rec = prooftree(
  axiom($Delta without p = Delta'$),
  axiom($p != p'$),
  rule(n:2, label: "Remove-Rec", $(p': alpha beta, Delta) without p = p': alpha beta, Delta'$),
)

#let SubPath-Base = prooftree(
  axiom(""),
  rule(label: "SubPath-Base", $p subset.sq p.f$),
)

#let SubPath-Rec = prooftree(
  axiom($p subset.sq p'$),
  rule(label: "SubPath-Rec", $p subset.sq p'.f$),
)

#let SubPath-Eq-1 = prooftree(
  axiom($p = p'$),
  rule(label: "SubPath-Eq-1", $p subset.sq.eq p'$),
)

#let SubPath-Eq-2 = prooftree(
  axiom($p subset.sq p'$),
  rule(label: "SubPath-Eq-2", $p subset.sq.eq p'$),
)

#let Remove-SupPathsEq-Empty = prooftree(
  axiom(""),
  rule(label: "Remove-SupPathsEq-Empty", $dot minus.circle p = dot$),
)

#let Remove-SupPathsEq-Discard = prooftree(
  axiom($p subset.sq.eq p'$),
  axiom($Delta minus.circle p = Delta'$),
  rule(n:2, label: "Remove-SupPathsEq-Discard", $(p': alpha beta, Delta) minus.circle p = Delta'$),
)

#let Remove-SupPathsEq-Keep = prooftree(
  axiom($p subset.not.sq.eq p'$),
  axiom($Delta minus.circle p = Delta'$),
  rule(n:2, label: "Remove-SupPathsEq-Keep", $(p': alpha beta, Delta) minus.circle p = (p': alpha beta, Delta')$),
)

#let Replace = prooftree(
  axiom($Delta minus.circle p = Delta'$),
  rule(label: "Replace", $Delta[p |-> alpha beta] = Delta', p: alpha beta$),
)

#let Get-SupPaths-Empty = prooftree(
  axiom(""),
  rule(label: "Get-SupPaths-Empty", $dot tr sp(p) = dot$),
)

#let Get-SupPaths-Discard = prooftree(
  axiom($not (p subset.sq p')$),
  axiom($Delta tr sp(p) = p_0 : alpha_0 beta_0, ..., p_n : alpha_n beta_n$),
  rule(n: 2, label: "Get-SupPaths-Discard", $p': alpha beta, Delta tr sp(p) = p_0 : alpha_0 beta_0, ..., p_n : alpha_n beta_n$),
)

#let Get-SupPaths-Keep = prooftree(
  axiom($p subset.sq p'$),
  axiom($Delta tr sp(p) = p_0 : alpha_0 beta_0, ..., p_n : alpha_n beta_n$),
  rule(n: 2, label: "Get-SupPaths-Keep", $p': alpha beta, Delta tr sp(p) = p': alpha beta, p_0 : alpha_0 beta_0, ..., p_n : alpha_n beta_n$),
)

// ************ Get ************

#let Get-Var = prooftree(
  axiom($Delta inangle(x) = alpha beta$),
  rule(label: "Get-Var", $Delta(x) = alpha beta$)
)

#let Get-Path = prooftree(
  axiom($Delta(p) = alpha beta$),
  axiom($Delta inangle(p.f) = alpha'$),
  rule(n: 2, label: "Get-Path", $Delta(p.f) = Lub{alpha beta, alpha'}$)
)

#let Std-Empty = prooftree(
  axiom(""),
  rule(label: "Std-Empty", $dot tr std(p, alpha beta)$),
)

#let Std-Rec-1 = prooftree(
  axiom($not (p subset.sq p')$),
  axiom($Delta tr std(p, alpha beta)$),
  rule(n:2, label: "Std-Rec-1", $p' : alpha beta, Delta tr std(p, alpha beta)$),
)

#let Std-Rec-2 = prooftree(
  axiom($p subset.sq p'$),
  axiom($root(p) = x$),
  axiom($(x : alpha beta) (p') = alpha'' beta''$),
  axiom($alpha' beta' rel alpha'' beta''$),
  axiom($Delta tr std(p, alpha beta)$),
  rule(n:5, label: "Std-Rec-2", $p' : alpha' beta', Delta tr std(p, alpha beta)$),
)