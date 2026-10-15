#import "/setup.typ": setupdoc
#show: setupdoc

#import "@preview/curryst:0.6.0": rule, prooftree, rule-set

#import "/proofs/setup.typ": *
#import "/utils.typ": *
#import "/models/language.typ": *

#show: no-ref
#show: great-theorems-init

#let theorem = appendix-theorem
#let lemma = appendix-lemma

#let tc(t) = $#t^*$
#let hc = $effs(heffcheck)$

= #langc to #lange Compiler Typesoundness

== Overview

This part shows how the compiler remains typesoundness of the source program to the target program. Since the compiler introduces effects and explicitly declares it everywhere (in lambdas, and perform operations), the function type is augmented with the effect. The compiler also does not introduce any handler, this makes the whole program (potentially) produce the effect as well.

The environment that will be used to type check target programs has the following $Sigma$ signature.

$
Sigma(heffcheck) = {effcheck : forall alpha. tuple(blab, tuple(teff(alpha,hc,boolt), alpha)) -> alpha}
$

// Assumptions:

// - The rules of #langb are lifted to #lange by giving every premise and the conclusion the same effect row $epsilon$ (as T-E-App does).
// - #lange has $type(Gamma, eblame(p), tau, eff: epsilon)$ for any $tau$ and $epsilon$ (T-E-Error), and blame labels have type $blab$ (T-E-Label).
// - The compiler writes the translated type $tc(tau)$ on every binder and on $perform(effcheck, tau: tau)$. Types are erased at run time, so this does not change the compiler correctness proofs.
// - Mutable cells are not covered.

== Type Translation

#block(width: 100%)[
  #rect(stroke: 0.5pt, inset: 5pt)[
    $tc(dot.op) : langc tau -> lange tau$
  ]

  #v(1em)
  #grid(
    columns: (1fr, auto, 1fr),
    column-gutter: 1em,
    row-gutter: 1.2em,
    align: (right, left, left),

    [$tc(numt)$], [$=$], [$numt$],
    [$tc(boolt)$], [$=$], [$boolt$],
    [$tc(unit)$], [$=$], [$unit$],
    [$tc(tuple(tau_1,tau_2))$], [$=$], [$tuple(tc(tau_1),tc(tau_2))$],
    [$tc((tau_1 -> tau_2))$], [$=$], [$teff(tc(tau_1),hc,tc(tau_2))$],
    [$tc((x_1 : tau_1, ..., x_n : tau_n))$], [$=$], [$x_1 : tc(tau_1), ..., x_n : tc(tau_n)$],
  )
]

== Compiler Type Preservation


#theorem(title: "Compiler Type Preservation")[

  If $compile(type(Gamma,e,tau),e')$ then $type(tc(Gamma),e',tc(tau),eff: hc)$.
] <compiler-type-ts-preservation>

#proof[

By induction on structure of $compile(type(Gamma,e,tau),e')$.

- Case $e = x$, $e = n$, $e = b$, $e = unit$

  #derivation((
    ($e' = e$, "Given"),
    ($type(tc(Gamma), e', tc(tau), type: "val")$, [#rn("T-E-Var"), #rn("T-Num"), #rn("T-Bool"), #rn("T-Unit")]),
    ($type(tc(Gamma), e', tc(tau), eff: hc)$, rn("T-E-Val")),
  ))

- Case #prooftree(rule(
    $compile(type(Gamma\, x : tau_1, e, tau_2), e'')$,
    $compile(type(Gamma, lambda x : tau_1. e, tau_1 -> tau_2), lambda x : tc(tau_1). e'')$,
  ))

  #derivation((
    ($type(tc(Gamma)\, x : tc(tau_1), e'', tc(tau_2), eff: hc)$, "I.H."),
    ($type(tc(Gamma), lambda x : tc(tau_1). e'', teff(tc(tau_1),hc,tc(tau_2)), type: "val")$, rn("T-E-Abs")),
    ($type(tc(Gamma), lambda x : tc(tau_1). e'', tc((tau_1 -> tau_2)), type: "val")$, [Type compilation $tc(dot.op)$]),
    ($type(tc(Gamma), lambda x : tc(tau_1). e'', tc((tau_1 -> tau_2)), eff: hc)$, rn("T-E-Val")),
  ))

- Case #prooftree(rule(
    $compile(type(Gamma, e_1, tau_1 -> tau_2), e'_1)$,
    $compile(type(Gamma, e_2, tau_1), e'_2)$,
    $compile(type(Gamma, apply(e_1,e_2), tau_2), apply(e'_1,e'_2))$,
  ))

  #derivation((
    ($type(tc(Gamma), e'_1, teff(tc(tau_1),hc,tc(tau_2)), eff: hc)$, "I.H."),
    ($type(tc(Gamma), e'_2, tc(tau_1), eff: hc)$, "I.H."),
    ($type(tc(Gamma), apply(e'_1,e'_2), tc(tau_2), eff: hc)$, rn("T-E-App")),
  ))

  The effect on the arrow and the effect of the premises are both $hc$.

- Case $mu x : tau. e$, $tuple(e_1,e_2)$, $injl(e)$, $injr(e)$, $ife(e_1,e_2,e_3)$, $o(e_1,...,e_n)$

  #derivation((
    ([$type(tc(Gamma), e'_i, tc(tau_i), eff: hc)$ for every sub-expression], "I.H."),
    ($type(tc(Gamma), e', tc(tau), eff: hc)$, [lifted rule of #langb]),
  ))

  For $mu x : tau. e$, the binder is $x : tc(tau)$, and the I.H. is used under $tc(Gamma)\, x : tc(tau)$.

- Case #prooftree(rule(
    $compile(type(Gamma,e_3,tau -> boolt), e_5)$,
    $compile(type(Gamma,e_4,tau), e_6)$,
    $compile(type(Gamma,mon(k,l,j,flat(e_3),e_4),tau), apply(perform(effcheck, tau: tc(tau)), tuple(k, tuple(e_5, e_6))))$,
  ))

  #derivation((
    ($type(tc(Gamma), e_5, teff(tc(tau),hc,boolt), eff: hc)$, "I.H."),
    ($type(tc(Gamma), e_6, tc(tau), eff: hc)$, "I.H."),
    ($type(tc(Gamma), apply(perform(effcheck, tau: tc(tau)), tuple(k, tuple(e_5, e_6))), tc(tau), eff: hc)$, [@compiler-type-ts-perform]),
  ))

  This is the only rule that introduces $heffcheck$.

- Case #prooftree(rule(
    $compile(type(Gamma,e_1,tau_1 -> tau_2), e_2)$,
    $compile(type(Gamma,
        lambda f : tau_1 -> tau_2. lambda x : tau_1. mon(k,l,j,kappa_2,apply(f, mon(l,k,j,kappa_1,x))),
        (tau_1 -> tau_2) -> (tau_1 -> tau_2)),
      e_3)$,
    $compile(type(Gamma,mon(k,l,j,kappa_1->kappa_2,e_1),tau_1 -> tau_2),apply(e_3, e_2))$,
  ))

  #derivation((
    ($type(tc(Gamma), e_2, tc((tau_1 -> tau_2)), eff: hc)$, "I.H."),
    ($type(tc(Gamma), e_3, tc(((tau_1 -> tau_2) -> (tau_1 -> tau_2))), eff: hc)$, "I.H."),
    ($type(tc(Gamma), e_3, teff(tc((tau_1 -> tau_2)),hc,tc((tau_1 -> tau_2))), eff: hc)$, [def. of $tc(dot.op)$]),
    ($type(tc(Gamma), apply(e_3,e_2), tc((tau_1 -> tau_2)), eff: hc)$, rn("T-E-App")),
  ))

- Case #prooftree(rule(
    $compile(type(Gamma,e_1,tau_1 -> tau_2), e_2)$,
    $compile(type(Gamma, e_w, (tau_1 -> tau_2) -> (tau_1 -> tau_2)), e_3)$,
    $compile(type(Gamma,mon(k,l,j,dep(kappa_1, lambda y. kappa_2),e_1),tau_1 -> tau_2),apply(e_3, e_2))$,
  ))

  where $e_w = lambda f : tau_1 -> tau_2. lambda x : tau_1. mon(k,l,j,{mon(l,j,j,kappa_1,x)\/y}kappa_2,apply(f, mon(l,k,j,kappa_1,x)))$

  #derivation((
    ($type(tc(Gamma), e_2, tc((tau_1 -> tau_2)), eff: hc)$, "I.H."),
    ($type(tc(Gamma), e_3, teff(tc((tau_1 -> tau_2)),hc,tc((tau_1 -> tau_2))), eff: hc)$, [I.H., def. of $tc(dot.op)$]),
    ($type(tc(Gamma), apply(e_3,e_2), tc((tau_1 -> tau_2)), eff: hc)$, rn("T-E-App")),
  ))

  The dependency $y$ is replaced in the source by the indy monitor $mon(l,j,j,kappa_1,x) : tau_1$, so the I.H. on $e_w$ already covers $kappa_2$ in the context $Gamma, f : tau_1 -> tau_2, x : tau_1$.

- Case #prooftree(rule(
    $x in.not "dom"(Gamma)$,
    $compile(type(Gamma\,x:tuple(tau_1,tau_2),mon(k,l,j,kappa_1,injl(x)),tau_1), e_1)$,
    $compile(type(Gamma\,x:tuple(tau_1,tau_2),mon(k,l,j,kappa_2,injr(x)),tau_2), e_2)$,
    $compile(type(Gamma,e,tuple(tau_1,tau_2)),e_3)$,
    $compile(type(Gamma,mon(k,l,j,tuple(kappa_1,kappa_2),e),tuple(tau_1,tau_2)), apply((lambda x : tc(tuple(tau_1,tau_2)). tuple(e_1,e_2)),e_3))$,
  ))

  #derivation((
    ($type(tc(Gamma)\, x : tc(tuple(tau_1,tau_2)), e_1, tc(tau_1), eff: hc)$, "I.H."),
    ($type(tc(Gamma)\, x : tc(tuple(tau_1,tau_2)), e_2, tc(tau_2), eff: hc)$, "I.H."),
    ($type(tc(Gamma)\, x : tc(tuple(tau_1,tau_2)), tuple(e_1,e_2), tc(tuple(tau_1,tau_2)), eff: hc)$, rn("T-Tuple")),
    ($type(tc(Gamma), lambda x : tc(tuple(tau_1,tau_2)). tuple(e_1,e_2), teff(tc(tuple(tau_1,tau_2)),hc,tc(tuple(tau_1,tau_2))), type: "val")$, rn("T-E-Abs")),
    ($type(tc(Gamma), lambda x : tc(tuple(tau_1,tau_2)). tuple(e_1,e_2), teff(tc(tuple(tau_1,tau_2)),hc,tc(tuple(tau_1,tau_2))), eff: hc)$, rn("T-E-Val")),
    ($type(tc(Gamma), e_3, tc(tuple(tau_1,tau_2)), eff: hc)$, "I.H."),
    ($type(tc(Gamma), apply((lambda x. tuple(e_1,e_2)),e_3), tc(tuple(tau_1,tau_2)), eff: hc)$, rn("T-E-App")),
  ))
]


#lemma(title: "Typing a perform of the check effect")[

  If $type(Gamma, e_1, teff(tau,hc,boolt), eff: hc)$ and $type(Gamma, e_2, tau, eff: hc)$ then

  $type(Gamma, apply(perform(effcheck, tau: tau), tuple(k, tuple(e_1, e_2))), tau, eff: hc)$.
] <compiler-type-ts-perform>

#proof[
  #derivation((
    ($type(Gamma, perform(effcheck, tau: tau), teff(tuple(blab, tuple(teff(tau,hc,boolt), tau)), hc, tau), type: "val")$,
      [#rn("T-E-Perform"), $alpha := tau, epsilon := mteff$]),
    ($type(Gamma, perform(effcheck, tau: tau), teff(tuple(blab, tuple(teff(tau,hc,boolt), tau)), hc, tau), eff: hc)$,
      rn("T-E-Val")),
    ($type(Gamma, k, blab, eff: hc)$, rn("T-E-Label")),
    ($type(Gamma, e_1, teff(tau,hc,boolt), eff: hc)$, "Given"),
    ($type(Gamma, e_2, tau, eff: hc)$, "Given"),
    ($type(Gamma, tuple(e_1, e_2), tuple(teff(tau,hc,boolt), tau), eff: hc)$, rn("T-Tuple")),
    ($type(Gamma, tuple(k, tuple(e_1, e_2)), tuple(blab, tuple(teff(tau,hc,boolt), tau)), eff: hc)$, rn("T-Tuple")),
    ($type(Gamma, apply(perform(effcheck, tau: tau), tuple(k, tuple(e_1, e_2))), tau, eff: hc)$, rn("T-E-App")),
  ))

  In the last step, the effect on the arrow and the effect of both premises are the same row $hc$.
]

== Wrapped Compiled Program Typing

The deep handler wrapper from the compiler equivalence proof removes $heffcheck$ from the effect row. We rewrite the wrapper as follows:

$
kw("wrap") = & mu w : forall alpha. teff((teff(unit,hc,alpha)),mteff,alpha). Lambda alpha. lambda f : teff(unit,hc,alpha). apply(handler(h_w), f) \
h_w = & {effcheck -> Lambda beta. lambda tuple(l,tuple(e,v)). lambda k : teff(beta,mteff,alpha). ife(apply(w[boolt], (lambda \_ : unit. apply(e,v))),apply(k,v),eblame(l))}
$

Note that $h_w$ signature matches $Sigma(heffcheck)$ if we replace $alpha$ with $beta$.

#theorem(title: "Compiler Effect Safety")[

  If $compile(type(dot.op,e,tau),e')$ then $type(dot.op, apply(kw("wrap")[tc(tau)],(lambda \_ : unit. e')), tc(tau), eff: mteff)$.
] <compiler-type-ts-effect-safety>

#proof[
  #derivation((
    ($type(dot.op,e',tc(tau),eff: hc)$, [@compiler-type-ts-preservation]),
    ($type(dot.op, lambda \_ : unit. e', teff(unit,hc,tc(tau)), type: "val")$, rn("T-E-Abs")),
    ($type(dot.op, kw("wrap")[tc(tau)], teff((teff(unit,hc,tc(tau))),mteff,tc(tau)), eff: mteff)$, [@compiler-type-ts-wrap, #rn("T-E-Tapp")]),
    ($type(dot.op, apply(kw("wrap")[tc(tau)],(lambda \_ : unit. e')), tc(tau), eff: mteff)$, rn("T-E-App")),
  ))
]


#lemma(title: "Type of wrap")[

  $type(dot.op, kw("wrap"), forall alpha. teff((teff(unit,hc,alpha)),mteff,alpha), type: "val")$
] <compiler-type-ts-wrap>

#proof[

  Assume contexts $Gamma_w = w : forall alpha. teff((teff(unit,hc,alpha)),mteff,alpha)$.

  And $Delta = Gamma_w, l : blab, e : teff(beta,hc,boolt), v : beta, k : teff(beta,mteff,alpha)$.

  #derivation((
    ($type(Delta, apply(e,v), boolt, eff: hc)$, rn("T-E-App")),
    ($type(Delta, lambda \_ : unit. apply(e,v), teff(unit,hc,boolt), type: "val")$, rn("T-E-Abs")),
    ($type(Delta, w[boolt], teff((teff(unit,hc,boolt)),mteff,boolt), eff: mteff)$, rn("T-E-Tapp")),
    ($type(Delta, apply(w[boolt], (lambda \_ : unit. apply(e,v))), boolt, eff: mteff)$, rn("T-E-App")),
    ($type(Delta, apply(k,v), alpha, eff: mteff)$, rn("T-E-App")),
    ($type(Delta, eblame(l), alpha, eff: mteff)$, rn("T-E-Error")),
    ($type(Delta, ife(apply(w[boolt], (lambda \_ : unit. apply(e,v))),apply(k,v),eblame(l)), alpha, eff: mteff)$, rn("T-If")),
    ($type(Gamma_w, h_w(effcheck), forall beta. teff(tuple(blab, tuple(teff(beta,hc,boolt), beta)),mteff,(teff((teff(beta,mteff,alpha)),mteff,alpha))), type: "val")$,
      [#rn("T-E-Abs"), #rn("T-E-TAbs")]),
    ($type(Gamma_w, h_w, alpha, type: "ops", eff: effs(heffcheck | mteff))$,
      rn("T-E-Ops")),
    ($type(Gamma_w, handler(h_w), teff((teff(unit,hc,alpha)),mteff,alpha), type: "val")$, rn("T-E-Handler")),
    ($type(Gamma_w\, f : teff(unit,hc,alpha), apply(handler(h_w), f), alpha, eff: mteff)$, rn("T-E-App")),
    ($type(Gamma_w, lambda f : teff(unit,hc,alpha). apply(handler(h_w), f), teff((teff(unit,hc,alpha)),mteff,alpha), type: "val")$, rn("T-E-Abs")),
    ($type(Gamma_w, Lambda alpha. lambda f. apply(handler(h_w), f), forall alpha. teff((teff(unit,hc,alpha)),mteff,alpha), type: "val")$, rn("T-E-TAbs")),
    ($type(dot.op, kw("wrap"), forall alpha. teff((teff(unit,hc,alpha)),mteff,alpha), type: "val")$, rn("T-Fix")),
  ))
]
