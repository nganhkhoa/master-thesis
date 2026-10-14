#import "/setup.typ": setupdoc
#show: setupdoc

#import "@preview/great-theorems:0.1.2": *
#import "@preview/rich-counters:0.2.1": *

#import "/utils.typ": *
#import "/models/language.typ": *

#set heading(numbering: "A.1")

#show: no-ref
#show: great-theorems-init
#show link: text.with(fill: blue)

#import "/proofs/setup.typ": appendix-theorem, appendix-lemma, derivation, rn
#let theorem = appendix-theorem
#let lemma = appendix-lemma

#let remark = mathblock(
  blocktitle: "Remark",
  prefix: [_Remark._],
  inset: 5pt,
  fill: lime,
  radius: 5pt,
  numbering: "A.1"
)

#let proof = proofblock()

= #langc Safety Theorems

// == Scope and Conventions

// We prove progress and preservation for #langc, extending the proofs for #langb. As for #langb, mutable cells and the contract $refc(kappa)$ are left out, so the store never changes and we write $e cstep e'$. We do not prove contract erasure here.

// The figures of #langc leave some rules implicit, or state them in a form that gets stuck. We use the following.

// *Contract typing.* The judgment $type(Gamma, kappa, con(tau))$ is the one of the figure, and the premise of Type-C-DepFun is read as $type(Gamma\, x : tau_1, kappa_2, con(tau_2))$.

// *Runtime typing.* $check(k, j, e, v)$ and guards only appear during evaluation. They are typed by

// #align(center, grid(
//   columns: 2,
//   column-gutter: 3em,
//   [Type-C-Check: from $type(Gamma, e, boolt)$ and $type(Gamma, v, tau)$ conclude $type(Gamma, check(k, j, e, v), tau)$],
//   [Type-C-Guard: from $type(Gamma, kappa, con(tau))$ and $type(Gamma, v, tau)$ conclude $type(Gamma, guard(v, kappa, k, l, j), tau)$, \ where $kappa$ is $kappa_1 -> kappa_2$ or $dep(kappa_1, lambda x. kappa_2)$],
// ))

// Guards are only created by Mon-Guard, which never wraps a flat or tuple contract, so the side condition of Type-C-Guard holds for every guard that evaluation produces.

// *Tuple contracts.* The guard rules for $injl$ and $injr$ are commented out in the figure, so $injl(guard(tuple(v_1,v_2), tuple(kappa_1,kappa_2), k, l, j))$ would be stuck. We use the rule of the Redex model and the compiler instead, which monitors the components eagerly, and restrict Mon-Guard to function contracts:

// $
// mon(k, l, j, tuple(kappa_1, kappa_2), tuple(v_1, v_2)) quad cstepx quad tuple(mon(k, l, j, kappa_1, v_1), mon(k, l, j, kappa_2, v_2)) quad "(Mon-Tuple)"
// $

// *Checks.* Check-True and Check-False are on $trueb$ and $falseb$.

// *Results.* Blame is not a value. A program either reduces to a value, reduces to $blame(k, j)$, or diverges.

#theorem(title: [#langc Type Safety])[

  1. If $type(dot, e, tau)$ and $e cstep e'$ then $type(dot,e',tau)$.
  2. If $type(dot, e, tau)$ then $e$ is a value or $e = blame(k,j)$ or $e cstep e'$ for some $e'$.
] <langc-Type-Safety>

#proof[
  By @langc-Preservation and @langc-Progress.
]


#lemma(title: [#langc Preservation])[
  If $type(Gamma, e_1, tau)$ and $e_1 cstep e_2$ then $type(Gamma, e_2, tau)$.
] <langc-Preservation>

#proof(of: <langc-Preservation>)[
  By cases on the step.

  - Case Step-C, $E[e'_1] cstep E[e'_2]$ with $e'_1 cstepx e'_2$.
    #derivation((
      ($type(Gamma, e'_1, tau_1)$, [@langc-decomposition]),
      ($type(Gamma, e'_2, tau_1)$, [@langc-redex-preservation]),
      ($type(Gamma, E[e'_2], tau)$, [@langc-decomposition]),
    ))

  - Case Step-C-Blame, $E[blame(k, j)] cstep blame(k, j)$.
    #derivation((
      ($type(Gamma, blame(k, j), tau)$, rn("Type-C-Blame")),
    ))
]

#lemma(title: [#langc Progress])[

If $type(Gamma, e_1, tau)$ then $e_1$ is a value, or $e_1 = blame(k, j)$, or there is $e_2$ with $e_1 cstep e_2$.
] <langc-Progress>

#proof(of: <langc-Progress>)[
  By induction on the derivation of $type(Gamma, e_1, tau)$.

  During induction, we encounter case $e' = blame(k',j')$. This makes $e = E[blame(k',j')]$ and would take a step. In the following proof, we left this case (blame) out.

  - Cases of #langb.

    Similarly to @langb-Progress, except for T-App. Function type by @langc-canonical, introduces two new cases:

    - $e_3 = guard(v_1, kappa_1 -> kappa_2, k, l, j)$. Steps by Guard-Func.
    - $e_3 = guard(v_1, dep(kappa_1, lambda x. kappa_2), k, l, j)$. Steps by Guard-Dep.

  - Case Type-C-Blame. $e_1 = blame(k, j)$.

  - Case Type-C-Guard. $e_1$ is a value.

  - Case Type-C-Check, $e_1 = check(k, j, e, v)$.

    #derivation((
      ($type(Gamma,e,boolt)$, [Type-C-Check]),
      ($e = trueb | falseb$, [@langc-canonical]),
      ($e_1 cstep e'_1$, [Check-True or Check-False]),
    ))

  - Case Type-C-Mon, $e_1 = mon(k, l, j, kappa, v)$

    #derivation((
      ($type(Gamma,kappa,con(tau))$, [Type-C-Mon]),
    ))

    Subcase on type of conract:

    - Type-C-Flat. Steps by Mon-Flat.
    - Type-C-Fun or Type-C-DepFun. Steps by Mon-Guard.
    // - Type-C-Tuple. $tau = tuple(tau_1, tau_2)$, so $v = tuple(v_1, v_2)$ by @langc-canonical, and Mon-Tuple applies.
]


// #lemma(title: [Steps under contexts])[

// If $e cstep e'$ then $E[e] cstep e''$ for some $e''$.
// ] <langc-step-context>

// #proof[
//   If the step is Step-C, then $E[e] cstep E[e']$ by Step-C with the composed context. If it is Step-C-Blame, $e = E'[blame(k, j)]$ with $E' != square.stroked$, so $E[E'] != square.stroked$ and $E[e] cstep blame(k, j)$ by Step-C-Blame.
// ]

#lemma(title: [Canonical forms])[
  If $type(Gamma, v, tau)$ then either:

  - If $tau = boolt$ then $v = trueb$ or $v = falseb$
  - If $tau = tau_1 -> tau_2$ then $v = lambda x : tau_1. e$ or $v = guard(v',kappa,k,l,j)$ where $kappa = kappa_1 -> kappa_2$ or $kappa = dep(kappa_1,lambda y. kappa_2)$
] <langc-canonical>

#proof[
  Trivial by type inversion.
]

#lemma(title: [Substitution Expression])[

  If $type(Gamma, e_1, tau_1)$ and $type(Gamma\, x : tau_1, e, tau)$ then $type(Gamma, e[x:=e_1], tau)$.
] <langc-substitution-expression>

#proof[
  By induction on $type(Gamma\,x:tau_1,e,tau)$. The cases of #langb are those of @langb-substitution.

  - Case $type(Gamma\,x:tau_1,mon(k,l,j,kappa,e_2),tau)$
    #derivation((
      ($type(Gamma\, x : tau_1, kappa, con(tau))$, rn("Type-C-Mon")),
      ($type(Gamma\, x : tau_1, e_2, tau)$, rn("Type-C-Mon")),
      ($type(Gamma, kappa[x:=e_1], con(tau))$, [@langc-substitution-contract]),
      ($type(Gamma, e[x:=e_1], tau)$, [I.H.]),
      ($type(Gamma, mon(k, l, j, kappa, e)[x:=e_1], tau)$, rn("Type-C-Mon")),
    ))

  - Cases Type-C-Check and Type-C-Guard.

    Similarly to the above, using I.H..

  - Case $type(Gamma\,x:tau_1,blame(k,j),tau)$

    #derivation((
      ($blame(k,j)[x:=e_1] = blame(k,j)$, [Substitution]),
      ($type(Gamma, blame(k,j)[x:=e_1], tau)$, []),
    ))
]


#lemma(title: [Substitution Contract])[

  If $type(Gamma, kappa, tau_1)$ and $type(Gamma\, x : tau_1, kappa, con(tau))$ then $type(Gamma, kappa[x:=e_1], con(tau))$.
] <langc-substitution-contract>

#proof[

  - Case $type(Gamma\,x:tau_1,flat(e),con(tau))$
    #derivation((
      ($type(Gamma\, x : tau_1, e, tau -> boolt)$, rn("Type-C-Flat")),
      ($type(Gamma, e[x:=e_1], tau -> boolt)$, [@langc-substitution-expression]),
      ($type(Gamma, flat(e)[x:=e_1], con(tau))$, rn("Type-C-Flat")),
    ))

  - Case Type-C-Fun and Type-C-Tuple.

    Similarly to the above.

  - Case $type(Gamma\, x : tau_1, dep(kappa_1, lambda y. kappa_2), con(tau_2 -> tau_3))$, $y != x$ and $y in.not "fv"(e_1)$.
    #derivation((
      ($type(Gamma\, x : tau_1, kappa_1, con(tau_2))$, rn("Type-C-DepFun")),
      ($type(Gamma\, x : tau_1\, y : tau_2, kappa_2, con(tau_3))$, rn("Type-C-DepFun")),
      ($type(Gamma, kappa_1[x:=e_1], con(tau_2))$, [I.H.]),
      ($type(Gamma\, y : tau_2, e_1, tau_1)$, [Weakening context]),
      ($type(Gamma\, y : tau_2, kappa_2[x:=e_1], con(tau_3))$, [I.H.]),
      ($type(Gamma, kappa[x:=e_1], con(tau_2 -> tau_3))$, rn("Type-C-DepFun")),
    ))
]

#lemma(title: [Decomposition])[
  If $type(Gamma, E[e], tau)$ then there is $tau_1$ such that $type(Gamma, e, tau_1)$, and for every $e'$ with $type(Gamma, e', tau_1)$ we have $type(Gamma, E[e'], tau)$.
] <langc-decomposition>

#proof[
  By induction on $E$. The frames of #langb are as in @langb-decomposition. Two frames are new.

  - Case $E = mon(k, l, j, kappa, E_0)$.
    #derivation((
      ($type(Gamma, mon(k, l, j, kappa, E_0[e]), tau)$, "Given"),
      ($type(Gamma, kappa, con(tau))$, rn("Type-C-Mon")),
      ($type(Gamma, E_0[e], tau)$, rn("Type-C-Mon")),
      ($type(Gamma, e, tau_1)$, "I.H."),
      ($type(Gamma, E_0[e'], tau)$, [I.H., for $type(Gamma, e', tau_1)$]),
      ($type(Gamma, mon(k, l, j, kappa, E_0[e']), tau)$, rn("Type-C-Mon")),
    ))

  - Case $E = check(k, j, E_0, v)$.
    #derivation((
      ($type(Gamma, check(k, j, E_0[e], v), tau)$, "Given"),
      ($type(Gamma, E_0[e], boolt)$, rn("Type-C-Check")),
      ($type(Gamma, v, tau)$, rn("Type-C-Check")),
      ($type(Gamma, e, tau_1)$, "I.H."),
      ($type(Gamma, E_0[e'], boolt)$, [I.H., for $type(Gamma, e', tau_1)$]),
      ($type(Gamma, check(k, j, E_0[e'], v), tau)$, rn("Type-C-Check")),
    ))
]

#lemma(title: [Redex preservation])[
  If $type(Gamma, e_1, tau)$ and $e_1 cstepx e_2$ then $type(Gamma, e_2, tau)$.
] <langc-redex-preservation>

#proof[
  By cases on $e_1 cstepx e_2$. The reductions of #langb are as in @langb-redex-preservation, using @langc-substitution-expression for S-App and S-Fix.

  - Case $check(k, j, trueb, v) cstepx v$.
    #derivation((
      ($type(Gamma, v, tau)$, rn("Type-C-Check")),
    ))

  - Case $check(k, j, falseb, v) cstepx blame(k, j)$.
    #derivation((
      ($type(Gamma, blame(k, j), tau)$, rn("Type-C-Blame")),
    ))

  - Case $mon(k, l, j, flat(e), v) cstepx check(k, j, apply(e, v), v)$.
    #derivation((
      ($type(Gamma, flat(e), con(tau))$, rn("Type-C-Mon")),
      ($type(Gamma, v, tau)$, rn("Type-C-Mon")),
      ($type(Gamma, e, tau -> boolt)$, rn("Type-C-Flat")),
      ($type(Gamma, apply(e, v), boolt)$, rn("T-App")),
      ($type(Gamma, check(k, j, apply(e, v), v), tau)$, rn("Type-C-Check")),
    ))

  // - Case $mon(k, l, j, tuple(kappa_1, kappa_2), tuple(v_1, v_2)) cstepx tuple(mon(k, l, j, kappa_1, v_1), mon(k, l, j, kappa_2, v_2))$, with $tau = tuple(tau_1, tau_2)$.
  //   #derivation((
  //     ($type(Gamma, tuple(kappa_1, kappa_2), con(tuple(tau_1, tau_2)))$, rn("Type-C-Mon")),
  //     ($type(Gamma, tuple(v_1, v_2), tuple(tau_1, tau_2))$, rn("Type-C-Mon")),
  //     ($type(Gamma, kappa_1, con(tau_1)), type(Gamma, kappa_2, con(tau_2))$, rn("Type-C-Tuple")),
  //     ($type(Gamma, v_1, tau_1), type(Gamma, v_2, tau_2)$, rn("T-Tuple")),
  //     ($type(Gamma, mon(k, l, j, kappa_i, v_i), tau_i)$, rn("Type-C-Mon")),
  //     ($type(Gamma, tuple(mon(k, l, j, kappa_1, v_1), mon(k, l, j, kappa_2, v_2)), tuple(tau_1, tau_2))$, rn("T-Tuple")),
  //   ))

  - Case $mon(k, l, j, kappa, v) cstepx guard(v, kappa, k, l, j)$ with $kappa$ a function contract.
    #derivation((
      ($type(Gamma, kappa, con(tau))$, rn("Type-C-Mon")),
      ($type(Gamma, v, tau)$, rn("Type-C-Mon")),
      ($type(Gamma, guard(v, kappa, k, l, j), tau)$, rn("Type-C-Guard")),
    ))

  - Case $apply(guard(v_1, kappa_1 -> kappa_2, k, l, j), v_2) cstepx mon(k, l, j, kappa_2, apply(v_1, mon(l, k, j, kappa_1, v_2)))$.
    #derivation((
      ($type(Gamma, v_2, tau_1)$, rn("T-App")),
      ($type(Gamma, guard(v_1, kappa_1 -> kappa_2, k, l, j), tau_1 -> tau)$, rn("T-App")),
      ($type(Gamma, kappa_1 -> kappa_2, con(tau_1 -> tau))$, rn("Type-C-Guard")),
      ($type(Gamma, v_1, tau_1 -> tau)$, rn("Type-C-Guard")),
      ($type(Gamma, kappa_1, con(tau_1))$, rn("Type-C-Fun")),
      ($type(Gamma, kappa_2, con(tau))$, rn("Type-C-Fun")),
      ($type(Gamma, mon(l, k, j, kappa_1, v_2), tau_1)$, rn("Type-C-Mon")),
      ($type(Gamma, apply(v_1, mon(l, k, j, kappa_1, v_2)), tau)$, rn("T-App")),
      ($type(Gamma, mon(k, l, j, kappa_2, apply(v_1, mon(l, k, j, kappa_1, v_2))), tau)$, rn("Type-C-Mon")),
    ))

  - Case Guard-Dep, $apply(guard(v_1, dep(kappa_1, lambda x. kappa_2), k, l, j), v_2) cstepx mon(k, l, j, kappa_3, apply(v_1, mon(l, k, j, kappa_1, v_2)))$ with $kappa_3 = kappa_2[x:=mon(l, j, j, kappa_1, v_2)]$.
    #derivation((
      ($type(Gamma, v_2, tau_1)$, rn("T-App")),
      ($type(Gamma, v_1, tau_1 -> tau)$, rn("Type-C-Guard")),
      ($type(Gamma, dep(kappa_1,lambda x. kappa_2), con(tau_1 -> tau))$, rn("Type-C-Guard")),
      ($type(Gamma, kappa_1, con(tau_1))$, rn("Type-C-DepFun")),
      ($type(Gamma\,x : tau_1, kappa_2, con(tau))$, rn("Type-C-DepFun")),
      ($type(Gamma, mon(l, j, j, kappa_1, v_2), tau_1)$, rn("Type-C-Mon")),
      ($type(Gamma, kappa_3, con(tau))$, [@langc-substitution-contract]),
      ($type(Gamma, mon(l, k, j, kappa_1, v_2), tau_1)$, rn("Type-C-Mon")),
      ($type(Gamma, apply(v_1, mon(l, k, j, kappa_1, v_2)), tau)$, rn("T-App")),
      ($type(Gamma, mon(k, l, j, kappa_3, apply(v_1, mon(l, k, j, kappa_1, v_2))), tau)$, rn("Type-C-Mon")),
    ))
]
