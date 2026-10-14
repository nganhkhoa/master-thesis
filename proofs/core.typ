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

= #langb Safety Theorem

We prove type safety of #langb. The language has no mutable cells, so the store never changes and a step is just $e step e'$.

Each binary operator $o in {+, -, and, or}$ has a signature $o : tau_a times tau_b -> tau_o$ (used by T-Op), with $+, - : numt times numt -> numt$ and $and, or : boolt times boolt -> boolt$.

// The function $delta$ used by S-Op is total on values of the right types and returns a value of type $tau_o$.

== Type Safety

#theorem(title: [#langb Type Safety])[

  1. If $type(dot, e, tau)$ and $e step e'$ then $type(dot,e',tau)$
  2. If $type(dot, e, tau)$ then $e$ is a value or $e step e'$ for some $e'$.
] <langb-Type-Safety>

#proof[
  By @langb-Preservation and @langb-Progress.
]


#lemma(title: [#langb Preservation])[
  If $type(Gamma, e_1, tau)$ and $e_1 step e_2$ then $type(Gamma, e_2, tau)$.
] <langb-Preservation>

#proof(of: <langb-Preservation>)[
  #derivation((
    ($e_1 = E[e'_1], e_2 = E[e'_2], e'_1 stepx e'_2$, rn("Step")),
    ($type(Gamma, e'_1, tau_1)$, [@langb-decomposition]),
    ($type(Gamma, e'_2, tau_1)$, [@langb-redex-preservation]),
    ($type(Gamma, E[e'_2], tau)$, [@langb-decomposition]),
  ))
]

#lemma(title: [#langb Progress])[
  If $type(dot, e_1, tau)$ then $e_1$ is a value $e_1 step e_2$ for some $e_2$.
] <langb-Progress>

#proof(of: <langb-Progress>)[
  By induction on the derivation of $type(dot, e_1, tau)$.

  - Case T-Var. Impossible, the context is empty.

  - Case T-App, $e_1 = apply(e_3, e_4)$. By the I.H. $e_3$ is a value or steps, and then $e_4$ is a value or steps. If one of them steps then it steps, else if both are values:
    #derivation((
      ($type(dot, e_3, tau_2 -> tau)$, rn("T-App")),
      ($e_3 = lambda x : tau_2. e_5$, [@langb-canonical]),
      ($apply(e_3, e_4) step e_5[x:=e_4]$, rn("S-App")),
    ))

  - Other cases are trivial: the expression is a value, or it takes a step by the matching rule of $stepx$ (using @langb-canonical for the shape of values).
]

// #lemma(title: [Steps under contexts])[
//   If $e step e'$ then $E[e] step E[e']$.
// ] <langb-step-context>

// #proof[
//   $e = E'[e_1]$, $e' = E'[e_2]$ with $e_1 stepx e_2$, and $E[E'[dot.op]]$ is again an evaluation context, so Step applies.
// ]

#lemma(title: [Canonical forms])[
  If $type(Gamma, v, tau)$ then:
  - If $tau = numt$ then $v = n$.
  - If $tau = boolt$ then $v = b$.
  - If $tau = unit$ then $v = unit$.
  - If $tau = tau_1 -> tau_2$ then $v = lambda x : tau_1. e$.
  - If $tau = tuple(tau_1, tau_2)$ then $v = tuple(v_1, v_2)$ with $type(Gamma, v_1, tau_1)$ and $type(Gamma, v_2, tau_2)$.
] <langb-canonical>

#proof[
  By type rules T-Num, T-Bool, T-Unit, T-Lambda, T-Tuple.
]

#lemma(title: [Decomposition])[
  If $type(Gamma, E[e], tau)$ then there is $tau_1$ such that $type(Gamma, e, tau_1)$, and for every $e'$ with $type(Gamma, e', tau_1)$ we have $type(Gamma, E[e'], tau)$.
] <langb-decomposition>

#proof[
  By induction on $E$.

  - Case $E = square.stroked$. Take $tau_1 = tau$. The premise is $type(Gamma, e, tau)$, and the conclusion follows immediately.

  - Case $E = apply(E_0, e_0)$.
    #derivation((
      ($type(Gamma, apply(E_0[e], e_0), tau)$, "Given"),
      ($type(Gamma, E_0[e], tau_2 -> tau)$, rn("T-App")),
      ($type(Gamma, e_0, tau_2)$, rn("T-App")),
      ($type(Gamma, e, tau_1)$, "I.H."),
      ($type(Gamma, E_0[e'], tau_2 -> tau)$, [I.H.]),
      ($type(Gamma, apply(E_0[e'], e_0), tau)$, rn("T-App")),
    ))

  - Other cases are trivial: invert the typing rule of the frame, apply the I.H. to $E_0$ under the same $Gamma$, and apply the same typing rule again.
]

#lemma(title: [Redex preservation])[
  If $type(Gamma, e_1, tau)$ and $e_1 stepx e_2$ then $type(Gamma, e_2, tau)$.
] <langb-redex-preservation>

#proof[
  By cases on $e_1 stepx e_2$.

  - Case S-App, $apply((lambda x : tau_1. e), v) stepx e[x:=v]$.
    #derivation((
      ($type(Gamma, lambda x : tau_1. e, tau_1 -> tau)$, rn("T-App")),
      ($type(Gamma, v, tau_1)$, rn("T-App")),
      ($type(Gamma\, x : tau_1, e, tau)$, rn("T-Lambda")),
      ($type(Gamma, e[x:=v], tau)$, [@langb-substitution]),
    ))

  - Case S-Fix, $mu x : tau. e stepx e[x:=mu x : tau. e]$.
    #derivation((
      ($type(Gamma\, x : tau, e, tau)$, rn("T-Fix")),
      ($type(Gamma, mu x : tau. e, tau)$, "Given"),
      ($type(Gamma, e[x:=mu x : tau. e], tau)$, [@langb-substitution]),
    ))

  - Other cases are trivial.
]

#lemma(title: [Substitution])[
  If $type(Gamma\, x : tau_1, e, tau)$ and $type(Gamma, e_1, tau_1)$ then $type(Gamma, e[x:=e_1], tau)$.
] <langb-substitution>

#proof[
  By induction on the derivation of $type(Gamma\, x : tau_1, e, tau)$.

  - Case T-Var with $e = x$. Then $type(Gamma\, x : tau_1, x, tau_1)$ and $tau = tau_1$.
    #derivation((
      ($type(Gamma, e_1, tau_1)$, "Given"),
      ($x[x:=e_1] = e_1$, [Substitution]),
      ($type(Gamma, x[x:=e_1], tau)$, []),
    ))

  - Case T-Var with $e = y != x$. Then $type(Gamma\, x : tau_1, y, tau)$
    #derivation((
      ($y : tau in (Gamma\, x : tau_1)$, rn("T-Var")),
      ($y : tau in Gamma$, [$y != x$]),
      ($type(Gamma, y[x:=e_1], tau)$, [#rn("T-Var"), $y[x:=e_1] = y$]),
    ))

  - Case T-Lambda with $e = lambda y : tau_2. e_2$, $y != x$ and $y in.not "fv"(e_1)$.
    #derivation((
      ($type(Gamma\, x : tau_1\, y : tau_2, e_2, tau_3)$, rn("T-Lambda")),
      ($type(Gamma\, y : tau_2\, x : tau_1, e_2, tau_3)$, [Unordered Context]),
      ($type(Gamma\, y : tau_2, e_2[x:=e_1], tau_3)$, [I.H.]),
      ($type(Gamma, lambda y : tau_2. e_2[x:=e_1], tau_2 -> tau_3)$, rn("T-Lambda")),
    ))

  - Case T-Fix with $e = mu y : tau. e_2$. Same as T-Lambda.

  - Case T-App with $e = apply(e_2, e_3)$.
    #derivation((
      ($type(Gamma\, x : tau_1, e_2, tau_2 -> tau)$, rn("T-App")),
      ($type(Gamma\, x : tau_1, e_3, tau_2)$, rn("T-App")),
      ($type(Gamma, e_2[x:=e_1], tau_2 -> tau)$, "I.H."),
      ($type(Gamma, e_3[x:=e_1], tau_2)$, "I.H."),
      ($type(Gamma, (apply(e_2,e_3))[x:=e_1], tau)$, rn("T-App")),
    ))

  - Other cases are trivial: the expression has no variables, or the I.H. applies to every premise and the same rule is used again.
]
