#import "/setup.typ": setupdoc
#show: setupdoc

#import "@preview/curryst:0.6.0": rule, prooftree, rule-set
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#import "/proofs/setup.typ": *
#import "/utils.typ": *
#import "/models/language.typ": *

#show: no-ref
#show: great-theorems-init

#let theorem = appendix-theorem
#let lemma = appendix-lemma

#let relate(e) = $accent(#e, tilde)$
#let ereq(a,b) = $"ER"(#a,#b)$
#let activecheck(e) = $"ActiveCheck"(#e)$
#let noblame(e) = $"NoBlame"(#e)$

= #langc Erasure Theorem

Define erasure compiler $E$ as a homomorphic function over expressions of #langc with a single transformation:


$compile(type(Gamma,mon(k,l,j,kappa,e),tau), e)$

#let erase(e) = $"erase"(#e)$

== Relation

Define $langc F$ as contexts without $check(k,j,E,v)$.

Define these relations:

- $R_e subset.eq langc e times langb e$

  If $(e,e') in R_e$, we write $e attach(~, br: R_e) e'$ or $e ~ e'$. We define $relate(e)$ as shorthand for any expression $relate(e)$ satisfying $e ~ relate(e)$.

- $R_E subset.eq langc F times langb E$

  If $(E,E') in R_E$, we write $E attach(~, br: R_E) E'$ or $E ~ E'$. We define $relate(E)$ as shorthand for any context $relate(E)$ satisfying $E ~ relate(E)$.

- $R_v subset.eq langc v times langb v$

  If $(v,v') in R_v$, we write $v attach(~, br: R_v) v'$ or $v ~ v'$. We define $relate(v)$ as shorthand for any variable $relate(v)$ satisfying $v ~ relate(v)$.

// - $R_kappa subset.eq langc kappa times "Untyped" lange e$

//   If $(kappa,e) in R_kappa$, we write $kappa attach(~, br: R_kappa) e$ or $kappa ~ e$. We define $relate(kappa)$ as shorthand for any expression $relate(e)$ satisfying $kappa ~ relate(e)$.

#block(width: 100%)[
  #rect(stroke: 0.5pt, inset: 5pt)[
    $tilde.op subset.eq langc F times langb E$
  ]

  Define $relate(F)$ such that $F ~ relate(F)$.

  #v(1em)
  #grid(
    columns: (1fr, auto, 1fr),
    column-gutter: 1em,
    row-gutter: 1.2em,
    align: (right, left, left),

    [$square.stroked$],
    [$tilde$],
    [$square.stroked$],

    [$apply(F,e)$],
    [$tilde$],
    [$apply(relate(F),relate(e))$],

    [$apply(v,F)$],
    [$tilde$],
    [$apply(relate(v),relate(F))$],

    [$mon(k,l,j,kappa,F)$],
    [$tilde$],
    [$relate(F)$],
  )
]

#block(width: 100%)[
  #rect(stroke: 0.5pt, inset: 5pt)[
    $tilde.op subset.eq langc e times langb e$
  ]

  #v(1em)
  #grid(
    columns: (1fr, auto, 1fr),
    column-gutter: 1em,
    row-gutter: 1.2em,
    align: (right, left, left),

    [$v$],
    [$tilde$],
    [$relate(v)$],


    [$apply(e_1,e_2)$],
    [$tilde$],
    [$apply(relate(e)_1,relate(e)_2)$],

    [$mon(k,l,j,kappa,e_2)$],
    [$tilde$],
    [$relate(e)_2$],

    [$check(k,j,e_1,v)$],
    [$tilde$],
    [$relate(v)$],
  )
]

#block(width: 100%)[
  #rect(stroke: 0.5pt, inset: 5pt)[
    $tilde.op subset.eq langc v times langb v$
  ]

  #v(1em)
  #grid(
    columns: (1fr, auto, 1fr),
    column-gutter: 1em,
    row-gutter: 1.2em,
    align: (right, left, left),

    [$n$],
    [$tilde$],
    [$n$],

    [$b$],
    [$tilde$],
    [$b$],

    [$x$],
    [$tilde$],
    [$x$],

    [$lambda x. e$],
    [$tilde$],
    [$lambda x. relate(e)$],

    [$guard(v,kappa,k,l,j)$],
    [$tilde$],
    [$relate(v)$],
  )
]

#lemma(title: "Relation is closed under check-free contexts")[

  If $e ~ relate(e)$ and $F ~ relate(F)$, then $F[e] ~ relate(F)[relate(e)]$.
] <relation-is-correct>

#proof[

By induction on $F ~ relate(F)$.

- Case $square.stroked ~ square.stroked$

  #derivation((
    ($e ~ relate(e)$, [Given]),
    ($F[e] = e$, [Context Plug in]),
    ($relate(F)[relate(e)] = relate(e)$, [Context Plug in]),
    ($F[e] ~ relate(F)[relate(e)]$, []),
  ))

- Case $apply(F_1,e_2) ~ apply(relate(F)_1,e_2)$

  #derivation((
    ($e ~ relate(e)$, [Given]),
    ($F_1[e] ~ relate(F)_1[relate(e)]$, [I.H.]),
    ($F[e] = apply(F_1[e],e_2)$, [Context Plug in]),
    ($relate(F)[relate(e)] = apply(relate(F)_1[relate(e)],relate(e)_2)$, [Context Plug in]),
    ($F[e] ~ relate(F)[relate(e)]$, [definition]),
  ))

- Similarly for other cases
]

#lemma(title: "Relation is closed under substitution")[

  If $e ~ relate(e)$ and $v ~ relate(v)$, then $e[x:=v] ~ relate(e)[x:=relate(v)]$ for every $x$.
] <relation-substitution>

#proof[

By I.H. on $e ~ relate(e)$.

- Case $x ~ x$

  #derivation((
    ($v ~ relate(v)$, [Given]),
    ($e[x:=v] = v$, [Replacement]),
    ($relate(e)[x:=relate(v)] = relate(v)$, [Replacement]),
    ($e[x:=v] ~ relate(e)[x:=relate(v)]$, [By $v ~ relate(v)$])
  ))

- Case $y ~ y$, where $y eq.not x$

  #derivation((
    ($v ~ relate(v)$, [Given]),
    ($e[x:=v] = y$, [Replacement]),
    ($relate(e)[x:=relate(v)] = y$, [Replacement]),
    ($e[x:=v] ~ relate(e)[x:=relate(v)]$, [By $y ~ y$])
  ))

- Case $apply(e_1,e_2) ~ apply(relate(e)_1,relate(e)_2)$

  #derivation((
    ($e_1[x:=v] ~ relate(e)_1[x:=relate(v)]$,[I.H.]),
    ($e_2[x:=v] ~ relate(e)_2[x:=relate(v)]$,[I.H.]),
    ($e[x:=v] = apply(e_1[x:=v],e_2[x:=v])$,[Replacement]),
    ($relate(e)[x:=v] = apply(relate(e)_1[x:=relate(v)],relate(e)_2[x:=relate(v)])$,[Replacement]),
    ($e[x:=v] ~ relate(e)[x:=relate(v)]$, [Definition])
  ))

- Similarly with other cases. Lambda case avoid same variable by replacement $e[x:=v]$ to free variables of $e$.
]

#lemma(title: "Evaluation-context decomposition")[

Forall context $E$, either:
- $E = F$ or
- $E = F[check(k,j,E',v)]$
] <erasure-context-decomposition>

#proof[
  By induction on $E$.

- Case $square.stroked$

  #derivation((
    ($F = square.stroked$,[Choose]),
    ($E = F$,[]),
  ))

- Case $E=check(k,j,E_1,v)$

  #derivation((
    ($F = square.stroked$,[Choose]),
    ($E' = E_1$,[Choose]),
    ($E = F[check(k,j,E_1,v)]$,[])
  ))


- Case $apply(E_1,e)$

  I.H. on $E_1$:

  - Case $E_1 = F_1$

    #derivation((
      ($E = apply(F_1,e)$, []),
      ($F = apply(F_1,e)$, [Choose]),
      ($E = F$, []),
    ))

  - Case $E_1 = F_1[check(k,j,E'_1,v)]$

    #derivation((
      ($E = apply(F_1[check(k,j,E'_1,v)],v)$, []),
      ($F = apply(F_1,v)$, [Choose]),
      ($E' = E'_1$, [Choose]),
      ($E = F[check(k,j,E'_1,v)]$, [])
    ))

- Other cases follows similarly
]


#block(width: 100%)[
  #align(center)[
    $ereq(e,e') = cases(
      "true" & "if" e ~ e' "and" e eq.not F[check(k,j,e_0,v)],
      "true" & "if" e = F[check(k,j,e_0,v)] "and" e' = relate(F)[relate(v)],
      "false" & "otherwise",
    )$
  ]
]

#lemma(title: "Erasure satisfies the state predicate")[

  If $e' = erase(e)$, then $ereq(e,e')$.
] <erasure-is-relation>

#proof[
I.H on $e' = erase(e)$.

Because the compiler doesn't compile check (runtime expression), we never get the second clause of $"EQ"$. Therefore, $e eq.not F[check(k,j,e_0,v)]$, and all child nodes of $e$ also not this form.

- Case $e' = erase(mon(k,l,j,kappa,e_1)) = erase(e_1) = e'_1$

  #derivation((
    ($ereq(e_1,e'_1)$,[I.H.]),
    ($e_1 ~ e'_1$, [First clause EQ]),
    ($mon(k,l,j,kappa,e_1) ~ relate(e)_1$,[Definition]),
    ($e_1 ~ relate(e)_1$,[Definition]),
    ($relate(e)_1 = e'_1$,[Choose]),
    ($mon(k,l,j,kappa,e_1) ~ e'_1$,[]),
    ($ereq(e,e')$,[First clause EQ]),
  ))

- Case $e' = erase(apply(e_1,e_2)) = apply(erase(e_1),erase(e_2)) = apply(e'_1,e'_2)$

  #derivation((
    ($ereq(e_1,e'_1)$,[I.H.]),
    ($ereq(e_2,e'_2)$,[I.H.]),
    ($e_1 ~ e'_1$, [First clause EQ]),
    ($e_2 ~ e'_2$, [First clause EQ]),
    ($apply(e_1,e_2) ~ apply(relate(e)_1,relate(e)_2)$,[Definition]),
    ($ereq(e,e')$,[First clause EQ]),
  ))

- Other cases follow similarly to the above case.
]


== Main Theorem Proof

@erasure-proof-strategy shows the structure of the proof. Erasure initializes the state predicate $ereq(e,e')$ by @erasure-is-relation. Each non-blaming source step $e_i cstep e_(i+1)$ is matched by zero or more target steps $e'_i step1 e'_(i+1)$ while preserving $ereq(e_(i+1),e'_(i+1))$ (@erasure-step-simulation). Chaining these simulations with @erasure-multistep-simulation shows that whenever the source reaches $b$, the erased target reaches the same $b$.

#figure(caption: [Structure of the contract erasure proof. Dashed vertical lines denote ER.])[
  #diagram(
    spacing: (2.9em, 3em),
    node-inset: 2pt,

    // Source execution.
    node((0, 0), $e$),
    node((1, 0), $e_1$),
    node((2, 0), $e_2$),
    node((3, 0), $dots.c$),
    node((4, 0), $b$),
    edge((0, 0), (1, 0), "->", $cstep$, label-side: left),
    edge((1, 0), (2, 0), "->", $cstep$, label-side: left),
    edge((2, 0), (3, 0), "->", $cstep$, label-side: left),
    edge((3, 0), (4, 0), "->", $cstep$, label-side: left),

    // Erased execution. Putting the erasure equation in the first target
    // node avoids a detached label and keeps the diagram within thesis width.
    node((0, 2), $e' = erase(e)$),
    node((1, 2), $e'_1$),
    node((2, 2), $e'_2$),
    node((3, 2), $dots.c$),
    node((4, 2), $b$),
    // Step Simulation justifies each horizontal target segment. Use compact
    // linked names rather than full theorem references, which are too wide.
    edge((0, 2), (1, 2), "->", $step1$, label-side: right),
    edge((1, 2), (2, 2), "->", $step1$, label-side: right),
    edge((2, 2), (3, 2), "->", $step1$, label-side: right),
    edge((3, 2), (4, 2), "->", $step1$, label-side: right),

    // Initialization and the chained conclusion label their ER witnesses.
    edge((0, 0), (0, 2), "--",
      text(size: 0.54em)[#link(<erasure-is-relation>)[@erasure-is-relation]],
      label-side: left, label-pos: 48%, label-fill: white),
    edge((1, 0), (1, 2), "--",
      text(size: 0.54em)[#link(<erasure-step-simulation>)[@erasure-step-simulation]],
      label-side: right, label-pos: 50%, label-fill: white),
    edge((2, 0), (2, 2), "--",
      text(size: 0.54em)[#link(<erasure-step-simulation>)[]],
      label-side: left, label-pos: 50%, label-fill: white),
    edge((4, 0), (4, 2), "--",
      text(size: 0.54em)[#link(<erasure-multistep-simulation>)[@erasure-multistep-simulation]],
      label-side: left, label-pos: 50%, label-fill: white),
  )
] <erasure-proof-strategy>

#theorem(title: "Contract Erasure Theorem")[

  If $e' = erase(e)$ and $e cstep1 b$, then $e' step1 b$.
] <contract-erasure>

#proof[

#derivation((
  ($ereq(e,e')$, [@erasure-is-relation]),
  ($e' step1 b$, [@erasure-multistep-simulation]),
))
]

#lemma(title: "Erasure Multistep Simulation")[

  If $ereq(e,e')$ and $e cstep1 b$ then $e' step1 b$.
] <erasure-multistep-simulation>

#proof[

By induction on $e cstep1 b$.

- Case $b cstep1 b$

  #derivation((
    ($ereq(e,e')$,[Given]),
    ($e ~ e'$, [First clause EQ]),
    ($e' = b$, [Relation inversion $b ~ e'$]),
    ($e' step1 b$, [Reflexivity]),
  ))

- Case $e cstep e_1$ and $e_1 cstep1 b$

  By cases on $e cstep e_1$.

  - Case $e = E[blame(k,j)] cstep blame(k,j) = e_1$ for some $E eq.not square.stroked,k,j$

    #derivation((
      ($e_1 cstep1 blame(k,j)$, [Reflexivity]),
      ($e_1 cstep1 b$, [Given]),
      ($bot$, [Contradiction]),
    ))

  - Case $e = E[e_2] cstep E[e_3] = e_1$ where $e_2 cstepx e_3$ is a redex, and $e_2 != blame(k,j)$.

    #derivation((
      ($ereq(e,e')$,[Given]),
      ($e cstep e_1$,[Given]),
      ($e eq.not E[blame(k,j)]$,[Case assumption]),
    ))

    - Case $e_2 = check(k,j,falseb,v)$, and $e_3 = blame(k,j)$

      #derivation((
        ($e_1 cstep blame(k,j)$, [Step-C]),
        ($e_1 cstep1 blame(k,j)$, []),
        ($e_1 cstep1 b$, [Given]),
        ($bot$, [Contradiction]),
      ))

    - Other cases, $e_2 eq.not check(k,j,falseb,v)$, and $e_3 eq.not blame(k,j)$

      Relation is not local so we run simulation on $e cstep e_1$.

      #derivation((
        ($e eq.not E[check(k,j,falseb,v)]$, [Generalize]),
        ($e' step1 e'_1$, [@erasure-step-simulation]),
        ($ereq(e_1, e'_1)$, [@erasure-step-simulation]),
        ($e'_1 step1 b$, "I.H."),
        ($e' step1 b$, [Transitive]),
      ))

]

#lemma(title: "Erasure Step Simulation")[

  If $ereq(e_1,e'_1)$, $e_1 cstep e_2$, and $e_1 eq.not E_(1a)[blame(k_(1a),j_(1a))]$ and $e_1 eq.not E_(1b)[check(k_(1b),j_(1b),falseb,v)]$, then there is $e'_2$ such that $e'_1 step1 e'_2$ and $ereq(e_2,e'_2)$.
] <erasure-step-simulation>

#proof[

By case analysis of $ereq(e_1,e'_1)$:

- Case $e_1 ~ e'_1$ and $e_1 eq.not F[check(k_1,j_1,e_(1a),v)]$

- Case $e_1 eq F[check(k_1,j_1,e_(1a),v)]$ and $e'_1 = relate(F)[relate(v)]$

  - Case $e_(1a) = trueb$

    $e_1 cstep F[v]$

  - Case $e_(1a) = falseb$

  - Case $e_(1a) = v$, and $v eq.not b$. Impossible, no rule.

  - Case $e_(1a) cstepx e_(1b)$

By case analysis of $e_1 cstep e_2$ with $e_1 != E_1[blame(k_1,j_1)]$.

#derivation((
  ($e_1 = E[e_3]$, rn("C-Step")),
  ($e_2 = E[e_4]$, rn("C-Step")),
  ($e_3 cstepx e_4$, rn("C-Step")),
  ($e'_1 = relate(E)[relate(e)_3]$, [@context-decomposition-relation]),
))

By cases on the redex reduction $e_3 cstepx e_4$.

- Case $apply((lambda x. e_5),v_5) cstepx e_5[x:=v_5]$

  #derivation((
    ($relate(e)_3 = apply((lambda x. relate(e)_5),relate(v)_5)$, [definition of $tilde$]),
    ($apply((lambda x. relate(e)_5),relate(v)_5) stepx relate(e)_5[x:=relate(v)_5]$, rn("S-App")),
    ($e_4 ~ relate(e)_5[x:=relate(v)_5]$, [@relation-substitution]),
    ($e'_1 step1 relate(E)[relate(e)_4] = e'_2$, [reflexivity]),
    ($e_2 ~ e'_2$, [@relation-is-correct]),
  ))

- Case $mu x : tau. e_3 cstepx e_3[x:=mu x : tau. e_3]$

  Similar to the preceding case.

- Case $check(k,j,trueb,v) cstepx v$

  #derivation((
    ($relate(e)_3 = relate(v)$, [definition of $tilde$]),
    ($e_4 ~ relate(v)$, [definition of $tilde$]),
    ($e'_1 step1 relate(E)[relate(v)] = e'_2$, [reflexivity]),
    ($e_2 ~ e'_2$, [@relation-is-correct]),
  ))

- Case $check(k,j,falseb,v) cstepx blame(k,j)$

  #derivation((
    ($e_2 = E[blame(k,j)]$, rn("C-Step")),
    ($e_2 != E_2[blame(k_2,j_2)]$, "Given"),
    ($bot$, [impossible]),
  ))

- Case $mon(k,l,j,flat(e_3),v_3) cstepx check(k,j,apply(e_3,v_3),v_3)$

  #derivation((
    ($relate(e)_3 = relate(v)_3$, [definition of $tilde$]),
    ($e_4 ~ relate(v)_3$, [definition of $tilde$]),
    ($e'_1 step1 relate(E)[relate(v)_3] = e'_2$, [reflexivity]),
    ($e_2 ~ e'_2$, [@relation-is-correct]),
  ))

- Case $mon(k,l,j,kappa,v_3) cstepx guard(v_3,kappa,k,l,j)$

  #derivation((
    ($relate(e)_3 = relate(v)_3$, [definition of $tilde$]),
    ($e_4 ~ relate(v)_3$, [definition of $tilde$]),
    ($e'_1 step1 relate(E)[relate(v)_3] = e'_2$, [reflexivity]),
    ($e_2 ~ e'_2$, [@relation-is-correct]),
  ))

- Case $apply(guard(v_1,kappa_1 -> kappa_2,k,l,j),v_2) cstepx mon(k,l,j,kappa_2,apply(v_1,mon(l,k,j,kappa_1,v_2)))$

  #derivation((
    ($relate(e)_3 = apply(relate(v)_1,relate(v)_2)$, [definition of $tilde$]),
    ($relate(e)_4 ~ apply(relate(v)_1,relate(v)_2)$, [definition of $tilde$]),
    ($e'_1 step1 relate(E)[apply(relate(v)_1,relate(v)_2)] = e'_2$, [reflexivity]),
    ($e_2 ~ e'_2$, [@relation-is-correct]),
  ))

- Case $apply(guard(v_1,dep(kappa_1,lambda x. kappa_2),k,l,j),v_2) cstepx mon(k,l,j,kappa_3,apply(v_1,mon(l,k,j,kappa_1,v_2)))$, where $kappa_3 = kappa_2[x:=mon(l,j,j,kappa_1,v_2)]$

  Similar to the preceding case.
]

#lemma(title: "Relation Decomposition Through Contexts")[

  If $e_1 ~ e'_1$, $e_1 = E[e_2]$, and $e_2$ is a redex, then there are $relate(E)$ and $relate(e)_2$ such that $E ~ relate(E)$ and $e_2 ~ relate(e)_2$ and $e'_1 = relate(E)[relate(e)_2]$.
] <context-decomposition-relation>

#proof[
]

#line(length: 100%)

#lemma(title: "Successful Erasure Simulation")[

  If $ereq(e_1,e'_1)$ and $e_1 cstep e_2$, where $e_2$ is not a blaming expression, then there exists an $e'_2$ such that
  $e'_1 estep^* e'_2$ and $ereq(e_2,e'_2)$.

  The target may take zero, one, or more steps. In particular, successful check reductions are stuttering steps: they may be simulated by zero target steps. The $ereq$ relation is preserved even when the source contains a pending or nested check whose erased target has already reduced to the related value.
] <successful-erasure-simulation>

#lemma(title: "Successful Evaluation Is Preserved by Erasure")[

  If $ereq(e,e')$ and $e cstep^* v$ without reaching $blame(k,j)$, then there exists a target value $v'$ such that $e' estep^* v'$ and $ereq(v,v')$.
] <successful-erasure-preservation>
