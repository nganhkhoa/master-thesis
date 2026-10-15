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


We define context $F$ that is contexts without $check(k,j,E,v)$.

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
] <langc-relation-is-correct>

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

#lemma(title: "Relation Decomposition Through Contexts")[

  If $e_1 ~ e'_1$, $e_1 = E[e_2]$, and $e_2$ is a redex, then there are $relate(E)$ and $relate(e)_2$ such that $E ~ relate(E)$ and $e_2 ~ relate(e)_2$ and $e'_1 = relate(E)[relate(e)_2]$.
] <langc-context-decomposition-relation>

#proof[
By induction on the check-free context $E$.

- Case $E = square.stroked$

  #derivation((
    ($e_1 = e_2$, [Context Plug in]),
    ($relate(E) = square.stroked$, [Choose]),
    ($relate(e)_2 = e'_1$, [Choose]),
    ($E ~ relate(E)$, [Definition]),
    ($e_2 ~ relate(e)_2$, [Given]),
    ($e'_1 = relate(E)[relate(e)_2]$, [Context Plug in]),
  ))

- Case $E = apply(E_0,e_0)$

  #derivation((
    ($e_1 = apply(E_0[e_2],e_0) ~ e'_1$, [Given]),
    ($E_0[e_2] ~ e'_0$, [Relation inversion]),
    ($e_0 ~ relate(e)_0$, [Relation inversion]),
    ($e'_1 = apply(e'_0,relate(e)_0)$, [Relation inversion]),
    ($E_0 ~ relate(E)_0$, [I.H.]),
    ($e_2 ~ relate(e)_2$, [I.H.]),
    ($e'_0 = relate(E)_0[relate(e)_2]$, [I.H.]),
    ($relate(E) = apply(relate(E)_0,relate(e)_0)$, [Choose]),
    ($E ~ relate(E)$, [Definition]),
    ($e'_1 = relate(E)[relate(e)_2]$, [Context Plug in]),
  ))

- Case $E = apply(v,E_0)$

  #derivation((
    ($e_1 = apply(v,E_0[e_2]) ~ e'_1$, [Given]),
    ($v ~ relate(v)$, [Relation inversion]),
    ($E_0[e_2] ~ e'_0$, [Relation inversion]),
    ($e'_1 = apply(relate(v),e'_0)$, [Relation inversion]),
    ($E_0 ~ relate(E)_0$, [I.H.]),
    ($e_2 ~ relate(e)_2$, [I.H.]),
    ($e'_0 = relate(E)_0[relate(e)_2]$, [I.H.]),
    ($relate(E) = apply(relate(v),relate(E)_0)$, [Choose]),
    ($E ~ relate(E)$, [Definition]),
    ($e'_1 = relate(E)[relate(e)_2]$, [Context Plug in]),
  ))

- Case $E = mon(k,l,j,kappa,E_0)$

  #derivation((
    ($e_1 = mon(k,l,j,kappa,E_0[e_2]) ~ e'_1$, [Given]),
    ($E_0[e_2] ~ e'_1$, [Relation inversion]),
    ($E_0 ~ relate(E)_0$, [I.H.]),
    ($e_2 ~ relate(e)_2$, [I.H.]),
    ($e'_1 = relate(E)_0[relate(e)_2]$, [I.H.]),
    ($relate(E) = relate(E)_0$, [Choose]),
    ($E ~ relate(E)$, [Definition]),
    ($e'_1 = relate(E)[relate(e)_2]$, [Context Plug in]),
  ))

- Other check-free context cases follow similarly.
]

#lemma(title: "Relation is closed under substitution")[

  If $e ~ relate(e)$ and $v ~ relate(v)$, then $e[x:=v] ~ relate(e)[x:=relate(v)]$ for every $x$.
] <langc-relation-substitution>

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
] <langc-erasure-context-decomposition>

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

We define the predicate that will be used for simulation. The beauty of the predicate $ereq(e,e')$ is that $e = E[blame(k,j)]$ returns false, so we can skip this case in simulation proof.

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
] <langc-erasure-is-relation>

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
      // text(size: 0.54em)[#link(<langc-erasure-is-relation>)[@langc-erasure-is-relation]],
      // label-side: right, label-pos: 48%, label-fill: white
    ),
    edge((1, 0), (1, 2), "--",
      // text(size: 0.54em)[#link(<langc-erasure-step-simulation>)[@langc-erasure-step-simulation]],
      // label-side: right, label-pos: 50%, label-fill: white
    ),
    edge((2, 0), (2, 2), "--",
      // text(size: 0.54em)[#link(<langc-erasure-step-simulation>)[@langc-erasure-step-simulation]],
      // label-side: left, label-pos: 50%, label-fill: white
    ),

    edge((4, 0), (4, 2), "--",
      // text(size: 0.54em)[#link(<langc-erasure-multistep-simulation>)[@langc-erasure-multistep-simulation]],
      // label-side: left, label-pos: 50%, label-fill: white
    ),

    node((0.3, 1), text(size: 0.6em)[@langc-erasure-is-relation]),
    node((1.3, 1), text(size: 0.6em)[@langc-erasure-step-simulation]),
    node((2.4, 1), text(size: 0.6em)[@langc-erasure-step-simulation]),
    node((1.5, 2.6), text(size: 0.6em)[chained by @langc-erasure-multistep-simulation]),
  )
] <langc-erasure-proof-strategy>

#theorem(title: "Contract Erasure Theorem")[

  If $e' = erase(e)$ and $e cstep1 b$, then $e' step1 b$.
] <langc-contract-erasure>

#proof[

#derivation((
  ($ereq(e,e')$, [@langc-erasure-is-relation]),
  ($e' step1 b$, [@langc-erasure-multistep-simulation]),
))
]

#lemma(title: "Erasure Multistep Simulation")[

  If $ereq(e,e')$ and $e cstep1 b$ then $e' step1 b$.
] <langc-erasure-multistep-simulation>

${(e,e') | e cstep1 b "and" (e,e') in "EQ"}$. This active filter prevents $e cstep1 blame(k,j)$ as well as anything not $b$. Mainly we worry about $E[blame(k,j)] cstep blame(k,j)$ and $E[check(k,j,falseb,v)] cstep E[blame(k,j)]$. It's a strong claim here that $e cstep1 b$ so we can ignore these states. But the single step simulation must be reworded correctly.

Now if we check the argument for $"EQ"$, we can actually filter out $E[blame(k,j)]$ because it doesn't fit two clauses. So we only care about the check expression.

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
        ($e_1 eq.not E[blame(k,j)]$, []),
        // ($e eq.not E[check(k,j,falseb,v)]$, [Generalize]),
        ($e' step1 e'_1$, [@langc-erasure-step-simulation]),
        ($ereq(e_1, e'_1)$, [@langc-erasure-step-simulation]),
        ($e'_1 step1 b$, "I.H."),
        ($e' step1 b$, [Transitive]),
      ))

]

#lemma(title: "Erasure Step Simulation")[

  If $ereq(e_1,e'_1)$, $e_1 cstep e_2$, and $e_2 eq.not E_2[blame(k,j)]$, then there is $e'_2$ such that $e'_1 step1 e'_2$ and $ereq(e_2,e'_2)$.
] <langc-erasure-step-simulation>

#proof[

By case analysis of $ereq(e_1,e'_1)$:

- Case $e_1 eq F[check(k_1,j_1,e_(1a),v)]$ and $e'_1 = relate(F)[relate(v)]$

  - Case $e_(1a) = trueb$

    #derivation((
      ($e_1 cstep F[v]$, [Step-C]),
      ($e_2 = F[v]$,[]),
      ($e_2 ~ relate(F)[relate(v)]$,[Definition]),
      ($e'_1 step1 relate(F)[relate(v)]$, [Reflexivity]),
      ($e'_2 = relate(F)[relate(v)]$, [Choose]),
    ))


  - Case $e_(1a) = falseb$

  - Case $e_(1a) cstepx e_(1b)$

    #derivation((
      ($e_1 cstep F[check(k_1,j_1,e_(1b),v)]$, [Step-C]),
      ($e_2 = F[check(k_1,j_1,e_(1b),v)]$,[]),
      ($e_2 ~ relate(F)[relate(v)]$,[Definition]),
      ($e'_1 step1 relate(F)[relate(v)]$, [Reflexivity]),
      ($e'_2 = relate(F)[relate(v)]$, [Choose]),
    ))

- Case $e_1 ~ e'_1$ and $e_1 eq.not F[check(k_1,j_1,e_(1a),v)]$

  Casing on $e_1 cstep e_2$:

  - Case $E[blame(k_2,j_2)] cstep blame(k_2,j_2)$ contradiction.

  - Case $E[e_3] cstep E[e_4]$ where $e_3 cstepx e_4$ is a redex.

    By @langc-erasure-context-decomposition,

    - Case $E = F[check(k_3,j_3,E_3,v_3)]$

      $e_1 = F[check(k_3,j_3,E_3[e_3],v_3)]$ contradiction.

    - Case $E = F$ with $F$ a non-check context. Without confusion, we use $E$ below:

      For all cases, we have $E ~ relate(E),e_3 ~ relate(e)_3,e_4 ~ relate(e)_4$ by @langc-context-decomposition-relation.

      By cases on the redex reduction $e_3 cstepx e_4$:

      - Case $apply((lambda x. e_5),v_5) cstepx e_5[x:=v_5]$

        #derivation((
          ($e_3 ~ apply((lambda x. relate(e)_5),relate(v)_5)$, [Definition]),
          ($relate(e)_3 = apply((lambda x. relate(e)_5),relate(v)_5)$, [$e_3 ~ relate(e)_3$]),
          ($apply((lambda x. relate(e)_5),relate(v)_5) stepx relate(e)_5[x:=relate(v)_5]$, rn("S-App")),
          ($e_4 ~ relate(e)_5[x:=relate(v)_5]$, [@langc-relation-substitution]),
          ($relate(e)_4 = relate(e)_5[x:=relate(v)_5]$, [@langc-relation-substitution]),
          ($E[e_3] ~ relate(E)[relate(e)_3]$,[@langc-relation-is-correct]),
          ($e'_1 = relate(E)[relate(e)_3] step1 relate(E)[relate(e)_4] = e'_2$, [Step and Closure]),
          ($e_2 = E[e_4] ~ relate(E)[relate(e)_4] = e'_2$,[@langc-relation-is-correct]),
        ))

      - Case $mu x : tau. e_3 cstepx e_3[x:=mu x : tau. e_3]$

        Similar to the preceding case.

      For below cases, we left out obvious rules about relation.

      - Case $check(k,j,trueb,v) cstepx v$

        #derivation((
          ($relate(e)_3 = relate(v)$, [Definition]),
          ($e_4 ~ relate(v)$, [Definition]),
          ($e'_1 step1 relate(E)[relate(v)] = e'_2$, [Reflexivity]),
          ($e_2 ~ e'_2$, [@langc-relation-is-correct]),
        ))

      - Case $check(k,j,falseb,v) cstepx blame(k,j)$

        #derivation((
          ($e_2 = E[blame(k,j)]$, rn("C-Step")),
          ($e_2 != E_2[blame(k_2,j_2)]$, "Given"),
          ($bot$, [Contradiction]),
        ))

      - Case $mon(k,l,j,flat(e_3),v_3) cstepx check(k,j,apply(e_3,v_3),v_3)$

        #derivation((
          ($relate(e)_3 = relate(v)_3$, [Definition]),
          ($e_4 ~ relate(v)_3$, [Definition]),
          ($e'_1 step1 relate(E)[relate(v)_3] = e'_2$, [Reflexivity]),
          ($e_2 ~ e'_2$, [@langc-relation-is-correct]),
        ))

      - Case $mon(k,l,j,kappa,v_3) cstepx guard(v_3,kappa,k,l,j)$

        #derivation((
          ($relate(e)_3 = relate(v)_3$, [Definition]),
          ($e_4 ~ relate(v)_3$, [Definition]),
          ($e'_1 step1 relate(E)[relate(v)_3] = e'_2$, [Reflexivity]),
          ($e_2 ~ e'_2$, [@langc-relation-is-correct]),
        ))

      - Case $apply(guard(v_1,kappa_1 -> kappa_2,k,l,j),v_2) cstepx mon(k,l,j,kappa_2,apply(v_1,mon(l,k,j,kappa_1,v_2)))$

        #derivation((
          ($relate(e)_3 = apply(relate(v)_1,relate(v)_2)$, [Definition]),
          ($relate(e)_4 ~ apply(relate(v)_1,relate(v)_2)$, [Definition]),
          ($e'_1 step1 relate(E)[apply(relate(v)_1,relate(v)_2)] = e'_2$, [Reflexivity]),
          ($e_2 ~ e'_2$, [@langc-relation-is-correct]),
        ))

      - Case $apply(guard(v_1,dep(kappa_1,lambda x. kappa_2),k,l,j),v_2) cstepx mon(k,l,j,kappa_3,apply(v_1,mon(l,k,j,kappa_1,v_2)))$, where $kappa_3 = kappa_2[x:=mon(l,j,j,kappa_1,v_2)]$

        Similar to the preceding case.

      - Other cases (#langb) follows similarly.
]


#block(width: 100%, fill: rgb("#FFF3CD"), inset: 8pt, radius: 3pt)[
  *Correction note for @langc-erasure-step-simulation.*  The following paragraphs replace the indicated reasoning when completing the proof; the original proof above is deliberately left unchanged.

  *First ER clause: obtain the related context before analyzing redexes.*
  In the case $e_1 ~ e'_1$ and $e_1 eq.not F[check(k,j,e_0,v)]$, invert the source step.  Step-C-Blame is impossible because no blaming expression satisfies $ereq$.  Hence
  $e_1 = E[e_3]$, $e_2 = E[e_4]$, and $e_3 cstepx e_4$.
  Apply @langc-erasure-context-decomposition to $E$.  If
  $E = F[check(k,j,E_0,v_0)]$, then
  $e_1 = F[check(k,j,E_0[e_3],v_0)]$, contradicting the first ER clause.  Therefore $E$ is check-free.  Moreover $e_3$ cannot itself be a check redex, for otherwise $e_1 = E[check(k,j,e_0,v)]$, the same contradiction.

  Now apply @langc-context-decomposition-relation to
  $e_1 ~ e'_1$ and $e_1 = E[e_3]$.  It supplies witnesses $relate(E)$ and $relate(e)_3$ such that
  $E ~ relate(E)$, $e_3 ~ relate(e)_3$, and
  $e'_1 = relate(E)[relate(e)_3]$.  It does *not* supply a relation for $e_4$; that relation is proved separately in each redex case.

  For example, for
  $e_3 = apply((lambda x.e_5),v_5)$, inversion of
  $e_3 ~ relate(e)_3$ yields
  $relate(e)_3 = apply((lambda x.relate(e)_5),relate(v)_5)$,
  with $e_5 ~ relate(e)_5$ and $v_5 ~ relate(v)_5$.  S-App gives the target reduct
  $relate(e)_5[x:=relate(v)_5]$, while @langc-relation-substitution gives
  $e_4 = e_5[x:=v_5] ~ relate(e)_5[x:=relate(v)_5]$.  Closing this relation under $E ~ relate(E)$ proves the ER conclusion.  The $mu$ and other base-language redexes are similar.

  *Check redexes belong only to the second ER clause.*
  In the first clause, check redexes have already been ruled out.  In the second clause,
  $e_1 = F[check(k,j,e_(1a),v)]$ and
  $e'_1 = relate(F)[relate(v)]$:

  - If $e_(1a) = trueb$, choose $e'_2 = e'_1$.  Then
    $e_2 = F[v] ~ relate(F)[relate(v)]$ by @langc-relation-is-correct, so ER holds by its first clause.

  - If $e_(1a) cstepx e_(1b)$, choose $e'_2 = e'_1$.  Then
    $e_2 = F[check(k,j,e_(1b),v)]$, so ER holds by its second clause.

  - If $e_(1a) = falseb$, then $e_2 = F[blame(k,j)]$, contradicting the premise that $e_2$ is not a blaming expression.
]
