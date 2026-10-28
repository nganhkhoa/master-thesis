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

#let rel(e) = $accent(#e, tilde)$
#let treq(a,b) = $"EQ"(#a,#b)$
#let wrap(tau, e) = $apply(kw("wrap")[#tau], (lambda \_. #e))$

= #langc to #lange Compiler Correctness \ (Local Handler)

In this part, we provide the proof for a compiler version using local handler. Instead of a global handler outside, a flat contract is compiled into an effect and handle it on the spot. All other compilation rules stay the same. Semantics of handlers can be either Deep or Shallow. However, because Deep Handlers push a new (unused) handler each time a check is performed, Shallow Handlers are chosen for this compiler implementation.


#align(center)[
#v(1em)
#rule-set(
  prooftree(rule(
    name: [Compile-Flat],
    $compile(type(Gamma,e_1,tau -> boolt), e_3, m: l)$,
    $compile(type(Gamma,e_2,tau), e_4, m: l)$,
    $compile(type(Gamma,mon(k,l,j,flat(e_1),e_2),tau), handle(heffcheck,(apply(perform(effcheck, tau: tau), tuple(k, tuple(e_3, e_4)))), m: s), m: l)$,
  ))
)

#v(2em)

#grid(
  columns: (auto,auto,auto),
  align: (right,center,left),
  gutter: 1.5em,

  [$heffcheck : lab$],
  [$=$],
  grid.cell(align: left,
    [${effcheck -> forall alpha. tuple(blab, tuple(alpha -> boolt, alpha)) -> alpha}$]),

  [], [$=$],
  [${effcheck -> lambda tuple(l,tuple(e,v)). lambda k. ife(apply(e,v),apply(k,v),eblame(l))}$],
  [], grid.cell(colspan: 2, align: right,
    [where $lambda tuple(l,tuple(e,v))$ deconstructs the argument as tuple pattern]),
)
]

#line(length: 100%)

== Relations

Before we define relations that will be used in the simulation proof below. We define:

  - Context $E^*$ is any context without $check(k,j,e,v)$ in $langc$.
  - Context $E^+  =& square.stroked | E^+[E^*[check(k,j,square.stroked,v)]]$ // | apply(E^+,e) | apply(v,E^+) | mon(k,l,j,kappa,E^+)$


#block(width: 100%)[
  #rect(stroke: 0.5pt, inset: 5pt)[
    $R_v subset.eq langc v times lange v$
  ]

  Abuse of notation: If $(v,v') in R_v$, we write $v attach(~, br: R_v) v'$ or $v ~ v'$. We write $rel(v)$ for any value $rel(v)$ satisfying $v ~ rel(v)$.

  #v(1em)
  #grid(
    columns: (1fr, auto, 1fr),
    column-gutter: 1em,
    row-gutter: 1.2em,
    align: (right, left, left),

    [$x$],
    [$tilde$],
    [$x$],

    [$b$],
    [$tilde$],
    [$b$],

    [$N$],
    [$tilde$],
    [$N$],

    [$lambda x: tau. e$],
    [$tilde$],
    [$lambda x: tau^*. rel(e)$],

    [$guard(v,kappa_1 -> kappa_2,k,l,j)$],
    [$tilde$],
    [$rel(e)$],
    [],[],grid.cell(align:left,colspan:1)[$e=lambda x: tau. mon(k,l,j,kappa_2,apply(v,mon(l,k,j,kappa_1,x)))$],
    // [],[],grid.cell(align:left,colspan:1)[With $type(dot,tau,v)$],

    [$guard(v,dep(kappa_1, lambda y. kappa_2),k,l,j)$],
    [$tilde$],
    [$rel(e)$],
    [],[],grid.cell(align:left,colspan:1)[$e=lambda x: tau. mon(k,l,j,kappa_3,apply(v,mon(l,k,j,kappa_1,x)))$],
    [],[],grid.cell(align:left,colspan:1)[$kappa_3=kappa_2[y:=mon(l,j,j,kappa_1,x)]$],
    // [],[],grid.cell(align:left,colspan:1)[With $type(dot,tau,v)$],
  )
]

#block(width: 100%)[
  #rect(stroke: 0.5pt, inset: 5pt)[
    $R_e subset.eq langc e times lange e$
  ]

  Abuse of notation: If $(e,e') in R_e$, we write $e attach(~, br: R_e) e'$ or $e ~ e'$. We write $rel(e)$ for any expression $rel(e)$ satisfying $e ~ rel(e)$.

  #v(1em)
  #grid(
    columns: (1fr, auto, 1fr),
    column-gutter: 1em,
    row-gutter: 1.2em,
    align: (right, left, left),

    [$v$],
    [$tilde$],
    [$rel(v)$],


    [$apply(e_1,e_2)$],
    [$tilde$],
    [$apply(rel(e)_1,rel(e)_2)$],

    [$mon(k,l,j,flat(e_1),e_2)$],
    [$tilde$],
    [$handle(heffcheck,apply(perform(effcheck), tuple(k,tuple(rel(e)_1,rel(e)_2))),m:s)$],

    [$mon(k,l,j,kappa_1 -> kappa_2,e)$],
    [$tilde$],
    [$apply(rel(e)_1,rel(e))$],
    [],[],grid.cell(align:left,colspan:1)[$e_1=lambda f. lambda x. mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x)))$],

    [$mon(k,l,j,dep(kappa_1, lambda y. kappa_2),e)$],
    [$tilde$],
    [$apply(rel(e)_1,rel(e))$],
    [],[],grid.cell(align:left,colspan:1)[$e_1=lambda f. lambda x. mon(k,l,j,kappa_3,apply(f,mon(l,k,j,kappa_1,x)))$],
    [],[],grid.cell(align:left,colspan:1)[$kappa_3=kappa_2[y:=mon(l,j,j,kappa_1,x)]$],

    [$blame(k,j)$],[$tilde$],[$eblame(k)$],
  )
]

#block(width: 100%)[
  #rect(stroke: 0.5pt, inset: 5pt)[
    $R_(E^*) subset.eq langc E^* times lange E^*$
  ]

  Abuse of notation: If $(E^*,E'^*) in R_(E^*)$, we write $E^* attach(~, br: R_(E^*)) E'^*$ or $E^* ~ E'^*$. We write $rel(E)^*$ for any expression $rel(E)^*$ satisfying $E^* ~ rel(E)^*$.

  #v(1em)
  #grid(
    columns: (1fr, auto, 1fr),
    column-gutter: 1em,
    row-gutter: 1.2em,
    align: (right, left, left),

    [$square.stroked$],
    [$tilde$],
    [$square.stroked$],

    [$apply(E^*,e)$],
    [$tilde$],
    [$apply(rel(E)^*,rel(e))$],

    [$apply(v,E^*)$],
    [$tilde$],
    [$apply(rel(v),rel(E)^*)$],

    [$mon(k,l,j,flat(e),E^*)$],
    [$tilde$],
    [$handle(heffcheck,apply(perform(effcheck), tuple(k,tuple(rel(e)_1,rel(E)^*))),m:s)$],

    [$mon(k,l,j,kappa_1 -> kappa_2,E^*)$],
    [$tilde$],
    [$apply(rel(e)_1,rel(E)^*)$],
    [],[],grid.cell(align:left,colspan:1)[$e_1=lambda f. lambda x. mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x)))$],

    [$mon(k,l,j,dep(kappa_1, lambda y. kappa_2),E^*)$],
    [$tilde$],
    [$apply(rel(e)_1,rel(E)^*)$],
    [],[],grid.cell(align:left,colspan:1)[$e_1=lambda f. lambda x. mon(k,l,j,kappa_3,apply(f,mon(l,k,j,kappa_1,x)))$],
    [],[],grid.cell(align:left,colspan:1)[$kappa_3=kappa_2[y:=mon(l,j,j,kappa_1,x)]$],
  )
]


#block(width: 100%)[
  #rect(stroke: 0.5pt, inset: 5pt)[
    $R_(E^+) subset.eq langc E^+ times lange E^+$
  ]

  Abuse of notation: If $(E^+,E'^+) in R_(E^+)$, we write $E^+ attach(~, br: R_(E^+)) E'^+$ or $E^+ ~ E'^+$. We write $rel(E)^+$ for any expression $rel(E)^+$ satisfying $E^+ ~ rel(E)^+$.

  #v(1em)
  #grid(
    columns: (auto, auto, auto),
    column-gutter: 1em,
    row-gutter: 1.2em,
    align: (right, left, left),

    [$square.stroked$],
    [$tilde$],
    [$square.stroked$],

    [$E^+[E^*[check(k,j,square.stroked,v)]]$],
    [$tilde$],
    [$ife(square.stroked, apply((lambda x. rel(E)^+[rel(E)^*[x])],rel(v)), eblame(k))$],
  )
]

#lemma(title: "Relation is closed")[

  If $E^* ~ rel(E)^*$, $e ~ rel(e)$ and $e$ has no check in evaluation position, then $E^*[e] ~ rel(E)^*[rel(e)]$.
] <compiler-local-relation-context>

#proof[
By induction on $E^* ~ rel(E)^*$. Follows similarly to @compiler-relation-is-closed because the relations ($R_e,R_E$) are the same.
]

#lemma(title: "Relation is closed under substitution")[

  If $e ~ rel(e)$ and $v ~ rel(v)$ then $e[x:=v] ~ rel(e)[x:=rel(v)]$.
] <compiler-local-relation-substitution>

#proof[
By induction on $e ~ e'$. Follows @compiler-relation-subst because relations ($R_v,R_e$) are the same. For this compiler, there is a single case that has their relation different from Deep/Shallow compilers.

- Case $mon(k,l,j,flat(e_1),e_2) ~ handle(heffcheck,apply(perform(effcheck),tuple(k,tuple(rel(e)_1,rel(e)_2))),m:s)$

  #derivation((
    ($e_1[x:=v] ~ rel(e)_1[x:=v']$, [I.H.]),
    ($e_2[x:=v] ~ rel(e)_2[x:=v']$, [I.H.]),
    ($mon(k,l,j,flat(e_1),e_2)[x:=v] ~ handle(heffcheck,apply(perform(effcheck),tuple(k,tuple(rel(e)_1,rel(e)_2))),m:s)[x:=v']$, [Def.]),
  ))

- Other cases follow @compiler-relation-subst because their relations ($R_e$) are the same.
]

#lemma(title: "Relation decomposition through check-free contexts")[

  If $E^*[e] ~ e'$, then there exist $E'^*$ and $e'_0$ such that
  $E^* ~ E'^*$ and $e ~ e'_0$ and $e' = E'^*[e'_0]$.
] <compiler-local-relation-find-E>

#proof[

By induction on the check-free context $E^*$. Follows @compiler-relation-context-decomposition because relations ($R_E,R_e$) are the same.
]


#lemma(title: "Breaking down Context E")[

  For all contexts $E$, uniquely decompose $E = E^+[E^*]$.

  Uniqueness observation: Recall that $E^*$ has no check contexts.
  - If $E$ does not have check, then it is $E^* = E$, and $E^+ = square.stroked$.
  - Else there is only a single decomposition to get out $E^*$ without check contexts

] <compiler-local-context-breakdown>

#proof[
By induction on the structure of $E$. Follows @compiler-context-breakdown because the contexts $E,E^+,E^*$ are the same.
]

#lemma(title: "Compiler is subset of Relation")[

If $compile(type(Gamma,e,tau),e', m: l)$ then $e ~ e'$
] <compiler-local-compiler-is-relation>

#proof[

By induction on structure of $compile(type(Gamma,e_1,tau),e_2, m: l)$.

- Case #prooftree(rule(
    $compile(type(Gamma,e_3,tau -> boolt), e_5, m: s)$,
    $compile(type(Gamma,e_4,tau), e_6, m: s)$,
    $compile(type(Gamma,mon(k,l,j,flat(e_3),e_4),tau), handle(heffcheck,apply(perform(effcheck, tau: tau), tuple(k, tuple(e_5, e_6))),m:s), m: l)$,
  ))

  #derivation((
    ($e^*_2 = handle(heffcheck,apply(perform(effcheck), tuple(k, tuple(e^*_5, e^*_6))),m:s)$, []),
    ($e_3 ~ e^*_5$, [I.H.]),
    ($e_4 ~ e^*_6$, [I.H.]),
    ($e_1 ~ e^*_2$, []),
  ))

- Case #prooftree(rule(
        $compile(type(Gamma,e_3,tau_1 -> tau_2), e_4, m: l)$,
        $compile(type(Gamma,
            lambda f. lambda x. mon(k,l,j,kappa_2,apply(f, mon(l,k,j,kappa_1,x))),
            (tau_1 -> tau_2) -> (tau_1 -> tau_2)),
          e_5, m: l)$,
        $compile(type(Gamma,mon(k,l,j,kappa_1->kappa_2,e_3),tau_1 -> tau_2),apply(e_5, e_4), m: l)$,
      ))

  #derivation((
    ($e^*_2 = apply(e^*_5,e^*_4)$,[]),
    ($e_3 ~ e^*_4$, [I.H.]),
    ($lambda f. lambda x. mon(k,l,j,kappa_2,apply(f, mon(l,k,j,kappa_1,x))) ~ e^*_5$, [I.H.]),
    ($e_1 ~ e^*_2$, []),
  ))

- Case #prooftree(rule(
        $compile(type(Gamma,e_3,tau_1 -> tau_2), e_4, m: l)$,
        $compile(type(Gamma,
            lambda f. lambda x. apply((lambda y. mon(k,l,j,kappa_2,apply(f, mon(l,k,j,kappa_1,x)))), mon(l,j,j,kappa_1,x)),
            (tau_1 -> tau_2) -> (tau_1 -> tau_2)),
          e_5, m: l)$,
        $compile(type(Gamma,mon(k,l,j,dep(kappa_1, lambda y. kappa_2),e_3),tau_1 -> tau_2),apply(e_5, e_4), m: l)$,
      ))


  #derivation((
    ($e^*_2 = apply(e^*_5,e^*_4)$,[]),
    ($e_3 ~ e^*_4$, [I.H.]),
    ($lambda f. lambda x. apply((lambda y. mon(k,l,j,kappa_2,apply(f, mon(l,k,j,kappa_1,x)))), mon(l,j,j,kappa_1,x)) ~ e^*_5$, [I.H.]),
    ($e_1 ~ e^*_2$, []),
  ))

- Other cases follow similarly, by I.H.

]

== Correctness Theorem

$
treq(e,e') = cases(
  "true" "if" e ~ e' "and" e != E^*[check(k_1,j_1,e_1,v_1)],
  "true" "if" e = E^+[E^*[check(k_1,j_1,e_1,v_1)]] "and",
   quad quad quad e' = ife(rel(e)_1, apply((lambda x. rel(E)^+[rel(E)^*[x]]), rel(v)_1), eblame(k_1)),
  "true" "if" e = E[blame(k,j)] "and" e' = eblame(k),
  "false" "otherwise",
)
$


#theorem()[

If $e cstep1 b$ and $compile(type(dot,e,tau),e', m: l)$ then $e' estep1 b$

Runs without a wrapper because the local handler resolves the contract effect in-place.
]

#proof[
  #derivation((
    ($e ~ e'$, [@compiler-local-compiler-is-relation]),
    ($treq(e,e')$, [Case 1 EQ]),
    ($e' estep1 rel(b) = b$, [@compiler-local-multistep-simulation]),
  ))
]


#lemma()[

If $treq(e, e')$ and $e cstep1 r$ then $e' estep1 rel(r)$.

Where $r = v | blame(k,j)$ and $rel(r) = rel(v) | eblame(k)$
] <compiler-local-multistep-simulation>

#proof[

By induction on the structure of $e cstep1 r$

- Case $v cstep1 v$

  #derivation((
    ($treq(e,e')$, [Given]),
    ($e ~ e'$, [Case 1 EQ, otherwise invalid]),
    ($e' = rel(v)$, [Inversion]),
    ($e' estep1 rel(v)$, [Reflexivity]),
  ))

- Case $blame(k,j) cstep1 blame(k,j)$

  #derivation((
    ($treq(e,e')$, [Given]),
    ($e' = eblame(k)$, [Case 3 EQ]),
    ($e' estep1 eblame(k)$, [Reflexivity]),
  ))


- Case $e cstep e_1$ and $e_1 cstep1 r$

  #derivation((
    ($e' estep1 e'_1$, [@compiler-local-step-simulation]),
    ($treq(e_1, e'_1)$, [@compiler-local-step-simulation]),
    ($e'_1 estep1 rel(r)$, [I.H.]),
    ($e' estep1 rel(r)$,[Step]),
  ))
]

#lemma()[

If $treq(e_1, e'_1)$ and $e_1 cstep e_2$ then exists $e'_2$ that $e'_1 estep1 e'_2$ and $treq(e_2, e'_2)$
] <compiler-local-step-simulation>

#proof[

By case analysis on $e_1 cstep e_2$.

- $E[blame(k,j)] cstep blame(k,j)$, and $E eq.not square.stroked$

  #derivation((
    // ($E ~ rel(E)$, [@compiler-local-relation-find-E]),
    ($e'_1 = eblame(k)$, [Case 3 EQ]),
    ($e'_1 estep1 eblame(k)$, [Step and Reflexivity]),
    ($e'_2 = eblame(k)$, [Choose]),
  ))

- $E[e_3] cstep E[e_4]$ where $e_3 cstepx e_4$ is a redex

  Proof Sketch: $E = E^+[E^*[check(k,j,square.stroked,v)]]$, then casing on $E^+$ structure. At the same time, EQ predicate will allow one case analysis ($e_1 ?= E'[check(k',j',e',v')]$). If $E^+ = square.stroked$, use @compiler-local-relation-find-E to find equivalent $rel(E)^*$, else, by EQ case 2 identify the shape of $e'_1$ by $E^+$ relation.


  - Case $e_3 = mon(k,l,j,flat(e),v) cstepx check(k,j,apply(e,v),v) = e_4$

    Actually need $e != E'[check(k',j',e',v')]$ to obtain $rel(e)$. But the proof goes through without stating this fact because we inverse from EQ predicate. When running, this $e$ is never a check, because we don't evaluate inside flat contract.

    #derivation((
      ($e_1 = E[mon(k,l,j,flat(e),v)] = E^+[E^*[mon(k,l,j,flat(e),v)]]$, [@compiler-local-context-breakdown]),
    ))

    - Case $E^+ = square.stroked$

      #derivation((
        ($e_1 = E^*[mon(k,l,j,flat(e),v)]$, []),
        ($E^* ~ rel(E)^*$, [@compiler-local-relation-find-E]),
        ($e_3 ~ rel(e)_3$, [@compiler-local-relation-find-E]),
        ($rel(e)_3 = handle(heffcheck,apply(perform(effcheck),tuple(k,tuple(rel(e),rel(v)))),m:s)$, [Inversion]),
        ($e'_1 = rel(E)^*[handle(heffcheck,apply(perform(effcheck),tuple(k,tuple(rel(e),rel(v)))),m:s)]$, [Case 1 $"EQ"$]),
        ($e'_1 estep1 ife(apply(rel(e),rel(v)),apply((lambda x. rel(E)^*[x]), rel(v)),eblame(k))$, []),

        ($e_2 = E^*[check(k,j,apply(e,v),v)]$, []),
        ($apply(e,v) ~ apply(rel(e),rel(v))$, []),
        ($treq(e_2, ife(apply(rel(e),rel(v)),apply((lambda x. rel(E)^*[x]), rel(v)),eblame(k)))$, [Case 2 $"EQ"$]),
        ($e'_2 = ife(apply(rel(e),rel(v)),apply((lambda x. rel(E)^*[x]), rel(v)),eblame(k))$, [Choose]),
      ))

    - Case $E^+ = E^+_1[E^*_1[check(k_1,j_1,square.stroked,v_1)]]$

      #derivation((
        ($e_2 = E^+_1[E^*_1[check(k_1,j_1,E^*[check(k,j,apply(e,v),v)],v_1)]] = E^+_2[E^*[check(k,j,apply(e,v),v)]]$, []),
        ($rel(E)^+_2 = ife(square.stroked,apply((lambda x. rel(E)^+_1[rel(E)^*_1[x]]), rel(v)_1),eblame(k_1))$, []),
        ($E^+_2[E^*[check(k,j,square.stroked,v)]] ~ ife(square.stroked,apply((lambda x. rel(E)^+_2[rel(E)^*[x]]), rel(v)),eblame(k))$, []),
        ($e'_1 = ife(rel(E)^*[rel(e)_3],apply((lambda x. rel(E)^+_1[rel(E)^*_1[x]]), rel(v)_1),eblame(k_1))$, [Case 2 EQ]),
        ($rel(e)_3 = handle(heffcheck,apply(perform(effcheck),tuple(k,tuple(rel(e),rel(v)))),m:s)$, [Inversion]),
        ($e'_1 estep1 ife(apply(rel(e),rel(v)), apply((lambda x. ife(rel(E)^*[x],apply((lambda y. rel(E)^+_1[rel(E)^*_1[y]]), rel(v)_1),eblame(k_1))), rel(v)), eblame(k))$, []),
        ($quad = ife(apply(rel(e),rel(v)), apply((lambda x. rel(E)^+_2[rel(E)^*[x]]), rel(v)), eblame(k))$, []),
        ($treq(e_2, ife(apply(rel(e),rel(v)), apply((lambda x. rel(E)^+_2[rel(E)^*[x]]), rel(v)), eblame(k)))$, [Case 2 $"EQ"$]),
        ($e'_2 = ife(apply(rel(e),rel(v)), apply((lambda x. rel(E)^+_2[rel(E)^*[x]]), rel(v)), eblame(k))$, [Choose]),
      ))

  - Case $e_3 = check(k,j,trueb,v) cstepx v = e_4$

    Due to the restriction of EQ, only EQ case 2 matches this case.

    #derivation((
      ($e_1 = E[check(k,j,trueb,v)] = E^+[E^*[check(k,j,trueb,v)]]$, [Given and @compiler-local-context-breakdown]),
      ($e_2 = E^+[E^*[v]]$, []),
    ))

    - Case $E^+ = square.stroked$

      #derivation((
        ($e_1 = E^*[check(k,j,trueb,v)]$, []),
        ($e_2 = E^*[v]$, []),
        ($e'_1 = ife(trueb, apply((lambda x. rel(E)^*[x]),rel(v)), eblame(k))$, [EQ case 2]),
        ($e'_1 estep1 rel(E)^*[rel(v)]$, []),
        ($E^*[v] ~ rel(E)^*[rel(v)]$, [@compiler-local-relation-context]),
        ($treq(e_2, rel(E)^*[rel(v)])$, [EQ case 1]),
        ($e'_2 = rel(E)^*[rel(v)]$, [Choose]),
      ))

    - Case $E^+ = E^+_1[E^*_1[check(k_1,j_1,square.stroked,v_1)]]$

      #derivation((
        ($e_2 = E^+_1[E^*_1[check(k_1,j_1,E^*[v],v_1)]]$, []),
        ($e_1 = E^+_1[E^*_1[check(k_1,j_1,E^*[check(k,j,trueb,v)],v_1)]] = E^+_2[E^*[check(k,j,trueb,v)]]$, []),
        ($e'_1 = ife(trueb, apply((lambda y. rel(E)^+_2[rel(E)^*[y]]), rel(v)), eblame(k))$, [Case 2 EQ]),
        ($E^+_2 ~ ife(square.stroked,apply((lambda x. rel(E)^+_1[E^*_1[x]]), rel(v)_1),eblame(k_1)) = rel(E)^+_2$, []),
        ($e'_1 estep1 rel(E)^+_2[rel(E)^*[rel(v)]]$, []),
        ($E^*[v] ~ rel(E)^*[rel(v)]$, [@compiler-local-relation-context]),
        ($treq(e_2, ife(rel(E)^*[rel(v)],apply((lambda x. rel(E)^+_1[E^*_1[x]]), rel(v)_1),eblame(k_1)))$, [Case 2 EQ]),
        ($treq(e_2, rel(E)^+_2[rel(E)^*[rel(v)]])$, [Replace with $rel(E)^+_2$]),
        ($e'_2 = rel(E)^+_2[rel(E)^*[rel(v)]]$, [Choose]),
      ))

  - Case $e_3 = check(k,j,falseb,v) cstepx blame(k,j) = e_4$

    #derivation((
      ($e_1 = E[check(k,j,falseb,v)] = E^+[E^*[check(k,j,falseb,v)]]$, [Given and @compiler-local-context-breakdown]),
      ($e_2 = E^+[E^*[blame(k,j)]]$, []),
    ))

    - Case $E^+ = square.stroked$

      #derivation((
        ($e_1 = E^*[check(k,j,falseb,v)]$, []),
        ($e_2 = E^*[blame(k,j)]$, []),
        ($e'_1 = ife(falseb, apply((lambda x. rel(E)^*[x]),rel(v)), eblame(k))$, [EQ case 2]),
        ($e'_1 estep1 eblame(k)$, []),
        ($treq(e_2, eblame(k))$, [Case 3 EQ]),
        ($e'_2 = eblame(k)$, [Choose]),
      ))

    - Case $E^+ = E^+_1[E^*_1[check(k_1,j_1,square.stroked,v_1)]]$

      #derivation((
        ($e_2 = E^+_1[E^*_1[check(k_1,j_1,E^*[blame(k,j)],v_1)]]$, []),
        ($e_1 = E^+_1[E^*_1[check(k_1,j_1,E^*[check(k,j,falseb,v)],v_1)]] = E^+_2[E^*[check(k,j,falseb,v)]]$, []),
        ($e'_1 = ife(falseb, apply((lambda y. rel(E)^+_2[rel(E)^*[y]]), rel(v)), eblame(k))$, [Case 2 EQ]),
        // ($E^+_2 ~ ife(square.stroked,apply((lambda x. rel(E)^+_1[E^*_1[x]]), rel(v)_1),eblame(k_1)) = rel(E)^+_2$, []),
        ($e'_1 estep1 eblame(k)$, []),
        ($treq(e_2, eblame(k))$, [Case 3 EQ]),
        ($e'_2 = eblame(k)$, [Choose]),
      ))

  - Case $mon(k,l,j,kappa_1 -> kappa_2,v) cstepx guard(v,kappa_1 -> kappa_2,k,l,j)$

    #derivation((
      ($e_1 = E^+[E^*[mon(k,l,j,kappa_1 -> kappa_2,v)]]$, [@compiler-local-context-breakdown]),
    ))

    - Case $E^+ = square.stroked$

      #derivation((
        ($e_1 = E^*[mon(k,l,j,kappa_1 -> kappa_2,v)]$, []),
        ($e_2 = E^*[guard(v,kappa_1 -> kappa_2,k,l,j)]$, []),
        ($E^* ~ rel(E)^*$, [@compiler-local-relation-find-E]),
        ($e_3 ~ rel(e)_3$, [@compiler-local-relation-find-E]),
        ($rel(e)_3 = apply((lambda f. rel(e)_(3a)),rel(v)); e_(3a) = lambda x. mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x)))$, []),
        ($e_1 ~ rel(E)^*[rel(e)_3]$, [@compiler-local-relation-context]),
        ($e'_1 = rel(E)^*[rel(e)_3]$, []),
        ($e'_1 estep1 rel(E)^*[rel(e)_(3a)[f:=rel(v)]]$, []),
        ($e_(3a)[f:=v] = lambda x. mon(k,l,j,kappa_2,apply(v,mon(l,k,j,kappa_1,x)))$, []),
        ($e_(3a)[f:=v] ~ rel(e)_(3a)[f:=rel(v)]$, [@compiler-local-relation-substitution]),
        ($guard(v,kappa_1 -> kappa_2,k,l,j) ~ rel(e)_(3a)[f:=rel(v)]$, [Relation]),
        ($e_2 ~ rel(E)^*[rel(e)_(3a)[f:=rel(v)]]$, [@compiler-local-relation-context]),
        ($treq(e_2, rel(E)^*[rel(e)_(3a)[f:=rel(v)]])$, [Case 1 EQ]),
        ($e'_2 = rel(E)^*[rel(e)_(3a)[f:=rel(v)]]$, [Choose]),
      ))

    - Case $E^+ = E^+_1[E^*_1[check(k_1,j_1,square.stroked,v_1)]]$

      #derivation((
        ($e_1 = E^+_1[E^*_1[check(k_1,j_1,E^*[mon(k,l,j,kappa_1 -> kappa_2,v)],v_1)]]$,[]),
        ($e_2 = E^+_1[E^*_1[check(k_1,j_1,E^*[guard(v,kappa_1 -> kappa_2,k,l,j)],v_1)]]$,[]),
        ($E^* ~ rel(E)^*$, [@compiler-local-relation-find-E]),
        ($e_3 ~ rel(e)_3$, [@compiler-local-relation-find-E]),
        ($rel(e)_3 = apply((lambda f. rel(e)_(3a)),rel(v)); e_(3a) = lambda x. mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x)))$, []),
        ($e_1 ~ rel(E)^*[rel(e)_3]$, [@compiler-local-relation-context]),
        ($e'_1 = ife(rel(E)^*[rel(e)_3], apply((lambda x. rel(E)^+_1[rel(E)^*_1[x]]), rel(v)_1), eblame(k_1))$, [Case 2 EQ]),
        ($e'_1 estep1 ife(rel(E)^*[rel(e)_(3a)[f:=rel(v)]], apply((lambda x. rel(E)^+_1[rel(E)^*_1[x]]), rel(v)_1), eblame(k_1))$,[]),
        ($e_(3a)[f:=v] = lambda x. mon(k,l,j,kappa_2,apply(v,mon(l,k,j,kappa_1,x)))$, []),
        ($e_(3a)[f:=v] ~ rel(e)_(3a)[f:=rel(v)]$, [@compiler-local-relation-substitution]),
        ($guard(v,kappa_1 -> kappa_2,k,l,j) ~ rel(e)_(3a)[f:=rel(v)]$, [Relation]),
        ($E^*[guard(v,kappa_1 -> kappa_2,k,l,j)] ~ rel(E)^*[rel(e)_(3a)[f:=rel(v)]]$, [@compiler-local-relation-context]),
        ($treq(e_2, ife(rel(E)^*[rel(e)_(3a)[f:=rel(v)]], apply((lambda x. rel(E)^+_1[rel(E)^*_1[x]]), rel(v)_1), eblame(k_1)))$,[Case 2 EQ]),
        ($e'_2 = ife(rel(E)^*[rel(e)_(3a)[f:=rel(v)]], apply((lambda x. rel(E)^+_1[rel(E)^*_1[x]]), rel(v)_1), eblame(k_1))$,[Choose]),
      ))

  - Case $mon(k,l,j,dep(kappa_1, lambda y. kappa_2),v) cstepx guard(v,dep(kappa_1, lambda y. kappa_2),k,l,j)$

    Similarly to the functional case. Replacement variable is a fresh $f$, it does not affect anything.

    #derivation((
      ($e_1 = E^+[E^*[mon(k,l,j,dep(kappa_1, lambda y. kappa_2),v)]]$, [@compiler-local-context-breakdown]),
    ))

    - Case $E^+ = square.stroked$

      #derivation((
        ($e_1 = E^*[mon(k,l,j,dep(kappa_1, lambda y. kappa_2),v)]$, []),
        ($e_2 = E^*[guard(v,dep(kappa_1, lambda y. kappa_2),k,l,j)]$, []),
        ($E^* ~ rel(E)^*$, [@compiler-local-relation-find-E]),
        ($e_3 ~ rel(e)_3$, [@compiler-local-relation-find-E]),
        ($rel(e)_3 = apply((lambda f. rel(e)_(3a)),rel(v))$, []),
        ($quad e_(3a) = lambda x. mon(k,l,j,kappa_3,apply(f,mon(l,k,j,kappa_1,x))); kappa_3 = kappa_2[y:=mon(l,j,j,kappa_1,x)]$, []),
        ($e_1 ~ rel(E)^*[rel(e)_3]$, [@compiler-local-relation-context]),
        ($e'_1 = rel(E)^*[rel(e)_3]$, []),
        ($e'_1 estep1 rel(E)^*[rel(e)_(3a)[f:=rel(v)]]$, []),
        ($e_(3a)[f:=v] = lambda x. mon(k,l,j,kappa_3,apply(v,mon(l,k,j,kappa_1,x)))$, []),
        ($e_(3a)[f:=v] ~ rel(e)_(3a)[f:=rel(v)]$, [@compiler-local-relation-substitution]),
        ($guard(v,dep(kappa_1, lambda y. kappa_2),k,l,j) ~ rel(e)_(3a)[f:=rel(v)]$, [Relation]),
        ($e_2 ~ rel(E)^*[rel(e)_(3a)[f:=rel(v)]]$, [@compiler-local-relation-context]),
        ($treq(e_2, rel(E)^*[rel(e)_(3a)[f:=rel(v)]])$, [Case 1 EQ]),
        ($e'_2 = rel(E)^*[rel(e)_(3a)[f:=rel(v)]]$, [Choose]),
      ))

    - Case $E^+ = E^+_1[E^*_1[check(k_1,j_1,square.stroked,v_1)]]$

      #derivation((
        ($e_1 = E^+_1[E^*_1[check(k_1,j_1,E^*[mon(k,l,j,dep(kappa_1, lambda y. kappa_2),v)],v_1)]]$,[]),
        ($e_2 = E^+_1[E^*_1[check(k_1,j_1,E^*[guard(v,dep(kappa_1, lambda y. kappa_2),k,l,j)],v_1)]]$,[]),
        ($E^* ~ rel(E)^*$, [@compiler-local-relation-find-E]),
        ($e_3 ~ rel(e)_3$, [@compiler-local-relation-find-E]),
        ($rel(e)_3 = apply((lambda f. rel(e)_(3a)),rel(v))$, []),
        ($quad e_(3a) = lambda x. mon(k,l,j,kappa_3,apply(f,mon(l,k,j,kappa_1,x))); kappa_3 = kappa_2[y:=mon(l,j,j,kappa_1,x)]$, []),
        ($e_1 ~ rel(E)^*[rel(e)_3]$, [@compiler-local-relation-context]),
        ($e'_1 = ife(rel(E)^*[rel(e)_3], apply((lambda x. rel(E)^+_1[rel(E)^*_1[x]]), rel(v)_1), eblame(k_1))$, [Case 2 EQ]),
        ($e'_1 estep1 ife(rel(E)^*[rel(e)_(3a)[f:=rel(v)]], apply((lambda x. rel(E)^+_1[rel(E)^*_1[x]]), rel(v)_1), eblame(k_1))$,[]),
        ($e_(3a)[f:=v] = lambda x. mon(k,l,j,kappa_3,apply(v,mon(l,k,j,kappa_1,x)))$, []),
        ($e_(3a)[f:=v] ~ rel(e)_(3a)[f:=rel(v)]$, [@compiler-local-relation-substitution]),
        ($guard(v,dep(kappa_1, lambda y. kappa_2),k,l,j) ~ rel(e)_(3a)[f:=rel(v)]$, [Relation]),
        ($E^*[guard(v,dep(kappa_1, lambda y. kappa_2),k,l,j)] ~ rel(E)^*[rel(e)_(3a)[f:=rel(v)]]$, [@compiler-local-relation-context]),
        ($treq(e_2, ife(rel(E)^*[rel(e)_(3a)[f:=rel(v)]], apply((lambda x. rel(E)^+_1[rel(E)^*_1[x]]), rel(v)_1), eblame(k_1)))$,[Case 2 EQ]),
        ($e'_2 = ife(rel(E)^*[rel(e)_(3a)[f:=rel(v)]], apply((lambda x. rel(E)^+_1[rel(E)^*_1[x]]), rel(v)_1), eblame(k_1))$,[Choose]),
      ))

  - Case $e_3 = apply(guard(v_1,kappa_1 -> kappa_2,k,l,j),v_2) cstepx mon(k,l,j, kappa_2, apply(v_1, mon(l,k,j,kappa_1,v_2))) = e_4$

    #derivation((
      ($e_1 = E^+[E^*[apply(guard(v_1,kappa_1 -> kappa_2,k,l,j),v_2)]]$, [@compiler-local-context-breakdown]),
    ))

    - Case $E^+ = square.stroked$

      #derivation((
        ($e_1 = E^*[apply(guard(v_1,kappa_1 -> kappa_2,k,l,j),v_2)]$, []),
        ($E^* ~ rel(E)^*$, [@compiler-local-relation-find-E]),
        ($e_3 ~ rel(e)_3$, [@compiler-local-relation-find-E]),
        ($rel(e)_3 = apply(lambda x. rel(e)_(3a), rel(v)_2); e_(3a) = mon(k,l,j,kappa_2,apply(v_1,mon(l,k,j,kappa_1,x)))$, []),
        ($e_1 ~ rel(E)^*[rel(e)_3]$, [@compiler-local-relation-context]),
        ($e'_1 = rel(E)^*[rel(e)_3]$, [Case 1 EQ]),
        ($e'_1 estep1 rel(E)^*[rel(e)_(3a)[x:=rel(v)_2]]$, []),
        ($e_(3a)[x:=v_2] = mon(k,l,j,kappa_2,apply(v_1,mon(l,k,j,kappa_1,v_2)))$, []),
        ($e_(3a)[x:=v_2] ~ rel(e)_(3a)[x:=rel(v)_2]$, [@compiler-local-relation-substitution]),
        ($e_2 = E^*[mon(k,l,j,kappa_2,apply(v_1,mon(l,k,j,kappa_1,v_2)))] ~ rel(E)^*[rel(e)_(3a)[x:=rel(v)_2]]$, [@compiler-local-relation-context]),
        ($treq(e_2, rel(E)^*[rel(e)_(3a)[x:=rel(v)_2]])$, [Case 1 EQ]),
        ($e'_2 = rel(E)^*[rel(e)_(3a)[x:=rel(v)_2]]$, [Choose]),
      ))

    - Case $E^+ = E^+_1[E^*_1[check(k_1,j_1,square.stroked,v_3)]]$

      #derivation((
        ($e_1 = E^+_1[E^*_1[check(k_1, j_1, E^*[apply(guard(v_1,kappa_1 -> kappa_2,k,l,j),v_2)], v_3)]]$, []),
        ($E^* ~ rel(E)^*$, [@compiler-local-relation-find-E]),
        ($e_3 ~ rel(e)_3$, [@compiler-local-relation-find-E]),
        ($rel(e)_3 = apply(lambda x. rel(e)_(3a), rel(v)_2); e_(3a) = mon(k,l,j,kappa_2,apply(v_1,mon(l,k,j,kappa_1,x)))$, []),

        ($E^*[rel(e)_3] ~ rel(E)^*[rel(e)_3]$, [@compiler-local-relation-context]),
        ($e'_1 = ife(rel(E)^*[rel(e)_3], apply((lambda x. rel(E)^+_1[rel(E)^*[x]]), rel(v)_3), eblame(k_1))$, [Case 2 EQ]),
        ($e'_1 estep1 ife(rel(E)^*[rel(e)_(3a)[x:=rel(v)_2]], apply((lambda x. rel(E)^+_1[rel(E)^*[x]]), rel(v)_3), eblame(k_1))$, []),
        ($e_(3a)[x:=v_2] = mon(k,l,j,kappa_2,apply(v_1,mon(l,k,j,kappa_1,v_2)))$, []),
        ($e_(3a)[x:=v_2] ~ rel(e)_(3a)[x:=rel(v)_2]$, [@compiler-local-relation-substitution]),
        ($E^*[mon(k,l,j,kappa_2,apply(v_1,mon(l,k,j,kappa_1,v_2)))] ~ rel(E)^*[rel(e)_(3a)[x:=rel(v)_2]]$, [@compiler-local-relation-context]),
        ($e_2 = E^+_1[E^*_1[check(k_1,j_1,E^*[mon(k,l,j,kappa_2,apply(v_1,mon(l,k,j,kappa_1,v_2)))],v_3)]]$, []),
        ($treq(e_2, ife(rel(E)^*[rel(e)_(3a)[x:=rel(v)_2]], apply((lambda x. rel(E)^+_1[rel(E)^*[x]]), rel(v)_3), eblame(k_1)))$, [Case 2 EQ]),
        ($e'_2 = ife(rel(E)^*[rel(e)_(3a)[x:=rel(v)_2]], apply((lambda x. rel(E)^+_1[rel(E)^*[x]]), rel(v)_3), eblame(k_1))$, [Choose]),
      ))

  - Case $e_3 = apply(guard(v_1,dep(kappa_1, lambda y. kappa_2),k,l,j),v_2) cstepx mon(k,l,j, kappa_3, apply(v_1, mon(l,k,j,kappa_1,v_2))) = e_4$ where $kappa_3 = kappa_2[y:=mon(l,j,j,kappa_1,v_2)]$

    Similar to the functional case. The only problem is $kappa_4 = kappa_2[y:=mon(l,j,j,kappa_1,x)]$ where $x$ is the new argument of the function created for relation. We need to reason $kappa_4[x:=v_2] = kappa_3$, which is obvious.

    #derivation((
      ($e_1 = E^+[E^*[apply(guard(v_1,dep(kappa_1, lambda y. kappa_2),k,l,j),v_2)]]$, [@compiler-local-context-breakdown]),
    ))

    - Case $E^+ = square.stroked$

      #derivation((
        ($e_1 = E^*[apply(guard(v_1,dep(kappa_1, lambda y. kappa_2),k,l,j),v_2)]$, []),
        ($E^* ~ rel(E)^*$, [@compiler-local-relation-find-E]),
        ($e_3 ~ rel(e)_3$, [@compiler-local-relation-find-E]),
        ($rel(e)_3 = apply(lambda x. rel(e)_(3a), rel(v)_2)$, []),
        ($quad e_(3a) = mon(k,l,j,kappa_4,apply(v_1,mon(l,k,j,kappa_1,x))); kappa_4 = kappa_2[y:=mon(l,j,j,kappa_1,x)]$, []),
        ($e_1 ~ rel(E)^*[rel(e)_3]$, [@compiler-local-relation-context]),
        ($e'_1 = rel(E)^*[rel(e)_3]$, [Case 1 EQ]),
        ($e'_1 estep1 rel(E)^*[rel(e)_(3a)[x:=rel(v)_2]]$, []),
        ($e_(3a)[x:=v_2] = mon(k,l,j,kappa_4[x:=v_2],apply(v_1,mon(l,k,j,kappa_1,v_2)))$, []),
        ($kappa_4[x:=v_2]$, []),
        ($quad = kappa_2[y:=mon(l,j,j,kappa_1,x)][x:=v_2] = kappa_2[y:=mon(l,j,j,kappa_1,v_2)]$, [$x in.not "fv"(kappa_2,kappa_1)$]),
        ($quad = kappa_3$, []),
        ($e_(3a)[x:=v_2] = mon(k,l,j,kappa_3,apply(v_1,mon(l,k,j,kappa_1,v_2)))$, []),
        ($e_(3a)[x:=v_2] ~ rel(e)_(3a)[x:=rel(v)_2]$, [@compiler-local-relation-substitution]),
        ($e_2 = E^*[mon(k,l,j,kappa_3,apply(v_1,mon(l,k,j,kappa_1,v_2)))] ~ rel(E)^*[rel(e)_(3a)[x:=rel(v)_2]]$, [@compiler-local-relation-context]),
        ($treq(e_2, rel(E)^*[rel(e)_(3a)[x:=rel(v)_2]])$, [Case 1 EQ]),
        ($e'_2 = rel(E)^*[rel(e)_(3a)[x:=rel(v)_2]]$, [Choose]),
      ))

    - Case $E^+ = E^+_1[E^*_1[check(k_1,j_1,square.stroked,v_3)]]$

      #derivation((
        ($e_1 = E^+_1[E^*_1[check(k_1, j_1, E^*[apply(guard(v_1,dep(kappa_1, lambda y. kappa_2),k,l,j),v_2)], v_3)]]$, []),
        ($E^* ~ rel(E)^*$, [@compiler-local-relation-find-E]),
        ($e_3 ~ rel(e)_3$, [@compiler-local-relation-find-E]),
        ($rel(e)_3 = apply(lambda x. rel(e)_(3a), rel(v)_2)$, []),
        ($quad e_(3a) = mon(k,l,j,kappa_4,apply(v_1,mon(l,k,j,kappa_1,x))); kappa_4 = kappa_2[y:=mon(l,j,j,kappa_1,x)]$, []),

        ($E^*[rel(e)_3] ~ rel(E)^*[rel(e)_3]$, [@compiler-local-relation-context]),
        ($e'_1 = ife(rel(E)^*[rel(e)_3], apply((lambda x. rel(E)^+_1[rel(E)^*[x]]), rel(v)_3), eblame(k_1))$, [Case 2 EQ]),
        ($e'_1 estep1 ife(rel(E)^*[rel(e)_(3a)[x:=rel(v)_2]], apply((lambda x. rel(E)^+_1[rel(E)^*[x]]), rel(v)_3), eblame(k_1))$, []),
        ($e_(3a)[x:=v_2] = mon(k,l,j,kappa_4[x:=v_2],apply(v_1,mon(l,k,j,kappa_1,v_2)))$, []),
        ($kappa_4[x:=v_2]$, []),
        ($quad = kappa_2[y:=mon(l,j,j,kappa_1,x)][x:=v_2] = kappa_2[y:=mon(l,j,j,kappa_1,v_2)]$, [$x in.not "fv"(kappa_2,kappa_1)$]),
        ($quad = kappa_3$, []),
        ($e_(3a)[x:=v_2] = mon(k,l,j,kappa_3,apply(v_1,mon(l,k,j,kappa_1,v_2)))$, []),
        ($e_(3a)[x:=v_2] ~ rel(e)_(3a)[x:=rel(v)_2]$, [@compiler-local-relation-substitution]),
        ($E^*[mon(k,l,j,kappa_3,apply(v_1,mon(l,k,j,kappa_1,v_2)))] ~ rel(E)^*[rel(e)_(3a)[x:=rel(v)_2]]$, [@compiler-local-relation-context]),
        ($e_2 = E^+_1[E^*_1[check(k_1,j_1,E^*[mon(k,l,j,kappa_3,apply(v_1,mon(l,k,j,kappa_1,v_2)))],v_3)]]$, []),
        ($treq(e_2, ife(rel(E)^*[rel(e)_(3a)[x:=rel(v)_2]], apply((lambda x. rel(E)^+_1[rel(E)^*[x]]), rel(v)_3), eblame(k_1)))$, [Case 2 EQ]),
        ($e'_2 = ife(rel(E)^*[rel(e)_(3a)[x:=rel(v)_2]], apply((lambda x. rel(E)^+_1[rel(E)^*[x]]), rel(v)_3), eblame(k_1))$, [Choose]),
      ))


  - Other cases follow similarly.
]
