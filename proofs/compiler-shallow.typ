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

#let tc(t) = $#t^*$
#let hc = $effs(heffcheck)$
#let wrap(tau, e) = $apply(kw("wrap")[#tau], (lambda \_ : unit. #e))$
#let rel(e) = $accent(#e, tilde)$
#let treq(a,b) = $"EQ"(#a,#b)$
#let hcheck = $kw("H")$

= #langc to #lange Compiler Correctness \ (Shallow Handler)

== Overview

Proof for a compiler from $langc$ to $lange$ using shallow handler, where the continuation does not reinstall the handler.


#grid(
  columns: (auto,auto,auto),
  gutter: 1.5em,

  [$heffcheck : lab$],
  [$=$],
  grid.cell(align: left,
    [${effcheck -> forall alpha. tuple(blab, tuple(alpha -> boolt, alpha)) -> alpha}$]),

  [$hcheck$], [$=$],
  grid.cell(align: left,
    [$mu h. handler({effcheck -> lambda tuple(l,tuple(e,v)). lambda k. apply(h,(lambda \_. ife(apply(e,v),apply(k,v),eblame(l))))}, m: s)$]
  ),

  [$kw("wrap")$], [$=$],
  grid.cell(align: left,
    [$Lambda alpha. med lambda f: unit -> alpha. apply(hcheck, f)$]
  ),
  [], grid.cell(colspan: 2, align: right,
    [where $lambda tuple(l,tuple(e,v))$ deconstructs the argument as tuple pattern]),
)

The handler clause re-installs $hcheck$ around the rest of the program by itself, instead of the continuation doing it. So the whole program always runs under exactly one $handle(heffcheck, dot, m: s)$ at the top, and the predicate of a check runs under the same handler as the program. We write $handle(heffcheck, e, m: s)$ for the program running under the handler of $hcheck$.

Compared to the deep semantics, there are no states without handle, and there is no nested handle for predicates. This makes the relation much simpler.

#line(length: 100%)

== Relation

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
    [$apply(perform(effcheck), tuple(k,tuple(rel(e)_1,rel(e)_2)))$],

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
    [$apply(perform(effcheck),tuple(k,tuple(rel(e),rel(E)^*)))$],

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

  Note: This relation is different from deep handler compiler proof.

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

    // [$apply(E^+,e)$],
    // [$tilde$],
    // [$apply(rel(E)^+,e)$],

    // [$apply(v,E^+)$],
    // [$tilde$],
    // [$apply(v,rel(E)^+)$],

    // [$mon(k,l,j,kappa,E^+)$],
    // [$tilde$],
    // [$mon(k,l,j,kappa,rel(E)^+)$],
  )
]

#v(2em)


#lemma(title: "Relation is closed")[

  If $E^* ~ rel(E)^*$, $e ~ rel(e)$ and $e$ has no check in evaluation position, then $E^*[e] ~ rel(E)^*[rel(e)]$.
] <compiler-shallow-relation-context>

#proof[
By induction on $E$. Follows similarly to @compiler-relation-is-closed because the relations ($R_e,R_E$) is same.

// - Case $E = square.stroked$

//   #derivation((
//     ($E[e] = e$, [Context Plug in]),
//     ($rel(E) = square.stroked$, [Definition]),
//     ($rel(E)[rel(e)] = rel(e)$, [Context Plug in]),
//     ($E[e] ~ rel(E)[rel(e)]$, [Given]),
//   ))

// - Case $E = apply(E_0,e_0)$

//   #derivation((
//     ($E_0[e] ~ rel(E_0)[rel(e)]$, [I.H.]),
//     ($E[e] = apply(E_0[e],e_0)$, [Context Plug in]),
//     ($rel(E)[rel(e)] = apply(rel(E_0)[rel(e)],rel(e)_0)$, [Definition]),
//     ($E[e] ~ rel(E)[rel(e)]$, [Definition]),
//   ))

// - Case $E = apply(v,E_0)$

//   #derivation((
//     ($E_0[e] ~ rel(E_0)[rel(e)]$, [I.H.]),
//     ($E[e] = apply(v,E_0[e])$, [Context Plug in]),
//     ($rel(E)[rel(e)] = apply(rel(v),rel(E_0)[rel(e)])$, [Definition]),
//     ($E[e] ~ rel(E)[rel(e)]$, [Definition]),
//   ))

// - Case $E = E_0[check(k,j,E_1,v)]$

//   #derivation((
//     ($E_1[e] ~ rel(E_1)[rel(e)]$, [I.H.]),
//     ($E[e] = E_0[check(k,j,E_1[e],v)]$, [Context Plug in]),
//     ($E[e] ~ ife(rel(E)_1[rel(e)],apply((lambda x.rel(E)_0[x]),rel(v)),eblame(k))$, [Check row]),
//     ($ife(rel(E_1)[rel(e)],apply((lambda x.rel(E)_0[x]),rel(v)),eblame(k)) = rel(E)[rel(e)]$, [Definition]),
//     ($E[e] ~ rel(E)[rel(e)]$, []),
//   ))

// - Other context forms follow similarly.
]

#lemma(title: "Relation is closed under substitution")[
  If $e ~ rel(e)$ and $v ~ rel(v)$ then $e[x:=v] ~ rel(e)[x:=rel(v)]$.
] <compiler-shallow-relation-substitution>

#proof[
  By induction on $e ~ e'$. Follows @compiler-relation-subst because relations ($R_E,R_e$) are the same.
]

#lemma(title: "Compiler is subset of relation")[

  If $compile(type(Gamma,e_1,tau),e_2, m: s)$ then $e_1 ~ e^*_2$.
] <compiler-shallow-compiler-is-relation>

#proof[

By induction on structure of $compile(type(Gamma,e_1,tau),e_2, m: s)$.

- Case #prooftree(rule(
    $compile(type(Gamma,e_3,tau -> boolt), e_5, m: s)$,
    $compile(type(Gamma,e_4,tau), e_6, m: s)$,
    $compile(type(Gamma,mon(k,l,j,flat(e_3),e_4),tau), apply(perform(effcheck, tau: tau), tuple(k, tuple(e_5, e_6))), m: s)$,
  ))

  #derivation((
    ($e^*_2 = apply(perform(effcheck), tuple(k, tuple(e^*_5, e^*_6)))$, []),
    ($e_3 ~ e^*_5$, [I.H.]),
    ($e_4 ~ e^*_6$, [I.H.]),
    ($e_1 ~ e^*_2$, []),
  ))

- Case #prooftree(rule(
        $compile(type(Gamma,e_3,tau_1 -> tau_2), e_4, m: s)$,
        $compile(type(Gamma,
            lambda f. lambda x. mon(k,l,j,kappa_2,apply(f, mon(l,k,j,kappa_1,x))),
            (tau_1 -> tau_2) -> (tau_1 -> tau_2)),
          e_5, m: s)$,
        $compile(type(Gamma,mon(k,l,j,kappa_1->kappa_2,e_3),tau_1 -> tau_2),apply(e_5, e_4), m: s)$,
      ))

  #derivation((
    ($e^*_2 = apply(e^*_5,e^*_4)$,[]),
    ($e_3 ~ e^*_4$, [I.H.]),
    ($lambda f. lambda x. mon(k,l,j,kappa_2,apply(f, mon(l,k,j,kappa_1,x))) ~ e^*_5$, [I.H.]),
    ($e_1 ~ e^*_2$, []),
  ))

- Case #prooftree(rule(
        $compile(type(Gamma,e_3,tau_1 -> tau_2), e_4, m: s)$,
        $compile(type(Gamma,
            lambda f. lambda x. apply((lambda y. mon(k,l,j,kappa_2,apply(f, mon(l,k,j,kappa_1,x)))), mon(l,j,j,kappa_1,x)),
            (tau_1 -> tau_2) -> (tau_1 -> tau_2)),
          e_5, m: s)$,
        $compile(type(Gamma,mon(k,l,j,dep(kappa_1, lambda y. kappa_2),e_3),tau_1 -> tau_2),apply(e_5, e_4), m: s)$,
      ))


  #derivation((
    ($e^*_2 = apply(e^*_5,e^*_4)$,[]),
    ($e_3 ~ e^*_4$, [I.H.]),
    ($lambda f. lambda x. apply((lambda y. mon(k,l,j,kappa_2,apply(f, mon(l,k,j,kappa_1,x)))), mon(l,j,j,kappa_1,x)) ~ e^*_5$, [I.H.]),
    ($e_1 ~ e^*_2$, []),
  ))

- Other cases follow similarly, by I.H.

]

#lemma(title: "Relation decomposition through check-free contexts")[

  If $E^*[e] ~ e'$, then there exist $E'^*$ and $e'_0$ such that
  $E^* ~ E'^*$ and $e ~ e'_0$ and $e' = E'^*[e'_0]$.
] <compiler-shallow-relation-find-E>

#proof[

By induction on the check-free context $E^*$. Follows @compiler-relation-context-decomposition because relations ($R_E,R_e$) are the same.
]


// #lemma(title: "Find Relation Context")[

// If $e_1 = E[e_2]$ ($e_2$ a redex) and $e_2 != check(k,l,e,v)$ and $e_1 ~ e'_1$ then there exists $rel(E),rel(e)_2$ that $e'_1 = rel(E)[rel(e)_2]$
// ] <compiler-shallow-relation-find-E>

// #proof[

// By induction on $E$

// - Case $square.stroked$

//   #derivation((
//     ($e_1 = e_2$, []),
//     ($e_2 ~ e'_1$, []),
//     ($rel(e)_2 = e'_1$, [Choose]),
//     ($rel(E) = square.stroked$, [Choose]),
//   ))

// - Case $mon(k,l,j,flat(e),E_1)$

//   #derivation((
//     ($e_1 = mon(k,l,j,flat(e),E_1[e_2]) = mon(k,l,j,flat(e),e_3)$, []),
//     ($e_1 ~ apply(perform(effcheck),tuple(k,tuple(rel(e),rel(e)_3)))$, []),
//     ($rel(e)_3 = rel(E)_1[rel(e)_2]$, [I.H. by $e_3 = E_1[e_2] ~ rel(e)_3$]),
//     ($e'_1 = apply(perform(effcheck),tuple(k,tuple(rel(e),rel(E)_1[rel(e)_2])))$, []),
//     ($rel(E) = apply(perform(effcheck),tuple(k,tuple(rel(e),rel(E)_1)))$, [Choose]),
//   ))

// - Case $mon(k,l,j,kappa_1 -> kappa_2,E_1)$

//   #derivation((
//     ($e_1 = mon(k,l,j,kappa_1 -> kappa_2,E_1[e_2]) = mon(k,l,j,kappa_1 -> kappa_2,e_3)$, []),
//     ($e_1 ~ apply((lambda f. lambda x. mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x)))), rel(e)_3)$, []),
//     ($rel(e)_3 = rel(E)_1[rel(e)_2]$, [I.H. by $e_3 = E_1[e_2] ~ rel(e)_3$]),
//     ($e'_1 = apply((lambda f. lambda x. mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x)))), rel(E)_1[rel(e)_2])$, []),
//     ($rel(e) = apply((lambda f. lambda x. mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x)))), rel(E)_1)$, [Choose]),
//     ([Where $f,y != x$ and $f,y in.not "fv"(e_2)$ by alpha-renaming],[]),
//   ))

// - Case $mon(k,l,j,dep(kappa_1, lambda x. kappa_2),E_1)$

//   #derivation((
//     ($e_1 = mon(k,l,j,dep(kappa_1, lambda x. kappa_2),E_1[e_2]) \ quad = mon(k,l,j,dep(kappa_1, lambda x. kappa_2),e_3)$, []),
//     ($e_1 ~ apply((lambda f. lambda y. mon(k,l,j,kappa_3,apply(f,mon(l,k,j,kappa_1,y)))), rel(e)_3)$, []),
//     ($quad kappa_3 = kappa_2[y:=mon(l,j,j,kappa_1,x)]$, []),
//     ($rel(e)_3 = rel(E)_1[rel(e)_2]$, [I.H. by $e_3 = E_1[e_2] ~ rel(e)_3$]),
//     ($e'_1 ~ apply((lambda f. lambda y. mon(k,l,j,kappa_3,apply(f,mon(l,k,j,kappa_1,y)))), rel(E)_1[rel(e)_2])$, []),
//     ($rel(E) = apply((lambda f. lambda y. mon(k,l,j,kappa_3,apply(f,mon(l,k,j,kappa_1,y)))), rel(E)_1)$, [Choose]),
//     ([Where $f,y != x$ and $f,y in.not "fv"(e_2)$ by alpha-renaming],[]),
//   ))

// - Case $check(k,j,E_1,v)$

//   #derivation((
//     ($e_1 = check(k,j,E_1,v)[e_2] = check(k,j,E_1[e_2],v) = check(k,j,e_3,v)$, []),
//     ($e_1 ~ ife(rel(e)_3,apply((lambda x. x), rel(v)),eblame(k))$, []),
//     ($rel(e)_3 = rel(E)_1[rel(e)_2]$, [I.H. by $e_3 = E_1[e_2] ~ rel(e)_3$]),
//     ($e'_1 = ife(rel(E)_1[rel(e)_2],apply((lambda x. x), rel(v)),eblame(k))$, []),
//     ($rel(E) = ife(rel(E)_1,apply((lambda x. x), rel(v)),eblame(k))$, [Choose]),
//     ($$, []),
//   ))

// - Similarly for other cases.
// ]

#lemma(title: "Breaking down Context E")[

  For all contexts $E$, uniquely decompose $E = E^+[E^*]$.

  Uniqueness observation: Recall that $E^*$ has no check contexts.
  - If $E$ does not have check, then it is $E^* = E$, and $E^+ = square.stroked$.
  - Else there is only a single decomposition to get out $E^*$ without check contexts

] <compiler-shallow-context-breakdown>

#proof[
By induction on the structure of $E$. Follows @compiler-context-breakdown because the contexts $E,E^+,E^*$ are the same.
]

#lemma("Context Breakdown Helper")[

If $E^+_1 != square.stroked$ then there is a $E^+_2$, $E^+_2 = K[E^+_1]$.

Where $K = apply(square.stroked,e) | apply(v,square.stroked) | mon(k,l,j,kappa,square.stroked) | check(k,j,square.stroked,v)$
] <compiler-shallow-context-breakdown-1>

#proof[
By induction on the structure of $E^+_1$. Follows @compiler-context-breakdown-1 because the context $E^+$ is the same.
]

== Compiler Correctness

@compiler-shallow-proof-strategy shows the structure of the proof. The source program $e$ compiles to $e'$, and the target program runs $e'$ under $kw("wrap")$. After the handler is installed, the target reaches a state $e''_0$ with $treq(e,e''_0)$ (@compiler-shallow-wrap-step-eq). From then on, every source step $e_i cstep e_(i+1)$ is matched by zero or more target steps $e''_i estep1 e''_(i+1)$ that keep $treq(e_(i+1),e''_(i+1))$ (@compiler-shallow-simulation). Chaining the squares (@compiler-shallow-full-simulation), the source result $r$ and the target result $rel(r)$ are related: a value goes to its related value, and $blame(k,j)$ goes to $eblame(k)$.

#figure(caption: [Structure of the compiler correctness proof. Dashed lines rel states by EQ.])[
  #diagram(
    spacing: (3.2em, 3.2em),
    node-inset: 4pt,
    // source program and its run in #langc
    node((1, 0), $e$),
    node((2, 0), $e_1$),
    node((3, 0), $e_2$),
    node((4, 0), $dots.c$),
    node((5, 0), $r$),
    edge((1, 0), (2, 0), "->", $cstep$),
    edge((2, 0), (3, 0), "->", $cstep$),
    edge((3, 0), (4, 0), "->", $cstep$),
    edge((4, 0), (5, 0), "->", $cstep$),

    // compiling and wrapping
    node((0, 1), $e'$),
    node((0, 2), $wrap(tau, e')$),
    edge((1, 0), (0, 1), "->", $#compiles-into$, label-side: right),
    edge((0, 1), (0, 2), "->", [wrap], label-side: right),
    edge((0, 2), (1, 2), "->", $estep1$, label-side: right),

    // compiled program and its run in #lange
    node((1, 2), $e''_0$),
    node((2, 2), $e''_1$),
    node((3, 2), $e''_2$),
    node((4, 2), $dots.c$),
    node((5, 2), $rel(r)$),
    edge((1, 2), (2, 2), "->", $estep1$, label-side: right),
    edge((2, 2), (3, 2), "->", $estep1$, label-side: right),
    edge((3, 2), (4, 2), "->", $estep1$, label-side: right),
    edge((4, 2), (5, 2), "->", $estep1$, label-side: right),

    // the relation at every step
    edge((1, 0), (1, 2), "--"),
    edge((2, 0), (2, 2), "--"),
    edge((3, 0), (3, 2), "--"),
    edge((5, 0), (5, 2), "--", [EQ], label-side: left),

    // which lemma closes which part
    node((0.55, 1.45), text(size: 0.8em)[@compiler-shallow-wrap-step-eq]),
    node((1.5, 1), text(size: 0.8em)[@compiler-shallow-simulation]),
    node((2.5, 1), text(size: 0.8em)[@compiler-shallow-simulation]),
    node((3.5, 1), text(size: 0.8em)[@compiler-shallow-simulation]),
    node((3, 2.6), text(size: 0.8em)[chained by @compiler-shallow-full-simulation]),
  )
] <compiler-shallow-proof-strategy>

Define a predicate between $langc e$ and $lange e'$.

$
treq(e,e') = cases(
  "true" "if" e ~ e',
  "true" "if" e = E^+[E^*[check(k_1,j_1,e_1,v_1)]] "and",
   quad quad quad e' = ife(rel(e)_1, apply((lambda x. rel(E)^+[rel(E)^*[x]]), rel(v)_1), eblame(k_1)),
  "true" "if" e = E[blame(k,j)] "and" e' = eblame(k),
  "false" "otherwise",
)
$

#theorem()[
  If $compile(type(dot,e,tau),e', m: s)$ and $e^* = "untyped"(wrap(tau,e'))$ and $e cstep1 r$ then $e^* estep1 rel(r)$.

  Where $r$ is a value $v$ or $blame(k,j)$.
]

#proof[
  #derivation((
    ($e^* estep1 e'_1$, [@compiler-shallow-wrap-step-eq]),
    ($treq(e,e'_1)$, [@compiler-shallow-wrap-step-eq]),
    ($e'_1 estep1 rel(r)$, [@compiler-shallow-full-simulation]),
    ($e^* estep1 rel(r)$, []),
  ))
]

#lemma(title: "Wrapped compiled program steps to an equivalent state with source program")[

  If $compile(type(dot,e,tau),e', m: s)$ and $e^*_1 = "untyped"(wrap(tau,e'))$ then it exists $e^*_2$ such that $e^*_1 estep1 handle(heffcheck, e^*_2, m:s)$ and $treq(e,e^*_2)$.
] <compiler-shallow-wrap-step-eq>

#proof[
  #derivation((
    ($e ~ e'^*$, [@compiler-shallow-compiler-is-relation]),
    ($treq(e,e'^*)$, [Case 1]),
    ($e^*_1 estep1 apply(hcheck,lambda \_. e'^*) estep1 handle(heffcheck, e'^*, m: s)$, []),
    ($e^*_2 = e'^*$, [Choose])
  ))
]

#lemma()[
  If $e cstep1 r$ and $treq(e,e')$ then $handle(heffcheck,e', m:s) estep1 rel(r)$.
] <compiler-shallow-full-simulation>

#proof[
  By induction on $e cstep1 r$

  - Case $r cstep1 r$

    - Case $v cstep1 v$

      #derivation((
        ($e' = rel(v)$, [Case 1 $"EQ"$]),
        ($e' estep1 rel(v)$, [Reflexivity]),
      ))

    - Case $blame(k,j) cstep1 blame(k,j)$

      #derivation((
        ($e' = eblame(k)$, [Case 3 $"EQ"$]),
        ($e' estep1 eblame(k)$, [Reflexivity]),
      ))

  - Case $e cstep e_1$ and $e_1 cstep1 r$

    #derivation((
      ($e' estep1 e'_1$, [@compiler-shallow-simulation]),
      ($treq(e_1, e'_1)$, [@compiler-shallow-simulation]),
      ($e'_1 estep1 rel(r)$, [I.H.]),
      ($e' estep1 rel(r)$, []),
    ))
]

#lemma(title: "Performing a check")[

If $bop(E) = emptyset$, then

  $
  & handle(heffcheck, E[apply(perform(effcheck),tuple(k,tuple(e,v)))], m: s) \
  estep1 & handle(heffcheck, ife(apply(e,v), apply((lambda x. E[x]),rel(v)), eblame(k)), m: s)
  $
] <compiler-shallow-perform-check>

#proof[
  $
  & handle(heffcheck, E[apply(perform(effcheck),tuple(k,tuple(e,v)))], m: s) \
  estep1& apply(apply((lambda tuple(l,tuple(e,v)). lambda k. apply(hcheck,(lambda \_. ife(apply(e,v),apply(k,v),eblame(l))))), tuple(k,tuple(e,v))), (lambda x. E[x])) \
  estep1& apply(hcheck,(lambda \_. ife(apply(e,v),apply((lambda x. E[x]),v),eblame(k)))) \
  estep1& handle(heffcheck, ife(apply(e,v),apply((lambda x. E[x]),v),eblame(k)), m: s)
  $
]

#lemma()[
  If $e_1 cstep e_2$ and $treq(e_1,e'_1)$ then there exists $e'_2$ such that $handle(heffcheck,e'_1,m:s) estep1 handle(heffcheck,e'_2,m:s)$ and $treq(e_2,e'_2)$.
] <compiler-shallow-simulation>

#proof(of: <compiler-shallow-simulation>)[

By case analysis on $e_1 cstep e_2$ with respect to $treq(e_1,e'_1)$.

- Case $E[blame(k,j)] cstep blame(k,j)$

  #derivation((
    // ($E ~ rel(E)$, [@compiler-shallow-relation-find-E]),
    ($e'_1 = eblame(k)$, [$"EQ"$ case 3]),
    ($e'_1 estep1 eblame(k)$, [Reflexivity]),
    ($treq(e_2, eblame(k))$, []),
    ($e'_2 = eblame(k)$, [Choose]),
  ))

- Case $E[e_3] cstep E[e_4]$ and $e_3 cstepx e_4$ is a redex

  // Overview: For $e_3 != check(k,j,e,v)$ easily find $rel(E),rel(e)_3$ and because the only match $"EQ"$ case is case 2, then $e'_1 = handle(heffcheck,rel(E)[rel(e)_3], m: s)$. Else, we can identify the shape of $e'_1$ by EQ predicate.

  Overview: Because $e_1 != v$ and $e_1 != E[blame(k,j)]$, it *must* matches case 2. Therefore, $e_1 = E^+[E^*[e]]$, and $e'_1 = handle(heffcheck,rel(E)^+[rel(E)^*[rel(e)]], m:s)$. We know the shape of $e_1$ by both EQ predicate and the case analysis, we can try to unify them together. Most cases can unify $E=E^+[E^*]$ naturally. The cases where it breaks is $e_3=check(k,j,b_4,v_4)$, where we identify $E^+ = E[check(k,j,square.stroked,v_4)], E^*=square.stroked$, and $e_1 = E^+[E^*[b_4]]$, then the relation holds.

  - Case $e_3 = mon(k,l,j,flat(e),v) cstepx check(k,j,apply(e,v),v) = e_4$

    #derivation((
      ($e_1 = E[mon(k,l,j,flat(e),v)] = E^+[E^*[mon(k,l,j,flat(e),v)]]$, []),
      ($E ~ rel(E)$, [@compiler-shallow-relation-find-E]),
      ($e_3 ~ rel(e)_3$, [@compiler-shallow-relation-find-E]),
      ($e'_1 = handle(heffcheck,rel(E)[rel(e)_3], m: s)$, [$"EQ"$ case 2]),
      ($rel(e)_3 = apply(perform(effcheck),tuple(k,tuple(rel(e),rel(v))))$, [Inversion]),
      ($e_2 = E[check(k,j,apply(e,v),v)]$, [Given]),
      ($e'_1 estep1 handle(heffcheck, ife(apply(rel(e),rel(v)), apply((lambda x. rel(E)[x]), rel(v)), eblame(k)), m: s)$, [@compiler-shallow-perform-check]),
      ($treq(e_2,handle(heffcheck, ife(apply(rel(e),rel(v)), apply((lambda x. rel(E)[x]), rel(v)), eblame(k)), m: s))$, [Case 3]),
      ($e'_2 = handle(heffcheck, ife(apply(rel(e),rel(v)), apply((lambda x. rel(E)[x]), rel(v)), eblame(k)), m: s)$, [Choose]),
    ))

  - Case $e_3 = check(k,j,trueb,v) cstepx v = e_4$

    #derivation((
      ($e_3 cstep v$, []),
      ($e_1 = E[check(k,j,trueb,v)]$, [Given]),
      ($e'_1 = handle(heffcheck,ife(trueb,apply((lambda x. rel(E)[x]), rel(v)),eblame(k)), m: s)$, [EQ case 3]),
      ($e'_1 estep1 handle(heffcheck,rel(E)[rel(v)], m: s)$, []),
      ($e_2 = E[v] ~ rel(E)[rel(v)]$, [@compiler-shallow-relation-substitution]),
      ($treq(e_2, handle(heffcheck,rel(E)[rel(v)], m: s))$, []),
      ($e'_2 = handle(heffcheck,rel(E)[rel(v)], m: s)$, [Choose]),
    ))

  - Case $e_3 = check(k,j,falseb,v) cstepx blame(k,j) = e_4$

    #derivation((
      ($e_3 cstep blame(k,j)$, []),
      ($e_1 = E[check(k,j,falseb,v)]$, [Given]),
      ($e'_1 = handle(heffcheck,ife(falseb,apply((lambda x. rel(E)[x]), rel(v)),eblame(k)), m: s)$, [EQ case 3]),
      ($e'_1 estep1 eblame(k)$, []),
      ($e_2 = E[blame(k,j)]$, [Given]),
      ($treq(e_2, eblame(k))$, []),
      ($e'_2 = eblame(k)$, [Choose]),
    ))

  - Case $mon(k,l,j,kappa,v) cstepx guard(v,kappa,k,l,j)$ and $kappa != flat(e)$

      #derivation((
        ($E ~ rel(E)$, [@compiler-shallow-relation-find-E]),
        ($e_3 ~ rel(e)_3$, [@compiler-shallow-relation-find-E]),
      ))

    - Case $kappa = kappa_1 -> kappa_2$

      #derivation((
        ($rel(e)_3 = apply(rel(e)_5,rel(v))$,[Inversion]),
        ($quad e_5=lambda f. lambda x. mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x))) = lambda f. e_(5a)$, []),
        // ($e_6 = apply(e_5,v)=lambda x. mon(k,l,j,kappa_2,apply(v,mon(l,k,j,kappa_1,x)))$, []),
        ($e'_1 = rel(E)[apply(rel(e)_5,rel(v))]$, []),
        ($e'_1 estep rel(E)[rel(e)_(5a)[f:=rel(v)]]$, []),
        ($e_(5a) ~ rel(e)_(5a)$, []),
        ($v ~ rel(v)$, []),
        ($e_(5a)[f:=v] ~ rel(e)_(5a)[f:=rel(v)]$, [@compiler-shallow-relation-substitution]),
        ($e_(5a)[f:=v] = lambda x. mon(k,l,j,kappa_2,apply(v,mon(l,k,j,kappa_1,x)))$, []),
        ($e_4 ~ rel(e)_(5a)[f:=rel(v)]$, [Relation]),
        ($e_2 = E[e_4] ~ rel(E)[rel(e)_(5a)[f:=rel(v)]]$, [@compiler-shallow-relation-context]),
        ($e'_2 = rel(E)[rel(e)_(5a)[f:=rel(v)]]$, [Choose]),
      ))

    - Case $kappa = dep(kappa_1, lambda y. kappa_2)$

      #derivation((
        ($rel(e)_3 = apply(rel(e)_5,rel(v))$,[Inversion]),
        ($quad e_5=lambda f. lambda x. mon(k,l,j,kappa_3,apply(f,mon(l,k,j,kappa_1,x))) = lambda f. e_(5a)$, []),
        ($quad kappa_3=kappa_2[y:=mon(l,j,j,kappa_1,x)]$, []),
        // ($e_6 = apply(e_5,v)=lambda x. mon(k,l,j,kappa_2,apply(v,mon(l,k,j,kappa_1,x)))$, []),
        ($e'_1 = rel(E)[apply(rel(e)_5,rel(v))]$, []),
        ($e'_1 estep rel(E)[rel(e)_(5a)[f:=rel(v)]]$, []),
        ($e_(5a) ~ rel(e)_(5a)$, []),
        ($v ~ rel(v)$, []),
        ($e_(5a)[f:=v] ~ rel(e)_(5a)[f:=rel(v)]$, [@compiler-shallow-relation-substitution]),
        ($e_(5a)[f:=v] = lambda x. mon(k,l,j,kappa_3,apply(v,mon(l,k,j,kappa_1,x)))$, []),
        ($e_4 ~ rel(e)_(5a)[f:=rel(v)]$, [Relation]),
        ($e_2 = E[e_4] ~ rel(E)[rel(e)_(5a)[f:=rel(v)]]$, [@compiler-shallow-relation-context]),
        ($e'_2 = rel(E)[rel(e)_(5a)[f:=rel(v)]]$, [Choose]),
      ))

  - Case $e_3 = apply(guard(v_1,kappa_1 -> kappa_2,k,l,j),v_2) cstepx mon(k,l,j, kappa_2, apply(v_1, mon(l,k,j,kappa_1,v_2))) = e_4$

  - Case $e_3 = apply(guard(v_1,dep(kappa_1, lambda y. kappa_2),k,l,j),v_2) cstepx mon(k,l,j, kappa_3, apply(v_1, mon(l,k,j,kappa_1,v_2))) = e_4$ where $kappa_3 = kappa_2[y:=mon(l,j,j,kappa_1,v_2)]$


  - Other cases are follow similarly.
]
