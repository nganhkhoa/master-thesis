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

= #langc to #lange Compiler Correctness \ (Deep Handler)

== Overview

Proof for a compiler from $langc$ to $lange$ using the deep handler, where the continuation automatically reinstalls the handler.

#grid(
  columns: (auto,auto,auto),
  gutter: 1.5em,

  [$heffcheck : lab$],
  [$=$],
  grid.cell(align: left,
    [${effcheck -> forall alpha. tuple(blab, tuple(alpha -> boolt, alpha)) -> alpha}$]),

  [$kw("wrap")$], [$=$],
  grid.cell(align: left,
    [$mu w : forall alpha. ((teff((), chevron.l heffcheck chevron.r, alpha)) -> alpha). Lambda alpha. med lambda f: (teff((),chevron.l heffcheck chevron.r,alpha)). apply(handler(h, m: d), f)$]
  ),

  [$h$], [$=$],
  [${effcheck -> lambda tuple(l,tuple(e,v)). lambda k. ife(apply(w[kw("bool")], (lambda \_. apply(e,v))),apply(k,v),eblame(l))}$],
  [], grid.cell(colspan: 2, align: right,
    [where $lambda tuple(l,tuple(e,v))$ deconstructs the argument as tuple pattern]),
)


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

  #v(1em)
  #grid(
    columns: (1fr, auto, auto),
    column-gutter: 1em,
    row-gutter: 1.2em,
    align: (right, left, left),

    [$square.stroked$],
    [$tilde$],
    [$square.stroked$],

    [$E^+[E^*[check(k,j,square.stroked,v)]]$],
    [$tilde$],
    [$rel(E)^+[ife(square.stroked, apply((lambda x. handle(heffcheck,rel(E)^*[x], m: d)),rel(v)), eblame(k))]$],

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
  If $e ~ e'$ and $E^* ~ E'^*$ then $E^*[e] ~ E'^*[e']$.
] <compiler-relation-is-closed>

#proof[
By induction on the structure of $E^* ~ E'^*$.

- Case $square.stroked ~ square.stroked$

  #derivation((
    ($E^*[e] = e$, "Context Plug in"),
    ($E'^*[e'] = e'$, "Context Plug in"),
    ($e ~ e'$, "Given"),
    ($E^*[e] ~ E'^*[e']$, []),
  ))

- Case $apply(E^*_1,e_1) ~ apply(rel(E)^*_1,rel(e)_1)$

  #derivation((
    ($E^*_1 ~ rel(E)^*_1$, [Given]),
    ($E^*_1[e] ~ rel(E)^*_1[e']$, [I.H.]),
    ($apply(E^*_1[e], e_1) ~ apply(rel(E)^*_1[e'], rel(e)_1)$, [Relation]),
    ($E^*[e] ~ E'^*[e']$, []),
  ))

- Case $mon(k,l,j,flat(e_1),E^*_1) ~ apply(perform(effcheck),tuple(k,tuple(rel(e)_1,rel(E)^*_1)))$

  #derivation((
    ($E^*_1 ~ rel(E)^*_1$, [Given]),
    ($E^*_1[e] ~ rel(E)^*_1[e']$, [I.H.]),
    ($mon(k,l,j,flat(e_1),E^*_1[e]) ~ apply(perform(effcheck),tuple(k,tuple(rel(e)_1,rel(E)^*_1[e'])))$, [Relation]),
    ($E^*[e] ~ E'^*[e']$, []),
  ))

- Case $mon(k,l,j,kappa_1 -> kappa_2,rel(E)_1) ~ apply(rel(e)_1,rel(E)^*_1)$, with $e_1 = lambda f. lambda x. mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x)))$

  #derivation((
    ($e_1 ~ rel(e)_1$,[Given]),
    ($E^*_1 ~ rel(E)^*_1$, [Given]),
    ($E^*_1[e] ~ rel(E)^*_1[e']$, [I.H.]),
    ($mon(k,l,j,kappa_1 -> kappa_2,E^*_1[e]) ~ apply(rel(e)_1, rel(E)^*_1[e'])$, [Relation]),
    ($E^*[e] ~ E'^*[e']$, []),
  ))

- Case $mon(k,l,j,dep(kappa_1, lambda y. kappa_2),rel(E)_1) ~ apply(rel(e)_1,rel(E)^*_1)$, with $e_1 = lambda f. lambda x. mon(k,l,j,kappa_3,apply(f,mon(l,k,j,kappa_1,x)))$ and $kappa_3=kappa_2[y:=mon(l,j,j,kappa_1,x)]$

  Similarly to the above case

- Other cases follow similarly.
]


#lemma(title: "Relation decomposition through check-free contexts")[

  If $E^*[e] ~ e'$, then there exist $E'^*$ and $e'_0$ such that
  $E^* ~ E'^*$ and $e ~ e'_0$ and $e' = E'^*[e'_0]$.
] <compiler-relation-context-decomposition>

#proof[
By induction on the check-free context $E^*$.

- Case $E^* = square.stroked$

  #derivation((
    ($E^*[e] = e ~ e'$, [Given]),
    ($E'^* = square.stroked$, [Choose]),
    ($e'_0 = e'$, [Choose]),
    ($E^* ~ E'^*$, [Definition]),
    ($e ~ e'_0$, [Given]),
    ($e' = E'^*[e'_0]$, [Context Plug in]),
  ))

- Case $E^* = apply(E^*_0,e_1)$

  #derivation((
    ($apply(E^*_0[e],e_1) ~ e'$, [Given]),
    ($E^*_0[e] ~ e'_0$, [Relation inversion]),
    ($e_1 ~ e'_1$, [Relation inversion]),
    ($e' = apply(e'_0,e'_1)$, [Relation inversion]),
    ($E^*_0 ~ E'^*_0$, [I.H.]),
    ($e ~ e'_2$, [I.H.]),
    ($e'_0 = E'^*_0[e'_2]$, [I.H.]),
    ($E'^* = apply(E'^*_0,e'_1)$, [Choose]),
    ($E^* ~ E'^*$, [Definition]),
    ($e' = E'^*[e'_2]$, [Context Plug in]),
  ))

- Case $E^* = apply(v,E^*_0)$

  #derivation((
    ($apply(v,E^*_0[e]) ~ e'$, [Given]),
    ($v ~ v'$, [Relation inversion]),
    ($E^*_0[e] ~ e'_0$, [Relation inversion]),
    ($e' = apply(v',e'_0)$, [Relation inversion]),
    ($E^*_0 ~ E'^*_0$, [I.H.]),
    ($e ~ e'_1$, [I.H.]),
    ($e'_0 = E'^*_0[e'_1]$, [I.H.]),
    ($E'^* = apply(v',E'^*_0)$, [Choose]),
    ($E^* ~ E'^*$, [Definition]),
    ($e' = E'^*[e'_1]$, [Context Plug in]),
  ))

- Case $E^* = mon(k,l,j,flat(e_0),E^*_0)$

  #derivation((
    ($mon(k,l,j,flat(e_0),E^*_0[e]) ~ e'$, [Given]),
    ($e_0 ~ e'_0$, [Relation inversion]),
    ($E^*_0[e] ~ e'_1$, [Relation inversion]),
    ($e' = apply(perform(effcheck),tuple(k,tuple(e'_0,e'_1)))$, [Relation inversion]),
    ($E^*_0 ~ E'^*_0$, [I.H.]),
    ($e ~ e'_2$, [I.H.]),
    ($e'_1 = E'^*_0[e'_2]$, [I.H.]),
    ($E'^* = apply(perform(effcheck),tuple(k,tuple(e'_0,E'^*_0)))$, [Choose]),
    ($E^* ~ E'^*$, [Definition]),
    ($e' = E'^*[e'_2]$, [Context Plug in]),
  ))

- Case $E^* = mon(k,l,j,kappa,E^*_0)$

  #derivation((
    ($mon(k,l,j,kappa,E^*_0[e]) ~ e'$, [Given]),
    ($E^*_0[e] ~ e'_0$, [Relation inversion]),
    ($e' = apply(e'_c,e'_0)$, [Relation inversion]),
    ($E^*_0 ~ E'^*_0$, [I.H.]),
    ($e ~ e'_1$, [I.H.]),
    ($e'_0 = E'^*_0[e'_1]$, [I.H.]),
    ($E'^* = apply(e'_c,E'^*_0)$, [Choose]),
    ($E^* ~ E'^*$, [Definition]),
    ($e' = E'^*[e'_1]$, [Context Plug in]),
  ))

- Other cases follow similarly.
]


#lemma(title: "Relation is closed under substitution")[

  If $e ~ e'$ and $v ~ v'$ then $e[x:=v] ~ e'[x:=v']$.
] <compiler-relation-subst>

#proof[
By induction on the derivation of $e ~ e'$.

- Case $x ~ x$

  #derivation((
    ($x[x:=v] = v$, [Replacement]),
    ($x[x:=v'] = v'$, [Replacement]),
    ($v ~ v'$, [Given]),
    ($x[x:=v] ~ x[x:=v']$, []),
  ))

- Case $z ~ z$, where $z != x$

  #derivation((
    ($z[x:=v] = z$, [Replacement]),
    ($z[x:=v'] = z$, [Replacement]),
    ($z[x:=v] ~ z[x:=v']$, [Definition]),
  ))

- Case $lambda z.e_1 ~ lambda z.e'_1$

  #derivation((
    ($e_1[x:=v] ~ e'_1[x:=v']$, [I.H.]),
    ($lambda z.e_1[x:=v] ~ lambda z.e'_1[x:=v']$, [Definition]),
    ($(lambda z.e_1)[x:=v] ~ (lambda z.e'_1)[x:=v']$, [Replacement]),
  ))

- Case $apply(e_1,e_2) ~ apply(e'_1,e'_2)$

  #derivation((
    ($e_1[x:=v] ~ e'_1[x:=v']$, [I.H.]),
    ($e_2[x:=v] ~ e'_2[x:=v']$, [I.H.]),
    ($apply(e_1,e_2)[x:=v] = apply(e_1[x:=v],e_2[x:=v])$, [Replacement]),
    ($apply(e'_1,e'_2)[x:=v'] = apply(e'_1[x:=v'],e'_2[x:=v'])$, [Replacement]),
    ($apply(e_1,e_2)[x:=v] ~ apply(e'_1,e'_2)[x:=v']$, [Definition]),
  ))

- Case $mon(k,l,j,flat(e_1),e_2) ~ apply(perform(effcheck),tuple(k,tuple(rel(e)_1,rel(e)_2)))$

  #derivation((
    ($e_1[x:=v] ~ rel(e)_1[x:=v']$, [I.H.]),
    ($e_2[x:=v] ~ rel(e)_2[x:=v']$, [I.H.]),
    ($mon(k,l,j,flat(e_1),e_2)[x:=v] ~ apply(perform(effcheck),tuple(k,tuple(rel(e)_1,rel(e)_2)))[x:=v']$, [Definition]),
  ))

- Case $mon(k,l,j,kappa_1 -> kappa_2,e_1) ~ apply(rel(e)_2,rel(e)_1)$, with $e_2 = lambda f. lambda y. mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,y)))$

  #derivation((
    ($e_1 ~ rel(e)_1$, [Given]),
    ($e_2 ~ rel(e)_2$, [Given]),
    ($e_1[x:=v] ~ rel(e)_1[x:=v']$, [I.H.]),
    ($e_2[x:=v] ~ rel(e)_2[x:=v']$, [I.H.]),
    ($mon(k,l,j,kappa_1 -> kappa_2,e_1)[x:=v] = mon(k,l,j,kappa_1[x:=v] -> kappa_2[x:=v],e_1[x:=v]) $, []),
    ($e_2[x:=v] =  lambda f. lambda y. mon(k,l,j,kappa_2[x:=v],apply(f,mon(l,k,j,kappa_1[x:=v],y)))$, []),
    ($mon(k,l,j,kappa_1 -> kappa_2,e_1)[x:=v] ~ apply(rel(e)_2[x:=v'],rel(e)_1[x:=v'])$, [Relation]),
    ($mon(k,l,j,kappa_1 -> kappa_2,e_1)[x:=v] ~ (apply(rel(e)_2,rel(e)_1))[x:=v']$, []),
  ))

  Choose variables, $f,y != x$ and $f,y in.not "fv"(v,v')$ by alpha-renaming.

- Case $mon(k,l,j,dep(kappa_1, lambda y. kappa_2),rel(e)_1) ~ apply(rel(e)_2,rel(e)_1)$, with $e_2 = lambda f. lambda z. mon(k,l,j,kappa_3,apply(f,mon(l,k,j,kappa_1,z)))$ and $kappa_3=kappa_2[y:=mon(l,j,j,kappa_1,z)]$ and $y != x$

  #derivation((
    ($e_1 ~ rel(e)_1$, [Given]),
    ($e_2 ~ rel(e)_2$, [Given]),
    ($e_1[x:=v] ~ rel(e)_1[x:=v']$, [I.H.]),
    ($e_2[x:=v] ~ rel(e)_2[x:=v']$, [I.H.]),
    ($mon(k,l,j,dep(kappa_1, lambda y. kappa_2),e_1)[x:=v] = \ quad mon(k,l,j,dep(kappa_1[x:=v], lambda y. kappa_2[x:=v]),e_1[x:=v]) $, [Substitution]),
    ($e_2[x:=v] =  lambda f. lambda z. mon(k,l,j,kappa_3[x:=v],apply(f,mon(l,k,j,kappa_1[x:=v],z)))$, []),
    ($kappa_3[x:=v] = (kappa_2[y:=mon(l,j,j,kappa_1,z)])[x:=v]$,[]),
    ($kappa_3[x:=v] = (kappa_2[x:=v])[y:=mon(l,j,j,kappa_1[x:=v],z)]$,[Substitution?]),
    ($mon(k,l,j,dep(kappa_1, lambda y. kappa_2),e_1)[x:=v] ~ apply(rel(e)_2[x:=v'],rel(e)_1[x:=v'])$, [Relation]),
    ($mon(k,l,j,dep(kappa_1, lambda y. kappa_2),e_1)[x:=v] ~ (apply(rel(e)_2,rel(e)_1))[x:=v']$, [Definition]),
  ))

  Choose variables, $f,z != x$ and $f,y,z in.not "fv"(v,v')$ by alpha-renaming.

- Case $mon(k,l,j,dep(kappa_1, lambda x. kappa_2),rel(e)_1) ~ apply(rel(e)_2,rel(e)_1)$, with $e_2 = lambda f. lambda z. mon(k,l,j,kappa_3,apply(f,mon(l,k,j,kappa_1,z)))$ and $kappa_3=kappa_2[x:=mon(l,j,j,kappa_1,z)]$

  // Observe that $x in.not "fv"(kappa_3)$ because of replacement into $kappa_2$. Follows immediately with the above case.

  #derivation((
    ($e_1 ~ rel(e)_1$, [Given]),
    ($e_2 ~ rel(e)_2$, [Given]),
    ($e_1[x:=v] ~ rel(e)_1[x:=v']$, [I.H.]),
    ($e_2[x:=v] ~ rel(e)_2[x:=v']$, [I.H.]),
    ($mon(k,l,j,dep(kappa_1, lambda x. kappa_2),e_1)[x:=v] = \ quad mon(k,l,j,dep(kappa_1[x:=v], lambda x. kappa_2),e_1[x:=v]) $, [Substitution]),
    ($e_2[x:=v] =  lambda f. lambda z. mon(k,l,j,kappa_3[x:=v],apply(f,mon(l,k,j,kappa_1[x:=v],y)))$, []),
    ($kappa_3[x:=v] = (kappa_2[x:=mon(l,j,j,kappa_1,z)])[x:=v]$,[]),
    ($kappa_3[x:=v] = (kappa_2[x:=mon(l,j,j,kappa_1[x:=v],z)])$,[]),
    ($mon(k,l,j,dep(kappa_1, lambda x. kappa_2),e_1)[x:=v] ~ apply(rel(e)_2[x:=v'],rel(e)_1[x:=v'])$, [Relation]),
    ($mon(k,l,j,dep(kappa_1, lambda x. kappa_2),e_1)[x:=v] ~ (apply(rel(e)_2,rel(e)_1))[x:=v']$, [Definition]),
  ))

  Choose variables, $f,z != x$ and $f,y,z in.not "fv"(v,v')$ by alpha-renaming.

- Case $guard(v_1,kappa_1 -> kappa_2,k,l,j) ~ rel(e)_1$, with $e_1=lambda y. mon(k,l,j,kappa_2,apply(v_1,mon(l,k,j,kappa_1,y)))$

  #derivation((
    ($e_1 ~ rel(e)_1$, [Given]),
    ($e_1[x:=v] ~ rel(e)_1[x:=v']$, [I.H.]),
    ($e_1[x:=v]=lambda y. mon(k,l,j,kappa_2[x:=v],apply(v_1[x:=v],mon(l,k,j,kappa_1[x:=v],y)))$, []),
    ($guard(v_1,kappa_1 -> kappa_2,k,l,j)[x:=v] = guard(v_1[x:=v],kappa_1[x:=v] -> kappa_2[x:=v],k,l,j)$, []),
    ($guard(v_1,kappa_1 -> kappa_2,k,l,j)[x:=v] ~ rel(e)_1[x:=v']$, [Relation]),
  ))

  Choose variables, $y != x$ and $y in.not "fv"(v,v')$ by alpha-renaming.

- Case $guard(v,dep(kappa_1, lambda y. kappa_2),k,l,j) ~ rel(e)_1$, with $e_1=lambda z. mon(k,l,j,kappa_3,apply(v,mon(l,k,j,kappa_1,z)))$ and $kappa_3=kappa_2[y:=mon(l,j,j,kappa_1,z)]$

  #derivation((
    ($e_1 ~ rel(e)_1$, [Given]),
    ($e_1[x:=v] ~ rel(e)_1[x:=v']$, [I.H.]),
    ($e_1[x:=v]=lambda y. mon(k,l,j,kappa_3[x:=v],apply(v_1[x:=v],mon(l,k,j,kappa_1[x:=v],x)))$, []),
    ($kappa_3[x:=v] = kappa_2[y:=mon(l,j,j,kappa_1,z)][x:=v]$, []),
    ($kappa_3[x:=v] = (kappa_2[x:=v])[y:=mon(l,j,j,kappa_1[x:=v],z)]$, [Substitution?]),
    ($guard(v_1,dep(kappa_1, lambda y. kappa_2),k,l,j)[x:=v] = \ quad guard(v_1[x:=v],dep(kappa_1[x:=v], lambda y. kappa_2[x:=v]),k,l,j)$, []),
    ($guard(v_1,dep(kappa_1, lambda y. kappa_2),k,l,j)[x:=v] ~ rel(e)[x:=v']$, [Relation]),
  ))

  Choose variables, $z != x$ and $y,z in.not "fv"(v,v')$ by alpha-renaming.

- Case $guard(v,dep(kappa_1, lambda x. kappa_2),k,l,j) ~ rel(e)_1$, with $e_1=lambda z. mon(k,l,j,kappa_3,apply(v,mon(l,k,j,kappa_1,x)))$ and $kappa_3=kappa_2[x:=mon(l,j,j,kappa_1,x)]$

  #derivation((
    ($e_1 ~ rel(e)_1$, [Given]),
    ($e_1[x:=v] ~ rel(e)_1[x:=v']$, [I.H.]),
    ($e_1[x:=v]=lambda y. mon(k,l,j,kappa_3[x:=v],apply(v_1[x:=v],mon(l,k,j,kappa_1[x:=v],x)))$, []),
    ($kappa_3[x:=v] = kappa_2[x:=mon(l,j,j,kappa_1,z)][x:=v]$, []),
    ($kappa_3[x:=v] = kappa_2[x:=mon(l,j,j,kappa_1[x:=v],z)]$, []),
    ($guard(v_1,dep(kappa_1, lambda x. kappa_2),k,l,j)[x:=v] = \ quad guard(v_1[x:=v],dep(kappa_1[x:=v], lambda x. kappa_2),k,l,j)$, []),
    ($guard(v_1,dep(kappa_1, lambda x. kappa_2),k,l,j)[x:=v] ~ rel(e)[x:=v']$, [Relation]),
  ))

  Choose variables, $z != x$ and $z in.not "fv"(v,v')$ by alpha-renaming.

- Other cases follows similarly.
]

#lemma(title: "Breaking down Context E")[

  For all contexts $E$, uniquely decompose $E = E^+[E^*]$.

  Uniqueness observation: Recall that $E^*$ has no check contexts.
  - If $E$ does not have check, then it is $E^* = E$, and $E^+ = square.stroked$.
  - Else there is only a single decomposition to get out $E^*$ without check contexts

] <compiler-context-breakdown>

#proof[
By induction on $E$.

- Case $E = square.stroked$

  Choose $E^+ = E^* = square.stroked$

- Case $E = apply(E_1,e)$

  #derivation((
    ($E_1 = E^+_1[E^*_1]$, "I.H."),
    ($E = apply(E^+_1[E^*_1],e)$, []),
    ($E = (apply(E^+_1,e))[E^*_1]$, []),
  ))

  - Case $E^+_1 = square.stroked$

    #derivation((
      ($E = apply(E^*_1,e)$, []),
      ($E^+ = square.stroked$, [Choose]),
      ($E^* = apply(E^*_1,e)$, [Choose]),
    ))

  - Case $E^+_1 != square.stroked$

    #derivation((
      ($E^+ = apply(E^+_1,e)$, [@compiler-context-breakdown-1 ($K = apply(square.stroked,e)$) and Choose]),
      ($E^* = E^*_1$, [Choose]),
    ))

// - Case $E = mon(k,l,j,kappa,E_1)$

//   #derivation((
//     ($E_1 = E^+_1[E^*_1]$, "I.H."),
//     ($E = mon(k,l,j,kappa,E^+_1[E^*_1])$, []),
//     ($E = mon(k,l,j,kappa,E^+_1)[E^*_1]$, []),
//     ($E^+ = mon(k,l,j,kappa,E^+_1)$, [Choose]),
//     ($E^* = E^*_1$, [Choose]),
//   ))

- Case $E = check(k,j,E_1,v)$

  #derivation((
    ($E_1 = E^+_1[E^*_1]$, "I.H."),
    ($E = check(k,j,E^+_1[E^*_1],v) = check(k,j,E^+_1,v)[E^*_1]$, ""),
  ))

  - Case $E^+_1 = square.stroked$

    #derivation((
      ($E = check(k,j,square.stroked,v)[E^*_1]$, ""),
      ($E^+ = check(k,j,square.stroked,v), E^* = E^*_1$, "Choose"),
    ))

  - Case $E^+_1 != square.stroked$

    #derivation((
      ($E^+_2 = check(k,j,E^+_1,v)$,[@compiler-context-breakdown-1 ($K = check(k,j,square.stroked,v)$)]),
      ($E = E^+_2[E^*]$, []),
    ))

]

#lemma("Context Breakdown Helper")[

If $E^+_1 != square.stroked$ then there is a $E^+_2$, $E^+_2 = K[E^+_1]$.

Where $K = apply(square.stroked,e) | apply(v,square.stroked) | mon(k,l,j,kappa,square.stroked) | check(k,j,square.stroked,v)$
] <compiler-context-breakdown-1>

#proof[

By induction on the structure of $E^+_1$.

- Case $square.stroked$ invalid.

- Case $E^+_3[E^*[check(k,j,square.stroked,v)]]$

  - Case $E^+_3 = square.stroked$

    - Case $K = check(k_1,j_1,square.stroked,v_1)$

      #derivation((
        ($K = E^+_4$, [Definition of $E^+$]),
        ($K[E^+_1] = E^+_4[E^*[check(k,j,square.stroked,v)]]$, []),
        ($E^+_2 = E^+_4[E^*[check(k,j,square.stroked,v)]]$, [Choose]),
      ))

    - Case $K != check(k_1,j_1,square.stroked,v_1)$

      #derivation((
        ($K = E^*_4$, [Definition of $E^*$]),
        ($K[E^+_1] = E^*_4[E^*[check(k,j,square.stroked,v)]] = E^*_5[check(k,j,square.stroked,v)]$, []),
        ($E^+_2 = square.stroked[E^*_5[check(k,j,square.stroked,v)]]$, [Choose]),
      ))

  - Case $E^+_3 != square.stroked$

    #derivation((
      ($E^+_4 = K[E^+_3]$,[I.H.]),
      ($K[E^+_1] = K[E^+_3[E^*[check(k,j,square.stroked,v)]]] = \ quad K[E^+_3][E^*[check(k,j,square.stroked,v)]] = E^+_4[E^*[check(k,j,square.stroked,v)]]$,[]),
      ($E^+_2 = E^+_4[E^*[check(k,j,square.stroked,v)]]$,[Choose]),
    ))
]

// #lemma(title: "Context composition preserves check structure")[

//   If $E^+ = E^+_0[E^*_0[check(k,j,square.stroked,v)]]$ and $E$ is any evaluation context, then $E[E^+] = E^+_1$ for some $E^+_1$ of the form $E^+_1 = E^+_2[E^*_2[check(k',j',square.stroked,v')]]$.
// ] <compiler-context-composition-preservation>

// #proof[
// By induction on the structure of $E$.

// - Case $square.stroked$.

//   #derivation((
//     ($E[E^+] = E^+ = E^+_0[E^*_0[check(k,j,square.stroked,v)]]$, ""),
//   ))

// - Case $E = check(k_0,j_0,E_2,v_0)$

//   #derivation((
//     ($E_2[E^+] = E^+_2$, [I.H.]),
//     ($E[E^+] = check(k_0,j_0,E^+_2[E^+],v_0)$, []),
//     ($check(k_0,j_0,E^+_2,v_0) = E^+_3$, [I.H. with $E = check(k_0,j_0,square.stroked,v_0)$]),
//     ($E^+_1 = E^+_3$,[Choose]),
//   ))

// - Case $E = apply(E_1, e)$.

//   #derivation((
//     ($E_1[E^+] = E^+_1 = E^+_2[E^*_2[check(k',j',square.stroked,v')]]$, [I.H.]),
//     ($E[E^+] = apply(E_1[E^+], e) = apply(E^+_2[E^*_2[check(k',j',square.stroked,v')]], e)$, "Definition"),
//     ($E[E^+] = (apply(E^+_2, e))[E^*_2[check(k',j',square.stroked,v')]]$, ""),
//     ($E^+_1 = (apply(E^+_2, e))[E^*_2[check(k',j',square.stroked,v')]]$, "Choose"),
//   ))

// - Other cases (including monitor contexts) follow similarly.
// ]

#lemma(title: "Compiler is subset of relation")[

  If $compile(type(Gamma,e_1,tau),e_2, m: d)$ then $e_1 ~ e^*_2$.

  In particular, for closed programs, if $compile(type(dot,e_1,tau),e_2, m: d)$ then $e_1 ~ e^*_2$.

  In this lemma, we use $e^*$ as shorthand to denote $e$ untyped.
] <compiler-is-relation>

#proof[

By induction on structure of $compile(type(Gamma,e_1,tau),e_2, m: d)$.

- Case #prooftree(rule(
    $x : tau in Gamma$,
    $compile(type(Gamma, x, tau), x, m: d)$,
  ))

  #derivation((
    ($e^*_2 = x$, "Definition"),
    ($x ~ x$, "Relation"),
  ))

- Case #prooftree(rule(
    $compile(type(Gamma\, x : tau_1, e, tau_2), e', m: d)$,
    $compile(type(Gamma, lambda x : tau_1. e, tau_1 -> tau_2), lambda x : tau_1. e', m: d)$,
  ))

  #derivation((
    ($e^*_2 = lambda x. e'^*$, "Definition"),
    ($e ~ e'^*$, [I.H. on the premise with context $Gamma, x : tau_1$]),
    ($lambda x. e ~ lambda x. e'^*$, "Relation"),
  ))

- Case #prooftree(rule(
    $compile(type(Gamma,e_3,tau -> boolt), e_5, m: d)$,
    $compile(type(Gamma,e_4,tau), e_6, m: d)$,
    $compile(type(Gamma,mon(k,l,j,flat(e_3),e_4),tau), apply(perform(effcheck, tau: tau), tuple(k, tuple(e_5, e_6))), m: d)$,
  ))

  #derivation((
    ($e^*_2 = apply(perform(effcheck), tuple(k, tuple(e^*_5, e^*_6)))$, "Definition"),
    ($e_3 ~ e^*_5$, "I.H."),
    ($e_4 ~ e^*_6$, "I.H."),
    ($e_1 ~ e^*_2$, "Relation"),
  ))

- Case #prooftree(rule(
        $compile(type(Gamma,e_3,tau_2), e_4, m: d)$,
        $compile(type(Gamma,
            lambda f : tau_1 -> tau_2. lambda x : tau_1. mon(k,l,j,kappa_2,apply(f, mon(l,k,j,kappa_1,x))),
            (tau_1 -> tau_2) -> (tau_1 -> tau_2)),
          e_5, m: d)$,
        $compile(type(Gamma,mon(k,l,j,kappa_1->kappa_2,e_1),tau_1 -> tau_2),apply(e_5, e_4), m: d)$,
      ))

  #derivation((
    ($e_3 ~ e^*_4$, "I.H."),
    ($lambda f : tau_1 -> tau_2. lambda x : tau_1. mon(k,l,j,kappa_2,apply(f, mon(l,k,j,kappa_1,x))) ~ e^*_5$, "I.H."),
    ($e_1 ~ e^*_2$, "Relation"),
  ))

- Case #prooftree(rule(
        $compile(type(Gamma,e_3,tau_1 -> tau_2), e_4, m: d)$,
        $compile(type(Gamma,
            lambda f. lambda x. mon(k,l,j,kappa_2[y:=mon(l,j,j,kappa_1,x)],apply(f, mon(l,k,j,kappa_1,x))),
            (tau_1 -> tau_2) -> (tau_1 -> tau_2)),
          e_5, m: d)$,
        $compile(type(Gamma,mon(k,l,j,dep(kappa_1, lambda y. kappa_2),e_3),tau_1 -> tau_2),apply(e_5, e_4), m: d)$,
      ))

  #derivation((
    ($e_3 ~ e^*_4$, "I.H."),
    ($lambda f. lambda x. mon(k,l,j,kappa_2[y:=mon(l,j,j,kappa_1,x)],apply(f, mon(l,k,j,kappa_1,x))) ~ e^*_5$, "I.H."),
    ($e_1 ~ e^*_2$, "Relation"),
  ))

- Other cases are similar.
]

== Compiler Correctness

@compiler-proof-strategy shows the structure of the proof. The source program $e$ compiles to $e'$, and the target program runs $e'$ under $kw("wrap")$. After the handler is installed, the target reaches a state $e''_0$ with $treq(e,e''_0)$ (@compiler-wrap-step-eq). From then on, every source step $e_i cstep e_(i+1)$ is matched by zero or more target steps $e''_i estep1 e''_(i+1)$ that keep $treq(e_(i+1),e''_(i+1))$ (@compiler-simulation). Chaining the squares (@compiler-full-simulation), the source result $r$ and the target result $rel(r)$ are related: a value goes to its related value, and $blame(k,j)$ goes to $eblame(k)$.

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
    node((0.55, 1.45), text(size: 0.8em)[@compiler-wrap-step-eq]),
    node((1.5, 1), text(size: 0.8em)[@compiler-simulation]),
    node((2.5, 1), text(size: 0.8em)[@compiler-simulation]),
    node((3.5, 1), text(size: 0.8em)[@compiler-simulation]),
    node((3, 2.6), text(size: 0.8em)[chained by @compiler-full-simulation]),
  )
] <compiler-proof-strategy>

Define a predicate between $langc e$ and $"Untyped" lange e'$.

$
treq(e,e') = cases(
  "true" "if" e = v "and" e' = rel(v),
  "true" "if" e' = handle(heffcheck,rel(e), m: d) "and" e != E^*[check(k,j,e'',v)],
  "true" "if" e = E^+[E^*[check(k,j,e_1,v)]] "and",
  quad quad quad e' = rel(E)^+[ife(e'_1,apply((lambda x. handle(heffcheck,rel(E)^*[x], m: d)),rel(v)),eblame(j))] "and",
  quad quad quad treq(e_1,e'_1),
  "true" "if" e = E[blame(k,j)] "and" e' = eblame(k),
  "false" "otherwise",
)
$


#theorem(title: "Compiler Correctness")[

  If $compile(type(dot,e,tau),e', m: d)$ and $e^* = "untyped"(wrap(tau,e'))$ and $e cstep1 b$ then $e^* estep1 b$.
] <compiler-correctness>

#proof[

  #derivation((
    ($e^* estep1 e'_1$, [@compiler-wrap-step-eq]),
    ($treq(e,e'_1)$, [@compiler-wrap-step-eq]),
    ($e'_1 estep1 b$, [@compiler-full-simulation]),
    ($e^* estep1 b$, "Combining steps"),
  ))
]

#lemma(title: "Wrapped program steps into an EQ state with source")[

If $compile(type(dot,e,tau),e', m: d)$ and $e^*_1 = wrap(tau,e')$ then it exists $e^*_2$ such that $e^*_1 estep1 e^*_2$ and $treq(e,e^*_2)$.
] <compiler-wrap-step-eq>

#proof[

#derivation((
  ($e ~ e'^*$, [@compiler-is-relation]),
  ($e^*_1 estep1 apply(handler(heffcheck, m: d),lambda \_. e'^*) estep1 handle(heffcheck, e'^*, m: d) = e^*_2$, []),
  ($treq(e,e^*_2)$, "Definition"),
))

// By case on $compile(type(dot,e,tau),e', m: d)$.

// - Case #prooftree(rule(
//     $compile(type(dot,e_3,tau -> boolt), e_5, m: d)$,
//     $compile(type(dot,e_4,tau), e_6, m: d)$,
//     $compile(type(dot,mon(k,l,j,flat(e_3),e_4),tau), apply(perform(effcheck, tau: tau), tuple(k, tuple(e_5, e_6))), m: d)$,
//   ))

//   $
//   e^*_1 &= kw("wrap")(lambda \_. apply(perform(effcheck), tuple(k, tuple(e^*_5, e^*_6)))) \
//   &= apply(handler(heffcheck, m: d), (lambda \_. apply(perform(effcheck), tuple(k, tuple(e^*_5, e^*_6))))) \
//   &estep1 handle(heffcheck, (apply(perform(effcheck), tuple(k, tuple(e^*_5, e^*_6)))), m: d) = e^*_2
//   $

//   $e ~ apply(perform(effcheck), tuple(k, tuple(e^*_5, e^*_6)))$ by @compiler-is-relation

//   By definition $treq(e,e^*_2)$.

// - Case #prooftree(rule(
//         $x,f in.not "dom"(Gamma)$,
//         $compile(type(dot,e_3,tau_2), e_4, m: d)$,
//         $compile(type(dot\,x:tau_1\,f:tau_1->tau_2,mon(k,l,j,kappa_2,apply(f,x)),tau_2), e_5, m: d)$,
//         $compile(type(dot\,x:tau_1,mon(l,k,j,kappa_1,x),tau_1),e_6, m: d)$,
//         $e_7 = e_5[x:=e_6]$,
//         $compile(type(Gamma,mon(k,l,j,kappa_1->kappa_2,e_3),tau_1 -> tau_2),apply((lambda f: tau_1 -> tau_2. lambda x: tau_1. e_7),e_4), m: d)$,
//       ))

//   $
//   e^*_1 &= apply(kw("wrap"),(lambda \_. apply((lambda f. lambda x. e^*_7),e^*_4))) \
//   &= apply(handler(heffcheck, m: d), (lambda \_. apply((lambda f. lambda x. e^*_7),e^*_4))) \
//   &estep1 handle(heffcheck, apply((lambda f. lambda x. e^*_7),e^*_4), m: d) = e^*_2
//   $

//   $e ~ apply((lambda f. lambda x. e^*_7),e^*_4)$ by @compiler-is-relation.

//   $treq(e,e^*_2)$ by definition.

]

#lemma()[
  If $e cstep1 r$ and $treq(e,e')$ then $e' estep1 rel(r)$.
] <compiler-full-simulation>

#proof[
  By breaking down the $cstep1$, and induction on it.

  - Case $v cstep1 v$

    #derivation((
      ($e' = rel(r)$, [Definition of $treq(e,e')$]),
      ($e' estep1 rel(r)$, "Reflexivity"),
    ))

  - Case $blame(k,j) cstep1 blame(k,j)$

    #derivation((
      ($r = blame(k,j)$, "Case assumption"),
      ($rel(r) = eblame(j)$, "Relation"),
      ($e' = eblame(j) = rel(r)$, [Definition of $treq(e,e')$]),
      ($e' estep1 rel(r)$, "Reflexivity"),
    ))

  - Case $e cstep e_1$ and $e_1 cstep1 r$

    #derivation((
      ($e' estep1 e'_1$, [@compiler-simulation]),
      ($treq(e_1,e'_1)$, [@compiler-simulation]),
      ($e'_1 estep1 rel(r)$, "I.H."),
      ($e' estep1 rel(r)$, "Chaining steps"),
    ))
]


#lemma()[
  If $e_1 cstep e_2$ and $treq(e_1,e'_1)$ then there exists $e'_2$ such that $e'_1 estep1 e'_2$ and $treq(e_2,e'_2)$.
] <compiler-simulation>

#proof(of: <compiler-simulation>)[
By case analysis on $e_1 cstep e_2$ with respect to $treq(e_1,e'_1)$.

- Case $E[blame(k,j)] cstep blame(k,j)$

  #derivation((
    ($E = E^+[E^*]$, [@compiler-context-breakdown]),
  ))

  - Case $E^+ = square.stroked$

    #derivation((
      ($E^*[blame(k,j)] ~ rel(E)^*[eblame(k)]$, [@compiler-relation-context-decomposition]),
      ($rel(E)^*[eblame(k)] estep eblame(k)$, []),
      ($blame(k,j) ~ eblame(k)$, [Definition]),
      ($treq(blame(k,j), eblame(k))$, [EQ Definition]),
      ($e'_2 = eblame(k)$, [Choose]),
    ))

  - Case $E^+ = E^+_1[E^*_1[check(k_1,j_1,square.stroked,v_1)]]$

    #derivation((
      ($E[blame(k,j)] = E^+_1[E^*_1[check(k_1,j_1,blame(k,j),v_1)]]$,[]),
      ($blame(k,j) ~ eblame(k)$, [Definition]),
      ($e_1 ~ rel(E)^+_1[ife(eblame(k), apply((lambda x. handle(heffcheck,rel(E)^*_1[x], m: d)),rel(v)), eblame(k_1))]$,[]),
      ($e'_1 estep eblame(k)$,[]),
      ($treq(blame(k,j), eblame(k))$, [EQ Definition]),
      ($e'_2 = eblame(k)$, [Choose]),
    ))


- Case $E[e_3] cstep E[e_4]$ where $e_3 cstepx e_4$

  Overview of proof strategy: breaking down $E=E^+[E^*]$ using @compiler-context-breakdown and case on $E^+$, then try to match $treq(e_1,e'_1)$ cases. $"EQ"$ case 2 holds if and only if $E^+=square.stroked$, and case 3 holds if and only if $E^+ != square.stroked$ (other case) easily observed the form of $e_1$ in $"EQ"$. By step it should arrive at the next state that matches $"EQ"$ predicate cases.

  During the reduction, we likely encounter $handle(heffcheck,rel(E)^*[e], m: d)$. By @compiler-e-star-no-handler, the handler invoked is obviously the current handler.

  - Case $e_3 = mon(k,l,j,flat(e),v) cstepx check(k,j,apply(e,v),v) = e_4$

    Actually need $e != E'[check(k',j',e',v')]$ to obtain $rel(e)$. But the proof goes through without stating this fact because we inverse from EQ predicate. When running, this $e$ is never a check, because we don't evaluate inside flat contract.

    #derivation((
      ($E = E^+[E^*]$, [@compiler-context-breakdown]),
      ($e_1 = E^+[E^*[e_3]]$, "Substitution"),
    ))

    - Case $E^+ = square.stroked$

      #derivation((
        ($E^* ~ rel(E)^*$, [@compiler-relation-context-decomposition]),
        ($e_3 ~ rel(e)_3$, [@compiler-relation-context-decomposition]),
        ($rel(e)_1 = rel(E)^*[rel(e)_3]$, [@compiler-relation-context-decomposition]),
        ($e_1 = E^*[e_3] ~ rel(E)^*[apply(perform(effcheck),tuple(k,tuple(rel(e),rel(v))))]$, "Relation"),
        ($e'_1 = handle(heffcheck,rel(E)^*[apply(perform(effcheck),tuple(k,tuple(rel(e),rel(v))))], m: d)$, [Case 2]),
        ($e'_1 estep1 ife(handle(heffcheck,apply(rel(e),rel(v)), m: d),apply((lambda x. handle(heffcheck,rel(E)^*[x], m: d)),rel(v)),eblame(j))$, []),
        ($e'_2 = ife(handle(heffcheck,apply(rel(e),rel(v)), m: d),apply((lambda x. handle(heffcheck,rel(E)^*[x], m: d)),rel(v)),eblame(j))$, [Choose]),
        ($treq(apply(e,v),handle(heffcheck,apply(rel(e),rel(v)), m: d))$, "Case 2"),
        ($treq(e_2,e'_2)$, "Case 3"),
      ))

    - Case $E^+ = E^+_1[E^*_1[check(k_1,j_1,square.stroked,v_1)]]$

      #derivation((
        ($e_1 = E^+_1[E^*_1[check(k_1,j_1,E^*[e_3],v_1)]]$, []),
        ($e_3 ~ apply(perform(effcheck),tuple(k,tuple(rel(e),rel(v)))) = rel(e)_3$, []),
        ($treq(E^*[e_3],handle(heffcheck,rel(E)^*[rel(e)_3], m: d))$,[Case 2, by shape]),
        ($treq(e_1,rel(E)^+_1[ife(handle(heffcheck,rel(E)^*[rel(e)_3], m: d),apply((lambda x. handle(heffcheck,rel(E)^*_1[x], m: d)),rel(v)_1),eblame(j_1))])$, []),
        ($e'_1 = rel(E)^+_1[ife(handle(heffcheck,rel(E)^*[rel(e)_3], m: d),apply((lambda x. handle(heffcheck,rel(E)^*_1[x], m: d)),rel(v)_1),eblame(j_1))]$, []),
        ([Identified $e'_1$ based on the condition of $"EQ"$ case 3],[]),
        ($e'_1 estep1 rel(E)^+_2[ife(handle(heffcheck,apply(rel(e),rel(v)), m: d),apply((lambda x. handle(heffcheck, rel(E)^*[x], m: d)),rel(v)),eblame(j))]$, []),
        ($e'_2 = rel(E)^+_2[ife(handle(heffcheck,apply(rel(e),rel(v)), m: d),apply((lambda x. handle(heffcheck, rel(E)^*[x], m: d)),rel(v)),eblame(j))]$, [Choose]),
      ))

      where $rel(E)^+_2 = rel(E)^+_1[ife(square.stroked,apply((lambda x. handle(heffcheck,rel(E)^*_1[x], m: d)),rel(v)_1),eblame(j_1))]$

      #derivation((
        ($e_2 = E^+_1[E^*_1[check(k_1,j_1,E^*[check(k,j,apply(e,v),v)],v_1)]]$, []),
        ($treq(E^*[check(k,j,apply(e,v),v)], ife(handle(heffcheck,apply(rel(e),rel(v)), m: d),apply((lambda x. handle(heffcheck, rel(E)^*[x], m: d)),rel(v)),eblame(j)))$, []),
        ($treq(e_2,e'_2)$, "Case 3"),
      ))

      (Case 2 is invalid, because of the shape of $e_2$)

  - Case $e_3 = check(k,j,trueb,v) cstepx v = e_4$

    #derivation((
      ($E = E^+[E^*]$, [@compiler-context-breakdown]),
      ($e_1 = E^+[E^*[e_3]]$, "Substitution"),
    ))

    // By inversion of $treq(e_1,e'_1)$, the check is compiled to an $ife$, whose condition is related to $trueb$. Thus its condition is $trueb$.

    - Case $E^+ = square.stroked$

      Let $e_5 = apply((lambda x. handle(heffcheck,rel(E)^*[x], m: d)),rel(v))$.

      #derivation((
        ($e'_1 = ife(e'_3,e_5,eblame(j))$, [$treq(e_1,e'_1)$, case 3]),
        ($treq(trueb,e'_3)$, [Since $trueb$ is a value]),
        ($e'_3 = trueb$, [Definition of $"EQ"$]),
        ($e'_1 estep1 handle(heffcheck,rel(E)^*[rel(v)], m: d) = e'_2$, []),
        ($e_2 = E^*[v]$, []),
        ($treq(e_2,e'_2)$, "Case 2"),
      ))

    - Case $E^+ = E^+_1[E^*_1[check(k_1,j_1,square.stroked,v_1)]]$

      Let $e_5 = apply((lambda x. handle(heffcheck,rel(E)^*[x], m: d)),rel(v))$ and $e_6 = apply((lambda x. handle(heffcheck,rel(E)^*_1[x], m: d)),rel(v)_1)$.

      #derivation((
        ($e'_1 = rel(E)^+_1[ife(ife(e'_3,e_5,eblame(j)),e_6,eblame(j_1))]$, [$treq(e_1,e'_1)$, case 3]),
        ($treq(trueb,e'_3)$, [Since $trueb$ is a value]),
        ($e'_3 = trueb$, [Definition of $"EQ"$]),
        ($e'_1 estep1 rel(E)^+_1[ife(handle(heffcheck,rel(E)^*[rel(v)], m: d),e_6,eblame(j_1))] = e'_2$, []),
        ($e_2 = E^+_1[E^*_1[check(k_1,j_1,E^*[v],v_1)]]$, []),
        ($treq(E^*[v],handle(heffcheck,rel(E)^*[rel(v)], m: d))$, "Case 2"),
        ($treq(e_2,e'_2)$, "Case 3"),
      ))

      (Case 2 is invalid, because of the shape of $e_2$.)

  - Case $e_3 = check(k,j,falseb,v) cstepx blame(k,j) = e_4$

    #derivation((
      ($E = E^+[E^*]$, [@compiler-context-breakdown]),
      ($e_1 = E^+[E^*[e_3]]$, "Substitution"),
    ))

    - Case $E^+ = square.stroked$

      #derivation((
        ($e_1 = E^*[check(k,j,falseb,v)]$, []),
        ($e'_1 = $, []),
      ))

    - Case $E^+ = E^+_1[E^*_1[check(k_1,j_1,square.stroked,v_1)]]$

      #derivation((
        ($e_1 = E^+[E^*[check(k,j,falseb,v)]]$, []),
        ($e'_1 = rel(E)^+[ife(falseb,apply((lambda x. handle(heffcheck,rel(E)^*[x], m: d)),rel(v)),eblame(j))]$, [$treq(e_1,e'_1)$]),
        ($e'_1 estep1 rel(E)^+[eblame(j)] = e'_2$, "Reduction"),
        ($e_2 = E^+[E^*[blame(k,j)]]$, "Source reduction"),
        ($rel(E)^+[eblame(j)] estep eblame(j)$, rn("Step-E-Error")),
        ($blame(k,j) ~ eblame(j)$, "Relation"),
        ($treq(e_2,e'_2)$, "Definition"),
      ))

  - Case $e_3 = mon(k,l,j,kappa_1 -> kappa_2, v) cstepx guard(v, kappa_1 -> kappa_2, k,l,j) = e_4$

    #derivation((
      ($E = E^+[E^*]$, [@compiler-context-breakdown]),
      ($e_1 = E^+[E^*[e_3]]$, "Substitution"),
    ))

    - Case $E^+ = square.stroked$

      Let $e_5 = lambda f. lambda x. mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x))) = lambda f. lambda x. e_(5a)$

      // By inversion of case 2 of $treq(e_1,e'_1)$, $e_1 ~ rel(e)_1$. Since $e_1 = E^*[e_3]$, @compiler-relation-context-decomposition gives contexts and expressions that we name $rel(E)^*$ and $rel(e)_3$.

      #derivation((
        ($E^* ~ rel(E)^*$, [@compiler-relation-context-decomposition]),
        ($e_3 ~ rel(e)_3$, [@compiler-relation-context-decomposition]),
        ($rel(e)_1 = rel(E)^*[rel(e)_3]$, [@compiler-relation-context-decomposition]),
        ($e_1 = E^*[e_3] ~ rel(E)^*[apply((lambda f. lambda x. rel(e)_(5a)),rel(v))]$, "Relation"),
        ($e'_1 = handle(heffcheck,rel(E)^*[apply((lambda f. lambda x. rel(e)_(5a)),rel(v))], m: d)$, [$treq(e_1,e'_1)$, case 2]),
        ($e'_1 estep1 handle(heffcheck,rel(E)^*[lambda x. rel(e)_(5a)[f:=rel(v)]], m: d) = e'_2$, "Reduction"),
        ($e_2 = E^*[guard(v,kappa_1 -> kappa_2,k,l,j)]$, []),
        ($e_6 = lambda x. mon(k,l,j,kappa_2,apply(v,mon(l,k,j,kappa_1,x)))$, [Let]),
        ($e_6 = e_5[f:=v]$, [Substitution]),
        ($rel(e)_6 = rel(e)_5[f:=rel(v)]$, [@compiler-relation-subst]),
        ($guard(v,kappa_1 -> kappa_2,k,l,j) ~ rel(e)_6 = rel(e)_5[f:=rel(v)]$, [Definition]),
        ($E^*[guard(v,kappa_1 -> kappa_2,k,l,j)] ~ rel(E)^*[rel(e)_5[f:=rel(v)]]$, [@compiler-relation-is-closed]),
        ($treq(e_2,e'_2)$, "Case 2"),
      ))

    - Case $E^+ = E^+_1[E^*_1[check(k_1,j_1,square.stroked,v_1)]]$

      Let $e_5 = lambda f. lambda x. e_(5a)$, where $e_(5a) = mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x)))$.

      Let $rel(E)^+_2 = rel(E)^+_1[ife(square.stroked,apply((lambda x. handle(heffcheck,rel(E)^*_1[x], m: d)),rel(v)_1),eblame(j_1))]$

      #derivation((
        ($e'_1 = rel(E)^+_2[handle(heffcheck,rel(E)^*[apply(rel(e)_5,rel(v))], m: d)]$, []),
        ($e'_1 estep1 rel(E)^+_2[handle(heffcheck,rel(E)^*[lambda x. rel(e)_(5a)[f:=rel(v)]], m: d)] = e'_2$, []),
        ($e_2 = E^+_1[E^*_1[check(k_1,j_1,E^*[guard(v,kappa_1 -> kappa_2,k,l,j)],v_1)]]$, []),
        ($e_6 = lambda x. mon(k,l,j,kappa_2,apply(v,mon(l,k,j,kappa_1,x)))$, [Let]),
        ($e_6 = e_(5a)[f:=v]$, [Substitution]),
        ($rel(e)_6 = rel(e)_(5a)[f:=rel(v)]$, [@compiler-relation-subst]),
        ($guard(v,kappa_1 -> kappa_2,k,l,j) ~ rel(e)_6 = rel(e)_(5a)[f:=rel(v)]$, [Definition]),
        ($E^*[guard(v,kappa_1 -> kappa_2,k,l,j)] ~ rel(E)^*[rel(e)_(5a)[f:=rel(v)]]$, [@compiler-relation-is-closed]),
        ($treq(E^*[guard(v,kappa_1 -> kappa_2,k,l,j)], handle(heffcheck,rel(E)^*[rel(e)_(5a)[f:=rel(v)]], m: d))$, [Case 1]),
        ($treq(e_2,e'_2)$, [Case 3]),
      ))

  - Case $e_3 = apply(guard(v_1,kappa_1 -> kappa_2,k,l,j),v_2) cstepx mon(k,l,j,kappa_2,apply(v_1, mon(l,k,j,kappa_1,v_2))) = e_4$

    #derivation((
      ($E = E^+[E^*]$, [@compiler-context-breakdown]),
      ($e_1 = E^+[E^*[e_3]]$, "Substitution"),
    ))

    - Case $E^+ = square.stroked$

      Let $e_5 = lambda f. lambda x. e_(5a)$, where $e_(5a) = mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x)))$.

      #derivation((
        ($E^* ~ rel(E)^*$, [@compiler-relation-context-decomposition]),
        ($e_3 ~ rel(e)_3$, [@compiler-relation-context-decomposition]),
        ($rel(e)_1 = rel(E)^*[rel(e)_3]$, [@compiler-relation-context-decomposition]),
        ($rel(e)_3 = apply(rel(e)_5, rel(v)_2)$, [Relation]),
        ($e'_1 = handle(heffcheck, rel(E)^*[rel(e)_3], m: d)$, [$treq(e_1,e'_1)$, case 2]),
        ($e'_1 estep1 e'_1 = e'_2$, [Reflexivity]),
        ($rel(e)_4 = apply(rel(e)_5, rel(v)_2)$, [Relation]),
        ($E^*[e_4] ~ rel(E)^*[rel(e)_4]$,[@compiler-relation-is-closed]),
        ($treq(e_2,e'_2)$, "Case 2"),
      ))

    - Case $E^+ = E^+_1[E^*_1[check(k_1,j_1,square.stroked,v_1)]]$

      Same as the case $E^+ = square.stroked$, inside $rel(E)^+$, by case 3.

  - Case $e_3 = mon(k,l,j,dep(kappa_1, lambda y. kappa_2), v) cstepx guard(v, dep(kappa_1, lambda y. kappa_2), k,l,j) = e_4$

    Similar to its functional variant.

  - Case $e_3 = apply(guard(v_1,dep(kappa_1, lambda y. kappa_2),k,l,j),v_2) cstepx mon(k,l,j, kappa_3, apply(v_1, mon(l,k,j,kappa_1,v_2))) = e_4$ where $kappa_3 = kappa_2[y:=mon(l,j,j,kappa_1,v_2)]$

    Similar to its functional variant.

]

#lemma(title: [$rel(E)^*$ does not have a handler])[

If $E^* ~ rel(E)^*$, then $effcheck in.not bop(rel(E)^*)$.
] <compiler-e-star-no-handler>

#proof[

By induction on the structure of $E^* ~ rel(E)^*$. Trivial, the related context has no handler.
]
