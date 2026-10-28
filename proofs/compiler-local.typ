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

// Before we define relations that will be used in the simulation proof below. We define:

  // - Context $E^*$ is any context without $check(k,j,e,v)$ in $langc$.
  // - Context $E^+  =& square.stroked | E^+[E^*[check(k,j,square.stroked,v)]]$ // | apply(E^+,e) | apply(v,E^+) | mon(k,l,j,kappa,E^+)$


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
    [$handle(heffcheck, (apply(perform(effcheck), tuple(k,tuple(rel(e)_1,rel(e)_2)))), m: s)$],

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
    $R_(E) subset.eq langc E times lange E$
  ]

  Abuse of notation: If $(E,E') in R_(E)$, we write $E attach(~, br: R_(E)) E'$ or $E ~ E'$. We write $rel(E)$ for any expression $rel(E)$ satisfying $E ~ rel(E)$.

  #v(1em)
  #grid(
    columns: (1fr, auto, 1fr),
    column-gutter: 1em,
    row-gutter: 1.2em,
    align: (right, left, left),

    [$square.stroked$],
    [$tilde$],
    [$square.stroked$],

    [$apply(E,e)$],
    [$tilde$],
    [$apply(rel(E),rel(e))$],

    [$apply(v,E)$],
    [$tilde$],
    [$apply(rel(v),rel(E))$],

    [$mon(k,l,j,flat(e),E)$],
    [$tilde$],
    [$handle(heffcheck, (apply(perform(effcheck),tuple(k,tuple(rel(e),rel(E))))), m: s)$],

    [$mon(k,l,j,kappa_1 -> kappa_2,E)$],
    [$tilde$],
    [$apply(rel(e)_1,rel(E))$],
    [],[],grid.cell(align:left,colspan:1)[$e_1=lambda f. lambda x. mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x)))$],

    [$mon(k,l,j,dep(kappa_1, lambda y. kappa_2),E)$],
    [$tilde$],
    [$apply(rel(e)_1,rel(E))$],
    [],[],grid.cell(align:left,colspan:1)[$e_1=lambda f. lambda x. mon(k,l,j,kappa_3,apply(f,mon(l,k,j,kappa_1,x)))$],
    [],[],grid.cell(align:left,colspan:1)[$kappa_3=kappa_2[y:=mon(l,j,j,kappa_1,x)]$],

    [$E[check(k,j,E',v)]$],
    [$tilde$],
    [$ife(rel(E)',apply((lambda x. rel(E)[x]), rel(v)),eblame(k))$],
  )

Analysis for check context relation:

  Let $E = check(k_1,j_2,check(k_2,j_2,check(k_3,j_3,square.stroked,v_3),v_2),v_1)$ the context for analysis.

  $E_3 = check(k_1,j_2,check(k_2,j_2,square.stroked,v_2),v_1); E'_3 = square.stroked$

  $E_2 = check(k_1,j_2,square.stroked,v_1); E'_2 = square.stroked$

  $E_1 = square.stroked; E'_1 = square.stroked$

  $rel(E) = ife(square.stroked,apply((lambda x. rel(E)_3[x]), rel(v)_3),eblame(k_3))$

  $rel(E)_3 = ife(square.stroked,apply((lambda y. rel(E)_2[x]), rel(v)_2),eblame(k_2))$

  $rel(E)_2 = ife(square.stroked,apply((lambda z. rel(E)_1[x]), rel(v)_1),eblame(k_1))$

  $rel(E)_1 = square.stroked$

  $\ rel(E) = ife(square.stroked, \ med apply((lambda x. ife(x,\ med quad apply((lambda y. ife(y,\ quad quad apply((lambda z. rel(E)_1[x]), rel(v)_1),eblame(k_1))), rel(v)_2),eblame(k_2))), rel(v)_3),eblame(k_3))$

  So the expression on the target language is reversed going from the most nested check to the outside checks. Because when the handler is invoked, it pushes the whole current context (on going checks) into the continuation. Therefore the relation is correct. One note: $E[check(k,j,E',v)]$ must be uniquely decomposed to always get the last check up until current redex, as observed if we decompose $E,E'$ wrongly, it might give into a different relation. Maybe reusing the relation $E^+$ defined in other compilers to always get the most nested check?

  This relation maybe too loose, it contains pairs that should not have. Since the simulation uses the relation, we may need to bridge it closer.
]

#lemma(title: "Relation is closed")[

If $e ~ e'$ and $E ~ E'$ then $E[e] ~ E'[e']$

Assume: $e != check(k_1,j_1,e_1,v_1)$ by restrictions on $R_e$.
] <compiler-local-relation-plug>

#proof[

By induction on the structure of $E ~ E'$.

- Case $mon(k,l,j,flat(e_1),E_1) ~ handle(heffcheck,(apply(perform(effcheck),tuple(k,tuple(rel(e)_1,rel(E)_1)))), m: s)$

  #derivation((
    ($E_1[e] ~ rel(E)_1[e']$, [I.H.]),
    ($mon(k,l,j,flat(e_1),E_1[e]) ~ handle(heffcheck,(apply(perform(effcheck),tuple(k,tuple(rel(e)_1,rel(E)_1[e'])))), m: s)$, []),
    ($mon(k,l,j,flat(e_1),E_1)[e] ~ (handle(heffcheck,(apply(perform(effcheck),tuple(k,tuple(rel(e)_1,rel(E)_1)))), m: s))[e']$, []),
  ))

- Case $mon(k,l,j,kappa_1 -> kappa_2,E_1) ~ apply(rel(e)_1,rel(E)_1)$ and $e_1 = (lambda f. lambda x. mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x))))$

  #derivation((
    ($E_1[e] ~ rel(E)_1[e']$, [I.H.]),
    ($mon(k,l,j,kappa_1 -> kappa_2,E_1[e]) ~ apply(rel(e)_1,rel(E)_1[e'])$, []),
    ($mon(k,l,j,kappa_1 -> kappa_2,E_1)[e] ~ (apply(rel(e)_1,rel(E)_1))[e']$, []),
  ))

- Case $mon(k,l,j,dep(kappa_1, lambda y. kappa_2),E_1) ~ apply(rel(e)_1,rel(E)_1)$ and $e_1 = (lambda f. lambda x. mon(k,l,j,kappa_3,apply(f,mon(l,k,j,kappa_1,x))))$ and $kappa_3 = kappa_2[y:=mon(l,j,j,kappa_1,x)]$

  #derivation((
    ($E_1[e] ~ rel(E)_1[e']$, [I.H.]),
    ($mon(k,l,j,dep(kappa_1, lambda y. kappa_2),E_1[e]) ~ apply(rel(e)_1,rel(E)_1[e'])$, []),
    ($mon(k,l,j,dep(kappa_1, lambda y. kappa_2),E_1)[e] ~ (apply(rel(e)_1,rel(E)_1))[e']$, []),
  ))

- Case $E'[check(k,l,E_1,v_1)] ~ ife(rel(E)_1,apply((lambda x. rel(E)'[x]), rel(v)_1),eblame(k))$

  #derivation((
    ($E_1[e] ~ rel(E)_1[e']$, [I.H.]),
    ($E'[check(k,l,E_1[e],v_1)] ~ ife(rel(E)_1[e'],apply((lambda x. rel(E)'[x]), rel(v)_1),eblame(k))$, []),
    ($E'[check(k,l,E_1,v_1)][e] ~ (ife(rel(E)_1,apply((lambda x. rel(E)'[x]), rel(v)_1),eblame(k)))[e']$, []),
  ))
]

#lemma(title: "Relation substitution")[

If $e ~ e'$ and $v ~ v'$ then $e[x:=v] ~ e'[x:=v']$
] <compiler-local-relation-substitution>

#proof[

By induction on the derivation of $e ~ e'$. For this compiler, there is a single case that has their relation different from Deep/Shallow compilers.

It is also assumed that $e !=check(k',j',e',v')$ because it does not belongs in $R_e$.

// - Case $x ~ x$

//   #derivation((
//     ($x[x:=v] = v$, [Replacement]),
//     ($x[x:=v'] = v'$, [Replacement]),
//     ($v ~ v'$, [Given]),
//     ($x[x:=v] ~ x[x:=v']$, []),
//   ))

// - Case $z ~ z$, where $z != x$

//   #derivation((
//     ($z[x:=v] = z$, [Replacement]),
//     ($z[x:=v'] = z$, [Replacement]),
//     ($z[x:=v] ~ z[x:=v']$, [Definition]),
//   ))

// - Case $lambda z.e_1 ~ lambda z.e'_1$

//   #derivation((
//     ($e_1[x:=v] ~ e'_1[x:=v']$, [I.H.]),
//     ($lambda z.e_1[x:=v] ~ lambda z.e'_1[x:=v']$, [Definition]),
//     ($(lambda z.e_1)[x:=v] ~ (lambda z.e'_1)[x:=v']$, [Replacement]),
//   ))

// - Case $apply(e_1,e_2) ~ apply(e'_1,e'_2)$

//   #derivation((
//     ($e_1[x:=v] ~ e'_1[x:=v']$, [I.H.]),
//     ($e_2[x:=v] ~ e'_2[x:=v']$, [I.H.]),
//     ($apply(e_1,e_2)[x:=v] = apply(e_1[x:=v],e_2[x:=v])$, [Replacement]),
//     ($apply(e'_1,e'_2)[x:=v'] = apply(e'_1[x:=v'],e'_2[x:=v'])$, [Replacement]),
//     ($apply(e_1,e_2)[x:=v] ~ apply(e'_1,e'_2)[x:=v']$, [Definition]),
//   ))

- Case $mon(k,l,j,flat(e_1),e_2) ~ handle(heffcheck,apply(perform(effcheck),tuple(k,tuple(rel(e)_1,rel(e)_2))),m:s)$

  #derivation((
    ($e_1[x:=v] ~ rel(e)_1[x:=v']$, [I.H.]),
    ($e_2[x:=v] ~ rel(e)_2[x:=v']$, [I.H.]),
    ($mon(k,l,j,flat(e_1),e_2)[x:=v] ~ handle(heffcheck,apply(perform(effcheck),tuple(k,tuple(rel(e)_1,rel(e)_2))),m:s)[x:=v']$, [Def.]),
  ))

// - Case $mon(k,l,j,kappa_1 -> kappa_2,e_1) ~ apply(rel(e)_2,rel(e)_1)$, with $e_2 = lambda f. lambda y. mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,y)))$

//   #derivation((
//     ($e_1 ~ rel(e)_1$, [Given]),
//     ($e_2 ~ rel(e)_2$, [Given]),
//     ($e_1[x:=v] ~ rel(e)_1[x:=v']$, [I.H.]),
//     ($e_2[x:=v] ~ rel(e)_2[x:=v']$, [I.H.]),
//     ($mon(k,l,j,kappa_1 -> kappa_2,e_1)[x:=v] = mon(k,l,j,kappa_1[x:=v] -> kappa_2[x:=v],e_1[x:=v]) $, []),
//     ($e_2[x:=v] =  lambda f. lambda y. mon(k,l,j,kappa_2[x:=v],apply(f,mon(l,k,j,kappa_1[x:=v],y)))$, []),
//     ($mon(k,l,j,kappa_1 -> kappa_2,e_1)[x:=v] ~ apply(rel(e)_2[x:=v'],rel(e)_1[x:=v'])$, [Relation]),
//     ($mon(k,l,j,kappa_1 -> kappa_2,e_1)[x:=v] ~ (apply(rel(e)_2,rel(e)_1))[x:=v']$, []),
//   ))

//   Choose variables, $f,y != x$ and $f,y in.not "fv"(v,v')$ by alpha-renaming.

// - Case $mon(k,l,j,dep(kappa_1, lambda y. kappa_2),rel(e)_1) ~ apply(rel(e)_2,rel(e)_1)$, with $e_2 = lambda f. lambda z. mon(k,l,j,kappa_3,apply(f,mon(l,k,j,kappa_1,z)))$ and $kappa_3=kappa_2[y:=mon(l,j,j,kappa_1,z)]$ and $y != x$

//   #derivation((
//     ($e_1 ~ rel(e)_1$, [Given]),
//     ($e_2 ~ rel(e)_2$, [Given]),
//     ($e_1[x:=v] ~ rel(e)_1[x:=v']$, [I.H.]),
//     ($e_2[x:=v] ~ rel(e)_2[x:=v']$, [I.H.]),
//     ($mon(k,l,j,dep(kappa_1, lambda y. kappa_2),e_1)[x:=v] = \ quad mon(k,l,j,dep(kappa_1[x:=v], lambda y. kappa_2[x:=v]),e_1[x:=v]) $, [Substitution]),
//     ($e_2[x:=v] =  lambda f. lambda z. mon(k,l,j,kappa_3[x:=v],apply(f,mon(l,k,j,kappa_1[x:=v],z)))$, []),
//     ($kappa_3[x:=v] = (kappa_2[y:=mon(l,j,j,kappa_1,z)])[x:=v]$,[]),
//     ($kappa_3[x:=v] = (kappa_2[x:=v])[y:=mon(l,j,j,kappa_1[x:=v],z)]$,[Substitution?]),
//     ($mon(k,l,j,dep(kappa_1, lambda y. kappa_2),e_1)[x:=v] ~ apply(rel(e)_2[x:=v'],rel(e)_1[x:=v'])$, [Relation]),
//     ($mon(k,l,j,dep(kappa_1, lambda y. kappa_2),e_1)[x:=v] ~ (apply(rel(e)_2,rel(e)_1))[x:=v']$, [Definition]),
//   ))

//   Choose variables, $f,z != x$ and $f,y,z in.not "fv"(v,v')$ by alpha-renaming.

// - Case $mon(k,l,j,dep(kappa_1, lambda x. kappa_2),rel(e)_1) ~ apply(rel(e)_2,rel(e)_1)$, with $e_2 = lambda f. lambda z. mon(k,l,j,kappa_3,apply(f,mon(l,k,j,kappa_1,z)))$ and $kappa_3=kappa_2[x:=mon(l,j,j,kappa_1,z)]$

//   // Observe that $x in.not "fv"(kappa_3)$ because of replacement into $kappa_2$. Follows immediately with the above case.

//   #derivation((
//     ($e_1 ~ rel(e)_1$, [Given]),
//     ($e_2 ~ rel(e)_2$, [Given]),
//     ($e_1[x:=v] ~ rel(e)_1[x:=v']$, [I.H.]),
//     ($e_2[x:=v] ~ rel(e)_2[x:=v']$, [I.H.]),
//     ($mon(k,l,j,dep(kappa_1, lambda x. kappa_2),e_1)[x:=v] = \ quad mon(k,l,j,dep(kappa_1[x:=v], lambda x. kappa_2),e_1[x:=v]) $, [Substitution]),
//     ($e_2[x:=v] =  lambda f. lambda z. mon(k,l,j,kappa_3[x:=v],apply(f,mon(l,k,j,kappa_1[x:=v],y)))$, []),
//     ($kappa_3[x:=v] = (kappa_2[x:=mon(l,j,j,kappa_1,z)])[x:=v]$,[]),
//     ($kappa_3[x:=v] = (kappa_2[x:=mon(l,j,j,kappa_1[x:=v],z)])$,[]),
//     ($mon(k,l,j,dep(kappa_1, lambda x. kappa_2),e_1)[x:=v] ~ apply(rel(e)_2[x:=v'],rel(e)_1[x:=v'])$, [Relation]),
//     ($mon(k,l,j,dep(kappa_1, lambda x. kappa_2),e_1)[x:=v] ~ (apply(rel(e)_2,rel(e)_1))[x:=v']$, [Definition]),
//   ))

//   Choose variables, $f,z != x$ and $f,y,z in.not "fv"(v,v')$ by alpha-renaming.

// - Case $guard(v_1,kappa_1 -> kappa_2,k,l,j) ~ rel(e)_1$, with $e_1=lambda y. mon(k,l,j,kappa_2,apply(v_1,mon(l,k,j,kappa_1,y)))$

//   #derivation((
//     ($e_1 ~ rel(e)_1$, [Given]),
//     ($e_1[x:=v] ~ rel(e)_1[x:=v']$, [I.H.]),
//     ($e_1[x:=v]=lambda y. mon(k,l,j,kappa_2[x:=v],apply(v_1[x:=v],mon(l,k,j,kappa_1[x:=v],y)))$, []),
//     ($guard(v_1,kappa_1 -> kappa_2,k,l,j)[x:=v] = guard(v_1[x:=v],kappa_1[x:=v] -> kappa_2[x:=v],k,l,j)$, []),
//     ($guard(v_1,kappa_1 -> kappa_2,k,l,j)[x:=v] ~ rel(e)_1[x:=v']$, [Relation]),
//   ))

//   Choose variables, $y != x$ and $y in.not "fv"(v,v')$ by alpha-renaming.

// - Case $guard(v,dep(kappa_1, lambda y. kappa_2),k,l,j) ~ rel(e)_1$, with $e_1=lambda z. mon(k,l,j,kappa_3,apply(v,mon(l,k,j,kappa_1,z)))$ and $kappa_3=kappa_2[y:=mon(l,j,j,kappa_1,z)]$

//   #derivation((
//     ($e_1 ~ rel(e)_1$, [Given]),
//     ($e_1[x:=v] ~ rel(e)_1[x:=v']$, [I.H.]),
//     ($e_1[x:=v]=lambda y. mon(k,l,j,kappa_3[x:=v],apply(v_1[x:=v],mon(l,k,j,kappa_1[x:=v],x)))$, []),
//     ($kappa_3[x:=v] = kappa_2[y:=mon(l,j,j,kappa_1,z)][x:=v]$, []),
//     ($kappa_3[x:=v] = (kappa_2[x:=v])[y:=mon(l,j,j,kappa_1[x:=v],z)]$, [Substitution?]),
//     ($guard(v_1,dep(kappa_1, lambda y. kappa_2),k,l,j)[x:=v] = \ quad guard(v_1[x:=v],dep(kappa_1[x:=v], lambda y. kappa_2[x:=v]),k,l,j)$, []),
//     ($guard(v_1,dep(kappa_1, lambda y. kappa_2),k,l,j)[x:=v] ~ rel(e)[x:=v']$, [Relation]),
//   ))

//   Choose variables, $z != x$ and $y,z in.not "fv"(v,v')$ by alpha-renaming.

// - Case $guard(v,dep(kappa_1, lambda x. kappa_2),k,l,j) ~ rel(e)_1$, with $e_1=lambda z. mon(k,l,j,kappa_3,apply(v,mon(l,k,j,kappa_1,x)))$ and $kappa_3=kappa_2[x:=mon(l,j,j,kappa_1,x)]$

//   #derivation((
//     ($e_1 ~ rel(e)_1$, [Given]),
//     ($e_1[x:=v] ~ rel(e)_1[x:=v']$, [I.H.]),
//     ($e_1[x:=v]=lambda y. mon(k,l,j,kappa_3[x:=v],apply(v_1[x:=v],mon(l,k,j,kappa_1[x:=v],x)))$, []),
//     ($kappa_3[x:=v] = kappa_2[x:=mon(l,j,j,kappa_1,z)][x:=v]$, []),
//     ($kappa_3[x:=v] = kappa_2[x:=mon(l,j,j,kappa_1[x:=v],z)]$, []),
//     ($guard(v_1,dep(kappa_1, lambda x. kappa_2),k,l,j)[x:=v] = \ quad guard(v_1[x:=v],dep(kappa_1[x:=v], lambda x. kappa_2),k,l,j)$, []),
//     ($guard(v_1,dep(kappa_1, lambda x. kappa_2),k,l,j)[x:=v] ~ rel(e)[x:=v']$, [Relation]),
//   ))

//   Choose variables, $z != x$ and $z in.not "fv"(v,v')$ by alpha-renaming.

// - Other cases follows similarly.

- Other cases follow @compiler-relation-subst because their relations ($R_e$) are the same.
]

#lemma(title: "Find Relation Context")[

If $e_1 = E[e_2]$ and $e_2 != check(k,j,e_(2a),v)$ and $e_1 ~ e'_1$ then there exists $rel(E),rel(e)_2$, such that $e'_1 = rel(E)[rel(e)_2]$

// - If $e_2 = check(k,j,e_3,v_3)$ there exists $rel(E),rel(e)_3,rel(v)_3$, such that $e'_1 = ife(rel(e)_3,apply((lambda x. handle(heffcheck,rel(E)[x], m: s)), rel(v)_3),eblame(k))$
] <compiler-local-relation-find-E>

#proof[

By induction on $E$

- Case $mon(k,l,j,flat(e),E_1)$

  #derivation((
    ($e_1 = mon(k,l,j,flat(e),E_1[e_2]) = mon(k,l,j,flat(e),e_3)$, []),
    ($e_1 ~ handle(heffcheck,(apply(perform(effcheck),tuple(k,tuple(rel(e),rel(e)_3)))), m: s)$, []),
    ($rel(e)_3 = rel(E)_1[rel(e)_2]$, [I.H. by $e_3 = E_1[e_2] ~ rel(e)_3$]),
    ($e'_1 = handle(heffcheck,(apply(perform(effcheck),tuple(k,tuple(rel(e),rel(E)_1)))), m: s)[rel(e)_2]$, []),
    ($rel(E) = handle(heffcheck,(apply(perform(effcheck),tuple(k,tuple(rel(e),rel(E)_1)))), m: s)$, [Choose]),
  ))

- Case $mon(k,l,j,kappa_1 -> kappa_2,E_1)$

  #derivation((
    ($e_1 = mon(k,l,j,kappa_1 -> kappa_2,E_1[e_2]) = mon(k,l,j,kappa_1 -> kappa_2,e_3)$, []),
    ($e_1 ~ apply((lambda f. lambda x. mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x)))), rel(e)_3)$, []),
    ($rel(e)_3 = rel(E)_1[rel(e)_2]$, [I.H. by $e_3 = E_1[e_2] ~ rel(e)_3$]),
    ($e'_1 = apply((lambda f. lambda x. mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x)))), rel(E)_1[rel(e)_2])$, []),
    ($rel(e) = apply((lambda f. lambda x. mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x)))), rel(E)_1)$, [Choose]),
    ([Where $f,y != x$ and $f,y in.not "fv"(e_2)$ by alpha-renaming],[]),
  ))

- Case $mon(k,l,j,dep(kappa_1, lambda x. kappa_2),E_1)$

  #derivation((
    ($e_1 = mon(k,l,j,dep(kappa_1, lambda x. kappa_2),E_1[e_2]) \ quad = mon(k,l,j,dep(kappa_1, lambda x. kappa_2),e_3)$, []),
    ($e_1 ~ apply((lambda f. lambda y. mon(k,l,j,kappa_3,apply(f,mon(l,k,j,kappa_1,y)))), rel(e)_3)$, []),
    ($quad kappa_3 = kappa_2[y:=mon(l,j,j,kappa_1,x)]$, []),
    ($rel(e)_3 = rel(E)_1[rel(e)_2]$, [I.H. by $e_3 = E_1[e_2] ~ rel(e)_3$]),
    ($e'_1 ~ apply((lambda f. lambda y. mon(k,l,j,kappa_3,apply(f,mon(l,k,j,kappa_1,y)))), rel(E)_1[rel(e)_2])$, []),
    ($rel(E) = apply((lambda f. lambda y. mon(k,l,j,kappa_3,apply(f,mon(l,k,j,kappa_1,y)))), rel(E)_1)$, [Choose]),
    ([Where $f,y != x$ and $f,y in.not "fv"(e_2)$ by alpha-renaming],[]),
  ))

- Similarly for other cases.
]

#lemma(title: "Find Relation Context for check")[

If $e_1 = E[check(k,j,e_2,v)]$ and $e_2$ does not contain check. and $e_1 ~ e'_1$ then there exists $rel(E),rel(e)_2,rel(v)$, such that $e'_1 = ife(rel(e)_2,apply((lambda x. rel(E)[x]), rel(v)),eblame(k))$

Needs $e_2$ without checks along its execution path. Otherwise, the relation is wrong.
] <compiler-local-relation-find-E-check>

#proof[

By induction on the structure of $E$.

- Case $square.stroked$

  #derivation((
    ($e_1 = check(k,j,e_2,v)$, []),
    ($e_2 = E_1[e_3]$, []),
  ))

  - Case $e_3 != check(k_0,j_0,e_4,v_0)$

    #derivation((
      ($rel(e)_2 = rel(E)_1[rel(e)_3]$, [@compiler-local-relation-find-E]),
      ($e_1 ~ ife(rel(e)_2,apply((lambda x. x), rel(v)),eblame(k))$, []),
      ($rel(E) = square.stroked$, [Choose]),
    ))

  - Case $e_3 = check(k_0,j_0,e_4,v_0)$

    #derivation((
      ($rel(e)_2 = ife(rel(e)_4,apply((lambda x. rel(E)_1[x]), rel(v)_0),eblame(k))$, [I.H.]),
      ($e_1 ~ ife(rel(e)_2,apply((lambda x. x), rel(v)),eblame(k))$, []),
      ($rel(E) = square.stroked$, [Choose]),
    ))

- Case $mon(k_0,l_0,j_0,flat(e_0),E_0)$

  #derivation((
    ($e_1 = mon(k_0,l_0,j_0,flat(e_0),E_0[check(k,j,e_2,v)]) \ quad = mon(k_0,l_0,j_0,flat(e_0),E_0)[check(k,j,e_2,v)] \ quad = E_1[check(k,j,e_2,v)]$, []),
    ($e_1 ~ ife(rel(e)_2,apply((lambda x. rel(E)_1[x]), rel(v)),eblame(k))$, [I.H.]),
    ($rel(E) = rel(E)_1$, [Choose]),
  ))

- Case $check(k_0,j_0,E_0,v_0)$

  #derivation((
    ($e_1 = check(k_0,j_0,E_0[check(k,j,e_2,v)],v_0)$, []),
  ))
]

#lemma(title: "Compiler is Relation")[

If $compile(type(Gamma,e,tau),e', m: l)$ then $e ~ e'$
] <compiler-local-compiler-is-relation>

#proof[]

== Correctness Theorem

#theorem()[

If $e cstep1 b$ and $compile(type(dot,e,tau),e', m: l)$ then $e' estep1 b$
]

#proof[
  #derivation((
    ($e ~ e'$, [@compiler-local-compiler-is-relation]),
    ($e' estep1 rel(b) = b$, [@compiler-local-multistep-simulation]),
  ))
]


#lemma()[

If $e ~ e'$ and $e cstep1 r$ then $e' estep1 rel(r)$.

Where $r = v | blame(k,j)$ and $rel(r) = rel(v) | eblame(k)$
] <compiler-local-multistep-simulation>

#proof[

By induction on the structure of $e cstep1 r$

- Case $r cstep1 r$

  #derivation((
    ($e ~ e'$, [Given]),
    ($e' = rel(r)$, [Inversion]),
    ($e' estep1 rel(r)$, [Reflexivity]),
  ))

- Case $e cstep e_1$ and $e_1 cstep1 r$

  #derivation((
    ($e' estep1 e'_1$, [@compiler-local-step-simulation]),
    ($e_1 ~ e'_1$, [@compiler-local-step-simulation]),
    ($e'_1 estep1 rel(r)$, [I.H.]),
    ($e' estep1 rel(r)$,[Step]),
  ))
]

#lemma()[

If $e_1 ~ e'_1$ and $e_1 cstep e_2$ then $e'_1 estep1 e'_2$ and $e_2 ~ e'_2$
] <compiler-local-step-simulation>

#proof[

By case analysis on $e_1 cstep e_2$.

- $E[blame(k,j)] cstep blame(k,j)$, and $E eq.not square.stroked$

  #derivation((
    ($E ~ rel(E)$, [@compiler-local-relation-find-E]),
    ($e'_1 = rel(E)[eblame(k)]$, []),
    ($e'_1 estep1 eblame(k)$, [Step and Reflexivity]),
    ($e'_2 = eblame(k)$, [Choose]),
  ))

- $E[e_3] cstep E[e_4]$ where $e_3 cstepx e_4$ is a redex

  - Case $mon(k,l,j,flat(e),v) cstepx check(k,j,apply(e,v),v)$

    #derivation((
      ($E ~ rel(E)$, [@compiler-local-relation-find-E]),
      ($e_3 ~ rel(e)_3$, [@compiler-local-relation-find-E]),
      ($rel(e)_3 = handle(heffcheck,(apply(perform(effcheck),tuple(k,tuple(rel(e),rel(v))))), m: s)$,[Inversion]),
      ($e'_1 = rel(E)[rel(e)_3]$, []),
      ($e'_1 estep ife(apply(rel(e),rel(v)),apply((lambda x. rel(E)[x]), rel(v)),eblame(k))$, []),
      ($E[e_4] ~ ife(apply(rel(e),rel(v)),apply((lambda x. rel(E)[x]), rel(v)),eblame(k))$, []),
      ($e'_2 = ife(apply(rel(e),rel(v)),apply((lambda x. rel(E)[x]), rel(v)),eblame(k))$, [Choose]),
    ))

  - Case $mon(k,l,j,kappa,v) cstepx guard(v,kappa,k,l,j)$ and $kappa != flat(e)$

      #derivation((
        ($E ~ rel(E)$, [@compiler-local-relation-find-E]),
        ($e_3 ~ rel(e)_3$, [@compiler-local-relation-find-E]),
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
        ($e_(5a)[f:=v] ~ rel(e)_(5a)[f:=rel(v)]$, [@compiler-local-relation-substitution]),
        ($e_(5a)[f:=v] = lambda x. mon(k,l,j,kappa_2,apply(v,mon(l,k,j,kappa_1,x)))$, []),
        ($e_4 ~ rel(e)_(5a)[f:=rel(v)]$, [Relation]),
        ($e_2 = E[e_4] ~ rel(E)[rel(e)_(5a)[f:=rel(v)]]$, [@compiler-local-relation-plug]),
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
        ($e_(5a)[f:=v] ~ rel(e)_(5a)[f:=rel(v)]$, [@compiler-local-relation-substitution]),
        ($e_(5a)[f:=v] = lambda x. mon(k,l,j,kappa_3,apply(v,mon(l,k,j,kappa_1,x)))$, []),
        ($e_4 ~ rel(e)_(5a)[f:=rel(v)]$, [Relation]),
        ($e_2 = E[e_4] ~ rel(E)[rel(e)_(5a)[f:=rel(v)]]$, [@compiler-local-relation-plug]),
        ($e'_2 = rel(E)[rel(e)_(5a)[f:=rel(v)]]$, [Choose]),
      ))

  - Case $check(k,j,trueb,v) cstepx v$

    #derivation((
      ($E[e_3] ~ ife(trueb,apply((lambda x. rel(E)[x]), rel(v)),eblame(k))$, [@compiler-local-relation-find-E-check]),
      ($e'_1 estep1 rel(E)[rel(v)]$, []),
      ($e_2 ~ rel(E)[rel(v)]$, []),
      ($e'_2 = rel(E)[rel(v)]$, [Choose])
    ))

  - Case $check(k,j,falseb,v) cstepx blame(k,j)$

    #derivation((
      ($E[e_3] ~ ife(falseb,apply((lambda x. rel(E)[x]), rel(v)),eblame(k))$, [@compiler-local-relation-find-E-check]),
      ($e'_1 estep1 eblame(k)$, []),
      ($e_2 ~ eblame(k)$, []),
      ($e'_2 = eblame(k)$, [Choose])
    ))

  - Case $e_3 = apply(guard(v_1,kappa_1 -> kappa_2,k,l,j),v_2) cstepx mon(k,l,j, kappa_2, apply(v_1, mon(l,k,j,kappa_1,v_2))) = e_4$

    #derivation((
      ($E ~ rel(E)$, [@compiler-local-relation-find-E]),
      ($e_3 ~ rel(e)_3$, [@compiler-local-relation-find-E]),
      ($rel(e)_3 = apply((lambda x. rel(e)_(3a)), rel(v)_2)$,[Inversion]),
      ($quad e_(3a) = mon(k,l,j,kappa_2,apply(v_1,mon(l,k,j,kappa_1,x)))$,[]),
      ($e_1 = E[e_3] ~ rel(E)[apply((lambda x. rel(e)_(3a)), rel(v)_2)] = e'_1$, [@compiler-local-relation-plug]),
      ($e'_1 estep1 rel(E)[rel(e)_(3a)[x:=rel(v)_2)]]$, []),
      ($e_(3a)[x:=v_2] = mon(k,l,j,kappa_2,apply(v_1,mon(l,k,j,kappa_1,v_2)))$, []),
      ($e_(3a)[x:=v_2] ~ rel(e)_(3a)[x:=rel(v)_2]$, [@compiler-local-relation-substitution]),
      ($e_2 = E[e_4] = E[e_(3a)[x:=v_2]] ~ rel(E)[rel(e)_(3a)[x:=rel(v)_2)]]$, [@compiler-local-relation-plug]),
      ($e'_2 = rel(E)[rel(e)_(3a)[x:=rel(v)_2)]]$, [Choose]),
    ))

  - Case $e_3 = apply(guard(v_1,dep(kappa_1, lambda y. kappa_2),k,l,j),v_2) cstepx mon(k,l,j, kappa_3, apply(v_1, mon(l,k,j,kappa_1,v_2))) = e_4$ where $kappa_3 = kappa_2[y:=mon(l,j,j,kappa_1,v_2)]$

    #derivation((
      ($E ~ rel(E)$, [@compiler-local-relation-find-E]),
      ($e_3 ~ rel(e)_3$, [@compiler-local-relation-find-E]),
      ($rel(e)_3 = apply((lambda x. rel(e)_(3a)), rel(v)_2)$,[Inversion]),
      ($quad e_(3a) = mon(k,l,j,kappa_4,apply(v_1,mon(l,k,j,kappa_1,x)))$,[]),
      ($quad kappa_4 = kappa_2[y:=mon(l,j,j,kappa_1,x)]$,[]),
      ($e_1 = E[e_3] ~ rel(E)[apply((lambda x. rel(e)_(3a)), rel(v)_2)] = e'_1$, [@compiler-local-relation-plug]),
      ($e'_1 estep1 rel(E)[rel(e)_(3a)[x:=rel(v)_2)]]$, []),
      ($e_(3a)[x:=v_2] = mon(k,l,j,kappa_4[x:=v_2],apply(v_1,mon(l,k,j,kappa_1,v_2)))$, []),
      ($quad kappa_4[x:=v_2] = kappa_2[y:=mon(l,j,j,kappa_1,v_2)] = kappa_3$, [$x in.not "fv"(kappa_2,kappa_1)$]),
      ($e_(3a)[x:=v_2] = mon(k,l,j,kappa_3,apply(v_1,mon(l,k,j,kappa_1,v_2)))$, []),
      ($e_(3a)[x:=v_2] ~ rel(e)_(3a)[x:=rel(v)_2]$, [@compiler-local-relation-substitution]),
      ($e_2 = E[e_4] = E[e_(3a)[x:=v_2]] ~ rel(E)[rel(e)_(3a)[x:=rel(v)_2)]]$, [@compiler-local-relation-plug]),
      ($e'_2 = rel(E)[rel(e)_(3a)[x:=rel(v)_2)]]$, [Choose]),
    ))

  - Similarly for other cases.
]
