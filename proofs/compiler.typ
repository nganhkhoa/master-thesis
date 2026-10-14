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
#let rn(r) = $mono(#r)$
// like make-proof, but the rule column always gets its full width
#let mp(rows) = {
  block(width: 100%, grid(
    columns: (1fr, auto),
    column-gutter: 2em,
    row-gutter: 0.8em,
    align: (left, right),
    ..rows.map(((a, b)) => (a, b)).flatten(),
  ))
}

= Compiler Correctness Proof (Deep Handler)

== Overview

Proof for compiler from $langc$ to $"Untyped" "Deep" lange$, the handler semantic is deep, where the continuation automatically reinstall the handler.

#grid(
  columns: (auto,auto,auto),
  gutter: 1.5em,

  [$heffcheck : lab$],
  [$=$],
  grid.cell(align: left,
    [${effcheck -> forall alpha. tuple(blab, tuple(alpha -> boolt, alpha)) -> alpha}$]),

  [$kw("wrap")$], [$=$],
  grid.cell(align: left,
    [$mu w : forall alpha. ((teff((), chevron.l heffcheck chevron.r, alpha)) -> alpha). Lambda alpha. med lambda f: (teff((),chevron.l heffcheck chevron.r,alpha)).$]
  ),

  [], [],
  [$apply(handler({effcheck -> lambda tuple(l,tuple(e,v)). lambda k. ife(apply(w[kw("bool")], (lambda \_. apply(e,v))),apply(k,v),eblame(l))}), f)$],
  [], grid.cell(colspan: 2, align: right,
    [where $lambda tuple(l,tuple(e,v))$ deconstructs the argument as tuple pattern]),
)


The proof get into the way a lot because it switch back and forth between states prepended with handle and states without handle.

#line(length: 100%)

Compiler Correctness by proving (1) $langc ~ "Untyped " lange$, (2) $"Untyped " lange ~ lange$, then obtain $langc ~ lange$. (2) is trivial.

== Relation

Let's first define these relations:

- $R_e subset.eq langc e times "Untyped" lange e$

  If $(e,e') in R_e$, we write $e attach(~, br: R_e) e'$ or $e ~ e'$. We define $rel(e)$ as shorthand for any expression $rel(e)$ satisfying $e ~ rel(e)$.

- $R_E subset.eq langc E times "Untyped" lange E$

  If $(E,E') in R_E$, we write $E attach(~, br: R_E) E'$ or $E ~ E'$. We define $rel(E)$ as shorthand for any context $rel(E)$ satisfying $E ~ rel(E)$.

// - $R_kappa subset.eq langc kappa times "Untyped" lange e$

//   If $(kappa,e) in R_kappa$, we write $kappa attach(~, br: R_kappa) e$ or $kappa ~ e$. We define $rel(kappa)$ as shorthand for any expression $rel(e)$ satisfying $kappa ~ rel(e)$.

We define a separated context to deal with how $check(k,j,e,v)$ are related from source to target.

#block(width: 100%)[
  #rect(stroke: 0.5pt, inset: 5pt)[
    $tilde.op subset.eq langc E^+ times "Untyped" lange E^+$
  ]


  $E^+  =& square.stroked | E^+[E^*[check(k,j,square.stroked,v)]]$

  Define $rel(E)^+$ such that $E^+ ~ rel(E)^+$.

  #v(1em)
  #grid(
    columns: (1fr, auto, 1fr),
    column-gutter: 1em,
    row-gutter: 1.2em,
    align: (right, left, left),

    [$square.stroked$],
    [$tilde$],
    [$square.stroked$],

    [$E^+[E^*[check(k,j,square.stroked,v)]]$],
    [$tilde$],
    [$rel(E)^+[ife(square.stroked, apply((lambda x. handle(heffcheck,rel(E)^*[x])),rel(v)), eblame(j))]$],
  )
]

#block(width: 100%)[
  #rect(stroke: 0.5pt, inset: 5pt)[
    $tilde.op subset.eq langc E^* times "Untyped" lange E^*$
  ]

  $E^*$ is a context without $check(k,j,e,v)$ in $langc$.

  Define $rel(E)^*$ such that $E^* ~ rel(E)^*$.

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
    [$apply(perform(effcheck),tuple(rel(e),rel(E)^*))$],

    [$mon(k,l,j,kappa_1 -> kappa_2,E^*)$],
    [$tilde$],
    [$apply(rel(e)_1,rel(E)^*)$],
    [],[],grid.cell(align:left,colspan:1)[$e_1$ as in the $mon(k,l,j,kappa_1 -> kappa_2,e)$ row below],

    [$mon(k,l,j,dep(kappa_1, lambda y. kappa_2),E^*)$],
    [$tilde$],
    [$apply(rel(e)_1,rel(E)^*)$],
    [],[],grid.cell(align:left,colspan:1)[$e_1$ as in the $mon(k,l,j,dep(kappa_1, lambda y. kappa_2),e)$ row below],
  )
]

#block(width: 100%)[
  #rect(stroke: 0.5pt, inset: 5pt)[
    $tilde.op subset.eq langc e times "Untyped" lange e$
  ]

  $E^*$ is a context without $check(k,j,e,v)$ in $langc$. So it does not have the check cases below.

  #v(1em)
  #grid(
    columns: (1fr, auto, auto),
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
    [$perform(effcheck)tuple(rel(e)_1,rel(e)_2)$],

    [$mon(k,l,j,kappa_1 -> kappa_2,e)$],
    [$tilde$],
    [$apply(rel(e)_1,rel(e))$],
    [],[],grid.cell(align:left,colspan:1)[$e_1=lambda f. lambda x. mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x)))$],

    [$mon(k,l,j,dep(kappa_1, lambda y. kappa_2),e)$],
    [$tilde$],
    [$apply(rel(e)_1,rel(e))$],
    [],[],grid.cell(align:left,colspan:1)[$e_1=lambda f. lambda x. mon(k,l,j,{mon(l,j,j,kappa_1,x)\/y}kappa_2,apply(f,mon(l,k,j,kappa_1,x)))$],

    [$blame(k,j)$],[$tilde$],[$eblame(j)$],
  )
]


#block(width: 100%)[
  #rect(stroke: 0.5pt, inset: 5pt)[
    $tilde.op subset.eq langc v times "Untyped" lange v$
  ]

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

    [$lambda x. e$],
    [$tilde$],
    [$lambda x. rel(e)$],

    [$guard(v,kappa_1 -> kappa_2,k,l,j)$],
    [$tilde$],
    [$rel(e)$],
    [],[],grid.cell(align:left,colspan:1)[$e=lambda x. mon(k,l,j,kappa_2,apply(rel(v),mon(l,k,j,kappa_1,x)))$],

    [$guard(v,dep(kappa_1, lambda y. kappa_2),k,l,j)$],
    [$tilde$],
    [$rel(e)$],
    [],[],grid.cell(align:left,colspan:1)[$e=lambda x. rel(mon(k,l,j,{mon(l,j,j,kappa_1,x)\/y}kappa_2,apply(v,mon(l,k,j,kappa_1,x))))$],
  )
]

#lemma(title: "Relation is correct")[
  If $e ~ e'$ and $E ~ E'$ then $E[e] ~ E'[e']$.
]

#proof[
By induction on the structure of $E$.

Base case: $E = square.stroked$.

#mp((( $E[e] = e ~ e' = E'[e']$, "Assumption"),))

Inductive cases:
- Case $E = apply(E_1, e_0)$ and $E' = apply(E'_1, e'_0)$ where $E_1 ~ E'_1$ and $e_0 ~ e'_0$.

  #mp((
    ($E_1[e] ~ E'_1[e']$, "I.H."),
    ($apply(E_1[e], e_0) ~ apply(E'_1[e'], e'_0)$, "Relation definition"),
  ))

- Case $E = apply(v, E_1)$ and $E' = apply(v', E'_1)$ where $v ~ v'$ and $E_1 ~ E'_1$.

  #mp((
    ($E_1[e] ~ E'_1[e']$, "I.H."),
    ($apply(v, E_1[e]) ~ apply(v', E'_1[e'])$, "Relation definition"),
  ))

- Case $E = mon(k,l,j,flat(e_0),E_1)$ and $E' = apply(perform(effcheck),tuple(e'_0,E'_1))$ where $e_0 ~ e'_0$ and $E_1 ~ E'_1$.

  #mp((
    ($E_1[e] ~ E'_1[e']$, "I.H."),
    ($mon(k,l,j,flat(e_0),E_1[e]) ~ apply(perform(effcheck),tuple(e'_0,E'_1[e']))$, "Relation definition"),
  ))

- Case $E = mon(k,l,j,kappa_1 -> kappa_2,E_1)$ and $E' = apply(e'_c,E'_1)$ where $e_c ~ e'_c$ and $E_1 ~ E'_1$, with $e_c = lambda f. lambda x. mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x)))$.

  #mp((
    ($E_1[e] ~ E'_1[e']$, "I.H."),
    ($mon(k,l,j,kappa_1 -> kappa_2,E_1[e]) ~ apply(e'_c,E'_1[e'])$, [Relation row for $mon(k,l,j,kappa_1 -> kappa_2,e)$, with $e := E_1[e]$ and $rel(e)_1 := e'_c$]),
  ))

- Case $E = mon(k,l,j,dep(kappa_1, lambda y. kappa_2),E_1)$ and $E' = apply(e'_c,E'_1)$ where $e_c ~ e'_c$ and $E_1 ~ E'_1$, with $e_c = lambda f. lambda x. mon(k,l,j,{mon(l,j,j,kappa_1,x)\/y}kappa_2,apply(f,mon(l,k,j,kappa_1,x)))$.

  #mp((
    ($E_1[e] ~ E'_1[e']$, "I.H."),
    ($mon(k,l,j,dep(kappa_1, lambda y. kappa_2),E_1[e]) ~ apply(e'_c,E'_1[e'])$, [Relation row for $mon(k,l,j,dep(kappa_1, lambda y. kappa_2),e)$, with $e := E_1[e]$ and $rel(e)_1 := e'_c$]),
  ))

Note: We don't need explicit check cases here since $E^*$ contexts don't contain checks by definition.

All cases follow from the induction hypothesis and the compositional nature of the relation.
]


#lemma(title: "Relation decomposition through check-free contexts")[

  If $E^*[e] ~ e'$, then there exist $E'^*$ and $e'_0$ such that
  $E^* ~ E'^*$ and $e ~ e'_0$ and $e' = E'^*[e'_0]$.
] <relation-context-decomposition>

#proof[
]


#lemma(title: "Relation is closed under substitution")[
  If $e ~ e'$ and $v ~ v'$ then $e[x:=v] ~ e'[x:=v']$.
] <relation-subst>

#proof[
By induction on the derivation of $e ~ e'$.

- Case $x ~ x$.

  #mp((( $x[x:=v] = v ~ v' = x[x:=v']$, "Assumption"),))

- Case $z ~ z$ with $z != x$.

  #mp((( $z[x:=v] = z ~ z = z[x:=v']$, "Both sides are unchanged"),))

- Case $lambda z. e_1 ~ lambda z. e'_1$ with $e_1 ~ e'_1$. Choose $z != x$ and $z in.not "fv"(v, v')$ by renaming.

  #mp((
    ($e_1[x:=v] ~ e'_1[x:=v']$, "I.H."),
    ($lambda z. e_1[x:=v] ~ lambda z. e'_1[x:=v']$, [The $lambda$ row]),
  ))

- All other rows ($apply$, $mon$ with flat, arrow and dependent contracts, $guard$, $b$, $N$, $blame$) are compositional. The substitution goes into every related sub-expression, including the predicates inside contracts and the wrappers $e_1$, and each follows by I.H.
]

#lemma(title: "Breaking down Context E")[
  For all $E$, $E = E^+[E^*]$
]

#proof[
By induction on $E$.

- Case $E = square.stroked$

  Choose $E^+ = E^* = square.stroked$

- Case $E = E_1 e$

  #mp((
    ($E_1 = E^+_1[E^*_1]$, "I.H."),
    ($E = apply(E^+_1[E^*_1],e)$, "Definition"),
  ))

  - Case $E^+_1 = square.stroked$

    #mp((
      ($E = apply(E^*_1,e)$, "By the case assumption"),
      ($E^+ = square.stroked, E^*=apply(E^*_1,e)$, "Choose"),
    ))

  - Case $E^+_1 = E^+_2[E^*_2[check(k,j,square.stroked,v)]]$

    #mp((
      ($E = apply(E^+_2[E^*_2[check(k,j,E^*_1,v)]],e) = (apply(E^+_2,e))[E^*_2[check(k,j,E^*_1,v)]]$, "By the case assumption"),
      ($E^+ = (apply(E^+_2,e))[E^*_2[check(k,j,square.stroked,v)]], E^*=E^*_1$, "Choose"),
    ))

  Similarly to other basic cases.

- Case $E = check(k,j,E_1,v)$

  #mp((
    ($E_1 = E^+_1[E^*_1]$, "I.H."),
    ($E = check(k,j,E^+_1[E^*_1],v) = check(k,j,E^+_1,v)[E^*_1]$, "Definition"),
  ))

  - Case $E^+_1 = square.stroked$

    #mp((
      ($E = check(k,j,square.stroked,v)[E^*_1]$, "By the case assumption"),
      ($E^+ = check(k,j,square.stroked,v), E^* = E^*_1$, "Let"),
    ))

  - Case $E^+_1 = E^+_2[E^*_2[check(k_1,j_1,square.stroked,v_1)]]$.

    #mp((
      ($E = check(k,j,E^+_2[E^*_2[check(k_1,j_1,square.stroked,v_1)]],v)[E^*_1]$, "By the case assumption"),
      ($E^+ = check(k,j,E^+_2[E^*_2[check(k_1,j_1,square.stroked,v_1)]],v), E^* = E^*_1$, [Let; [@context-composition-preservation]]),
    ))

]

#lemma(title: "Context composition preserves check structure")[

  If $E^+ = E^+_0[E^*_0[check(k,j,square.stroked,v)]]$ and $E$ is any evaluation context, then $E[E^+] = E^+_1$ for some $E^+_1$ of the form $E^+_1 = E^+_2[E^*_2[check(k',j',square.stroked,v')]]$.
] <context-composition-preservation>

#proof[
By induction on the structure of $E$.

Base case: $E = square.stroked$.

#mp((( $E[E^+] = E^+ = E^+_0[E^*_0[check(k,j,square.stroked,v)]]$, "Required form"),))

Inductive cases:
- Case $E = apply(E_1, e)$. By I.H., $E_1[E^+] = E^+_1$ where $E^+_1 = E^+_2[E^*_2[check(k',j',square.stroked,v')]]$.

  #mp((
    ($E[E^+] = apply(E_1[E^+], e) = apply(E^+_2[E^*_2[check(k',j',square.stroked,v')]], e)$, "Definition"),
    ($E[E^+] = (apply(E^+_2, e))[E^*_2[check(k',j',square.stroked,v')]]$, "Reassociate context composition"),
    ($E^+_3 = apply(E^+_2, e)$, "Take; required form"),
  ))

- Case $E = apply(v, E_1)$. Similar to the previous case.

- Case $E = check(k_0,j_0,E_1,v_0)$. By I.H., $E_1[E^+] = E^+_1$.

  #mp((( $E[E^+] = check(k_0,j_0,E^+_1,v_0)$, "Definition"),))

  If $E^+_1 = square.stroked$, then $E[E^+] = check(k_0,j_0,square.stroked,v_0)$ which has the required form.

  If $E^+_1 = E^+_2[E^*_2[check(k',j',square.stroked,v')]]$, then:
  #mp((
    ($E[E^+] = check(k_0,j_0,E^+_2[E^*_2[check(k',j',square.stroked,v')]],v_0)$, "Case assumption"),
    ($E[E^+] = check(k_0,j_0,E^+_2,v_0)[E^*_2[check(k',j',square.stroked,v')]]$, "Reassociate context composition"),
    ($E^+_3 = check(k_0,j_0,E^+_2,v_0)$, "Take; required form"),
  ))

- Other cases (mon contexts) follow similarly.

In all cases, composing any context with a check-containing context yields another check-containing context.
]

#lemma(title: "Compiler is subset of relation")[

  If $compile(type(Gamma,e_1,tau),e_2)$ then $e_1 ~ e^*_2$.

  In particular, for closed programs, if $compile(type(dot,e_1,tau),e_2)$ then $e_1 ~ e^*_2$.

  In this lemma, we use $e^*$ as shorthand to denote $e$ untyped.
] <compiler-is-relation>

#proof[

By induction on structure of $compile(type(Gamma,e_1,tau),e_2)$.

- Case #prooftree(rule(
    $x : tau in Gamma$,
    $compile(type(Gamma, x, tau), x)$,
  ))

  #mp((
    ($e^*_2 = x$, "Definition"),
    ($x ~ x$, "Relation"),
  ))

- Case #prooftree(rule(
    $compile(type(Gamma\, x : tau_1, e, tau_2), e')$,
    $compile(type(Gamma, lambda x : tau_1. e, tau_1 -> tau_2), lambda x : tau_1. e')$,
  ))

  #mp((
    ($e^*_2 = lambda x. e'^*$, "Definition"),
    ($e ~ e'^*$, [I.H. on the premise with context $Gamma, x : tau_1$]),
    ($lambda x. e ~ lambda x. e'^*$, "Relation"),
  ))

- Case #prooftree(rule(
    $compile(type(Gamma,e_3,tau -> boolt), e_5)$,
    $compile(type(Gamma,e_4,tau), e_6)$,
    $compile(type(Gamma,mon(k,l,j,flat(e_3),e_4),tau), apply(perform(effcheck, tau: tau), tuple(k, tuple(e_5, e_6))))$,
  ))

  #mp((
    ($e^*_2 = apply(perform(effcheck), tuple(k, tuple(e^*_5, e^*_6)))$, "Definition"),
    ($e_3 ~ e^*_5$, "I.H."),
    ($e_4 ~ e^*_6$, "I.H."),
    ($e_1 ~ e^*_2$, "Relation"),
  ))

- Case #prooftree(rule(
        $compile(type(Gamma,e_3,tau_2), e_4)$,
        $compile(type(Gamma,
            lambda f : tau_1 -> tau_2. lambda x : tau_1. mon(k,l,j,kappa_2,apply(f, mon(l,k,j,kappa_1,x))),
            (tau_1 -> tau_2) -> (tau_1 -> tau_2)),
          e_5)$,
        $compile(type(Gamma,mon(k,l,j,kappa_1->kappa_2,e_1),tau_1 -> tau_2),apply(e_5, e_4))$,
      ))

  #mp((
    ($e_3 ~ e^*_4$, "I.H."),
    ($lambda f : tau_1 -> tau_2. lambda x : tau_1. mon(k,l,j,kappa_2,apply(f, mon(l,k,j,kappa_1,x))) ~ e^*_5$, "I.H."),
    ($e_1 ~ e^*_2$, "Relation"),
  ))

- Case #prooftree(rule(
        $compile(type(Gamma,e_3,tau_1 -> tau_2), e_4)$,
        $compile(type(Gamma,
            lambda f. lambda x. mon(k,l,j,{mon(l,j,j,kappa_1,x)\/y}kappa_2,apply(f, mon(l,k,j,kappa_1,x))),
            (tau_1 -> tau_2) -> (tau_1 -> tau_2)),
          e_5)$,
        $compile(type(Gamma,mon(k,l,j,dep(kappa_1, lambda y. kappa_2),e_3),tau_1 -> tau_2),apply(e_5, e_4))$,
      ))

  #mp((
    ($e_3 ~ e^*_4$, "I.H."),
    ($lambda f. lambda x. mon(k,l,j,{mon(l,j,j,kappa_1,x)\/y}kappa_2,apply(f, mon(l,k,j,kappa_1,x))) ~ e^*_5$, "I.H."),
    ($e_1 ~ e^*_2$, "Relation"),
  ))

- Other cases are similar.
]

== Compiler Correctness

@proof-strategy shows the structure of the proof. The source program $e$ compiles to $e'$, and the target program runs $e'$ under $kw("wrap")$. After the handler is installed, the target reaches a state $e''_0$ with $treq(e,e''_0)$ (@wrap-step-eq). From then on, every source step $e_i cstep e_(i+1)$ is matched by zero or more target steps $e''_i estep1 e''_(i+1)$ that keep $treq(e_(i+1),e''_(i+1))$ (@simulation). Chaining the squares (@full-simulation), the source result $r$ and the target result $rel(r)$ are related: a value goes to its related value, and $blame(k,j)$ goes to $eblame(j)$.

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
    node((0, 2), $apply(kw("wrap")[tau], (lambda \_. e'))$),
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
    node((0.55, 1.45), text(size: 0.8em)[@wrap-step-eq]),
    node((1.5, 1), text(size: 0.8em)[@simulation]),
    node((2.5, 1), text(size: 0.8em)[@simulation]),
    node((3.5, 1), text(size: 0.8em)[@simulation]),
    node((3, 2.6), text(size: 0.8em)[chained by @full-simulation]),
  )
] <proof-strategy>

Define a predicate between $langc e$ and $"Untyped" lange e'$.

$
treq(e,e') = cases(
  "true" "if" e = v "and" e' = rel(v),
  "true" "if" e' = handle(heffcheck,rel(e)) "and" e != E^*[check(k,j,e'',v)],
  "true" "if" e = E^+[E^*[check(k,j,e_1,v)]] "and",
  quad quad quad e' = rel(E)^+[ife(e'_1,apply((lambda x. handle(heffcheck,rel(E)^*[x])),rel(v)),eblame(j))] "and",
  quad quad quad treq(e_1,e'_1),
  "true" "if" e = blame(k,j) "and" e' = eblame(j),
  "false" "otherwise",
)
$


#theorem(title: "Compiler Correctness")[

  If $compile(type(dot,e,tau),e')$ and $e^* = "untyped"(apply(kw("wrap")[tau],(lambda \_. e')))$ and $e cstep1 b$ then $e^* estep1 b$.
] <compiler-correctness>

#proof[

  #mp((
    ($e^* estep1 e'_1$, [@wrap-step-eq]),
    ($treq(e,e'_1)$, [@wrap-step-eq]),
    ($e'_1 estep1 b$, [@full-simulation]),
    ($e^* estep1 b$, "Combining steps"),
  ))
]

#lemma(title: "Wrapped compiled program steps to an equivalent state with source program")[

  If $compile(type(dot,e,tau),e')$ and $e^*_1 = "untyped"(apply(kw("wrap")[tau],(lambda \_. e')))$ then it exists $e^*_2$ such that $e^*_1 estep1 e^*_2$ and $treq(e,e^*_2)$.

  In this lemma, we use $e^*$ as shorthand to denote $e$ untyped.
] <wrap-step-eq>

#proof[

#mp((
  ($e ~ e'^*$, [@compiler-is-relation]),
  ($e^*_1 estep1 apply(handler(heffcheck),lambda \_. e'^*) estep1 handle(heffcheck, e'^*) = e^*_2$, "Wrapper reduction"),
  ($treq(e,e^*_2)$, "Definition"),
))

// By case on $compile(type(dot,e,tau),e')$.

// - Case #prooftree(rule(
//     $compile(type(dot,e_3,tau -> boolt), e_5)$,
//     $compile(type(dot,e_4,tau), e_6)$,
//     $compile(type(dot,mon(k,l,j,flat(e_3),e_4),tau), apply(perform(effcheck, tau: tau), tuple(k, tuple(e_5, e_6))))$,
//   ))

//   $
//   e^*_1 &= kw("wrap")(lambda \_. apply(perform(effcheck), tuple(k, tuple(e^*_5, e^*_6)))) \
//   &= apply(handler(heffcheck), (lambda \_. apply(perform(effcheck), tuple(k, tuple(e^*_5, e^*_6))))) \
//   &estep1 handle(heffcheck, (apply(perform(effcheck), tuple(k, tuple(e^*_5, e^*_6))))) = e^*_2
//   $

//   $e ~ apply(perform(effcheck), tuple(k, tuple(e^*_5, e^*_6)))$ by @compiler-is-relation

//   By definition $treq(e,e^*_2)$.

// - Case #prooftree(rule(
//         $x,f in.not "dom"(Gamma)$,
//         $compile(type(dot,e_3,tau_2), e_4)$,
//         $compile(type(dot\,x:tau_1\,f:tau_1->tau_2,mon(k,l,j,kappa_2,apply(f,x)),tau_2), e_5)$,
//         $compile(type(dot\,x:tau_1,mon(l,k,j,kappa_1,x),tau_1),e_6)$,
//         $e_7 = e_5[x:=e_6]$,
//         $compile(type(Gamma,mon(k,l,j,kappa_1->kappa_2,e_3),tau_1 -> tau_2),apply((lambda f: tau_1 -> tau_2. lambda x: tau_1. e_7),e_4))$,
//       ))

//   $
//   e^*_1 &= apply(kw("wrap"),(lambda \_. apply((lambda f. lambda x. e^*_7),e^*_4))) \
//   &= apply(handler(heffcheck), (lambda \_. apply((lambda f. lambda x. e^*_7),e^*_4))) \
//   &estep1 handle(heffcheck, apply((lambda f. lambda x. e^*_7),e^*_4)) = e^*_2
//   $

//   $e ~ apply((lambda f. lambda x. e^*_7),e^*_4)$ by @compiler-is-relation.

//   $treq(e,e^*_2)$ by definition.

]

#lemma()[
  If $e cstep1 r$ and $treq(e,e')$ then $e' estep1 rel(r)$.
] <full-simulation>

#proof[
  By breaking down the $cstep1$, and induction on it.

  - Case $v cstep1 v$

    #mp((
      ($e' = rel(r)$, [Definition of $treq(e,e')$]),
      ($e' estep1 rel(r)$, "Reflexivity"),
    ))

  - Case $blame(k,j) cstep1 blame(k,j)$

    #mp((
      ($r = blame(k,j)$, "Case assumption"),
      ($rel(r) = eblame(j)$, "Relation"),
      ($e' = eblame(j) = rel(r)$, [Definition of $treq(e,e')$]),
      ($e' estep1 rel(r)$, "Reflexivity"),
    ))

  - Case $e cstep e_1$ and $e_1 cstep1 r$

    #mp((
      ($e' estep1 e'_1$, [@simulation]),
      ($treq(e_1,e'_1)$, [@simulation]),
      ($e'_1 estep1 rel(r)$, "I.H."),
      ($e' estep1 rel(r)$, "Chaining steps"),
    ))
]


We also need to make a claim that in no where in $e'_1$ do we have $perform(eff)$ that $eff != effcheck$.

#lemma()[
  If $e_1 cstep e_2$ and $treq(e_1,e'_1)$ then there exists $e'_2$ such that $e'_1 estep1 e'_2$ and $treq(e_2,e'_2)$.
] <simulation>

#proof(of: <simulation>)[
By case analysis on $e_1 cstep e_2$ with respect to $treq(e_1,e'_1)$. By decomposition lemma, we know that the program can be rewritten into:

#mp((
  ($e_1 = E[e_3]$, "Decomposition lemma"),
  ($e_2 = E[e_4]$, "Decomposition lemma"),
  ($e_3 cstepx e_4$, "Redex reduction"),
))

When $treq(e_1,e'_1)$ holds by case 2, @relation-context-decomposition supplies the related check-free context $rel(E)^*$ occurring in $e'_1$. When it holds by case 3, the related contexts $rel(E)^+$ and $rel(E)^*$ are witnesses carried by the definition of $"EQ"$; we obtain them by inversion of that case.

- Case $e_3 = mon(k,l,j,flat(e),v) cstepx check(k,j,apply(e,v),v) = e_4$

  - Case $e_1 = v$ is invalid.

  #mp((
    ($E = E^+[E^*]$, "Context breakdown lemma"),
    ($e_1 = E^+[E^*[e_3]]$, "Substitution"),
  ))

  - Case $E^+ = square.stroked$

    By inversion of case 2 of $treq(e_1,e'_1)$, $e_1 ~ rel(e_1)$. Since $e_1 = E^*[e_3]$, @relation-context-decomposition gives contexts and expressions that we name $rel(E)^*$ and $rel(e)_3$.

    #mp((
      ($E^* ~ rel(E)^*$, [@relation-context-decomposition]),
      ($e_3 ~ rel(e)_3$, [@relation-context-decomposition]),
      ($rel(e_1) = rel(E)^*[rel(e)_3]$, [@relation-context-decomposition]),
      ($e_1 = E^*[e_3] ~ rel(E)^*[apply(perform(effcheck),tuple(rel(e),rel(v)))]$, "Relation"),
      ($e'_1 = handle(heffcheck,rel(E)^*[apply(perform(effcheck),tuple(rel(e),rel(v)))])$, [$treq(e_1,e'_1)$, case 2]),
      ($e'_1 estep1 ife(handle(heffcheck,apply(rel(e),rel(v))),apply((lambda x. handle(heffcheck,rel(E)^*[x])),rel(v)),eblame(j)) = e'_2$, "Reduction"),
      ($treq(apply(e,v),handle(heffcheck,apply(rel(e),rel(v))))$, "Case 2"),
      ($treq(e_2,e'_2)$, "Case 3"),
    ))

  - Case $E^+ = E^+_1[E^*_1[check(k_1,j_1,square.stroked,v_1)]]$

    #mp((( $e_1 = E^+_1[E^*_1[check(k_1,j_1,E^*[e_3],v_1)]]$, "Context decomposition"),))

    #mp((
      ($e'_1 = rel(E)^+_1[ife(handle(heffcheck,rel(E)^*[rel(e)_3]),apply((lambda x. handle(heffcheck,rel(E)^*_1[x])),rel(v)_1),eblame(j_1))]$, [Definition of $"EQ"$]),
      ($e'_1 = rel(E)^+_1[ife(handle(heffcheck,rel(E)^*[apply(perform(effcheck),tuple(rel(e),rel(v)))]),apply((lambda x. handle(heffcheck,rel(E)^*_1[x])),rel(v)_1),eblame(j_1))]$, "Relation"),
      ($e'_1 estep1 rel(E)^+[ife(handle(heffcheck,apply(rel(e),rel(v))),apply((lambda x. handle(heffcheck, rel(E)^*[x])),rel(v)),eblame(j))] = e'_2$, "Reduction"),
    ))

    where $rel(E)^+ = rel(E)^+_1[ife(square.stroked,apply((lambda x. handle(heffcheck,rel(E)^*_1[x])),rel(v)_1),eblame(j_1))]$

    #mp((
      ($e_2 = E^+_1[E^*_1[check(k_1,j_1,E^*[check(k,j,apply(e,v),v)],v_1)]]$, "Reduction under context"),
      ($treq(E^*[check(k,j,apply(e,v),v)], ife(handle(heffcheck,apply(rel(e),rel(v))),apply((lambda x. handle(heffcheck, rel(E)^*[x])),rel(v)),eblame(j)))$, "Case 3"),
      ($treq(e_2,e'_2)$, "Case 3"),
    ))

    (Case 2 is invalid, because of the shape of $e_2$)

- Case $e_3 = check(k,j,trueb,v) cstepx v = e_4$

  - Case $e_1 = v$ is invalid.

  - Case $e_1 = E^+[E^*[check(k,j,trueb,v)]]$.

    #mp((
      ($e'_1 = rel(E)^+[ife(e'_3,apply((lambda x. handle(heffcheck,rel(E)^*[x])),rel(v)),eblame(j))]$, [$treq(e_1,e'_1)$]),
      ($treq(trueb,e'_3)$, [Since $trueb$ is a value]),
      ($e'_3 = trueb$, [Definition of $"EQ"$]),
      ($e'_1 estep1 rel(E)^+[handle(heffcheck,rel(E)^*[rel(v)])]$, "Reduction"),
      ($e_2 = E^+[E^*[v]]$, "Source reduction"),
    ))

    - Case $E^+ = square.stroked$

      #mp((( $treq(E^*[v], handle(heffcheck,rel(E)^*[rel(v)]))$, "Case 2"),))

    - Case $E^+ = E^+_1[E^*_1[check(k_1,j_1,square.stroked,v_1)]]$

      #mp((
        ($rel(E)^+ = rel(E)^+_1[ife(square.stroked, apply((lambda x. handle(heffcheck,rel(E)^*_1[x])),rel(v)_1), eblame(j_1))]$, "Relation"),
        ($e_2 = E^+_1[E^*_1[check(k_1,j_1,E^*[v],v_1)]]$, "Source reduction"),
        ($e'_2 = rel(E)^+_1[ife(handle(heffcheck,rel(E)^*[rel(v)]), apply((lambda x. handle(heffcheck,rel(E)^*_1[x])),rel(v)_1), eblame(j_1))]$, "Target reduction"),
        ($treq(E^*[v],handle(heffcheck,rel(E)^*[rel(v)]))$, "Case 2"),
        ($treq(e_2,e'_2)$, "Case 3"),
      ))


- Case $e_3 = mon(k,l,j,kappa_1 -> kappa_2, v) cstepx guard(v, kappa_1 -> kappa_2, k,l,j) = e_4$

  - Case $e_1 = v$ is invalid.

  #mp((
    ($E = E^+[E^*]$, "Context breakdown lemma"),
    ($e_1 = E^+[E^*[e_3]]$, "Substitution"),
  ))

  - Case $E^+ = square.stroked$

    Let $e_5 = lambda f. lambda x. mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x))) = lambda f. lambda x. e_(5a)$

    By inversion of case 2 of $treq(e_1,e'_1)$, $e_1 ~ rel(e_1)$. Since $e_1 = E^*[e_3]$, @relation-context-decomposition gives contexts and expressions that we name $rel(E)^*$ and $rel(e)_3$.

    #mp((
      ($E^* ~ rel(E)^*$, [@relation-context-decomposition]),
      ($e_3 ~ rel(e)_3$, [@relation-context-decomposition]),
      ($rel(e_1) = rel(E)^*[rel(e)_3]$, [@relation-context-decomposition]),
      ($e_1 = E^*[e_3] ~ rel(E)^*[apply((lambda f. lambda x. rel(e)_(5a)),rel(v))]$, "Relation"),
      ($e'_1 = handle(heffcheck,rel(E)^*[apply((lambda f. lambda x. rel(e)_(5a)),rel(v))])$, [$treq(e_1,e'_1)$, case 2]),
      ($e'_1 estep1 handle(heffcheck,rel(E)^*[lambda x. rel(e)_(5a)[f:=rel(v)]]) = e'_2$, "Reduction"),
      ($e_2 = E^*[guard(v,kappa_1 -> kappa_2,k,l,j)]$, "Source reduction"),
      ($guard(v,kappa_1 -> kappa_2,k,l,j) ~ lambda x. rel(e)_(5a)[f:=rel(v)]$, "Relation on values"),
      ($treq(e_2,e'_2)$, "Case 2"),
    ))

  - Case $E^+ = E^+_1[E^*_1[check(k_1,j_1,square.stroked,v_1)]]$

    Let $e_5 = lambda f. lambda x. mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x)))$

    where $e_(5a) = mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x)))$.

    #mp((
      ($e'_1 = rel(E)^+_1[ife(handle(heffcheck,rel(E)^*[apply(rel(e)_5,rel(v))]),apply((lambda x. handle(heffcheck,rel(E)^*_1[x])),rel(v)_1),eblame(j_1))]$, [Definition of $"EQ"$]),
      ($e'_1 estep1 rel(E)^+_1[ife(handle(heffcheck,rel(E)^*[lambda x. rel(e)_(5a)[f:=rel(v)]]),apply((lambda x. handle(heffcheck,rel(E)^*_1[x])),rel(v)_1),eblame(j_1))] = e'_2$, "Reduction"),
      ($e_2 = E^+_1[E^*_1[check(k_1,j_1,E^*[guard(v,kappa_1 -> kappa_2,k,l,j)],v_1)]]$, "Source reduction"),
      ($guard(v,kappa_1 -> kappa_2,k,l,j) ~ lambda x. rel(e)_(5a)[f:=rel(v)]$, "Relation on values"),
      ($treq(e_2,e'_2)$, "Case 3"),
    ))

- Case $e_3 = apply(guard(v_1,kappa_1 -> kappa_2,k,l,j),v_2) cstepx mon(k,l,j,kappa_2,apply(v_1, mon(l,k,j,kappa_1,v_2))) = e_4$

  - Case $e_1 = v$ is invalid.

  #mp((
    ($E = E^+[E^*]$, "Context breakdown lemma"),
    ($e_1 = E^+[E^*[e_3]]$, "Substitution"),
  ))

  - Case $E^+ = square.stroked$

    where $e_5 = lambda x. mon(k,l,j,kappa_2,apply(rel(v)_1,mon(l,k,j,kappa_1,x)))$.

    By inversion of case 2 of $treq(e_1,e'_1)$, $e_1 ~ rel(e_1)$. Since $e_1 = E^*[e_3]$, @relation-context-decomposition gives contexts and expressions that we name $rel(E)^*$ and $rel(e)_3$.

    #mp((
      ($E^* ~ rel(E)^*$, [@relation-context-decomposition]),
      ($e_3 ~ rel(e)_3$, [@relation-context-decomposition]),
      ($rel(e_1) = rel(E)^*[rel(e)_3]$, [@relation-context-decomposition]),
      ($rel(e)_3 = apply(rel(e)_5, rel(v)_2)$, "Relation"),
      ($e'_1 = handle(heffcheck, rel(E)^*[rel(e)_3])$, [$treq(e_1,e'_1)$, case 2]),
      ($e'_1 estep1 handle(heffcheck, rel(E)^*[rel(e)_4]) = e'_2$, $beta$),
      ($e_2 = E^*[e_4]$, "Source reduction"),
      ($treq(e_2,e'_2)$, "Case 2"),
    ))

  - Case $E^+ = E^+_1[E^*_1[check(k_1,j_1,square.stroked,v_1)]]$

    Same as the case $E^+ = square.stroked$, inside $rel(E)^+$, by case 3.

- Case $e_3 = mon(k,l,j,dep(kappa_1, lambda y. kappa_2), v) cstepx guard(v, dep(kappa_1, lambda y. kappa_2), k,l,j) = e_4$

  Same as the case $mon(k,l,j,kappa_1 -> kappa_2, v)$, with

  #mp((
    ($e_5 = lambda f. lambda x. mon(k,l,j,{mon(l,j,j,kappa_1,x)\/y}kappa_2,apply(f,mon(l,k,j,kappa_1,x))) = lambda f. lambda x. e_(5a)$, "Definition"),
    ($lambda x. rel(e)_(5a)[f:=rel(v)] ~ guard(v, dep(kappa_1, lambda y. kappa_2), k,l,j)$, "Relation on values"),
  ))

- Case $e_3 = apply(guard(v_1,dep(kappa_1, lambda y. kappa_2),k,l,j),v_2) cstepx mon(k,l,j, kappa_3, apply(v_1, mon(l,k,j,kappa_1,v_2))) = e_4$ where $kappa_3 = {mon(l,j,j,kappa_1,v_2)\/y}kappa_2$

  - Case $e_1 = v$ is invalid.

  Context breakdown lemma, $E = E^+[E^*]$.

  Let $e_6 = mon(k,l,j,{mon(l,j,j,kappa_1,x)\/y}kappa_2,apply(v_1,mon(l,k,j,kappa_1,x)))$. Since $x in.not "fv"(v_1, kappa_1, kappa_2)$, $e_4 = e_6[x:=v_2]$.

  - Case $E^+ = square.stroked$

    By inversion of case 2 of $treq(e_1,e'_1)$, $e_1 ~ rel(e_1)$. Since $e_1 = E^*[e_3]$, @relation-context-decomposition gives contexts and expressions that we name $rel(E)^*$ and $rel(e)_3$.

    #mp((
      ($E^* ~ rel(E)^*$, [@relation-context-decomposition]),
      ($e_3 ~ rel(e)_3$, [@relation-context-decomposition]),
      ($rel(e_1) = rel(E)^*[rel(e)_3]$, [@relation-context-decomposition]),
      ($rel(e)_3 = apply((lambda x. rel(e)_6), rel(v)_2)$, [The $guard$ row of the relation on values]),
      ($e'_1 = handle(heffcheck, rel(E)^*[apply((lambda x. rel(e)_6), rel(v)_2)])$, [$treq(e_1,e'_1)$, case 2]),
      ($e'_1 estep1 handle(heffcheck, rel(E)^*[rel(e)_6[x:=rel(v)_2]]) = e'_2$, $beta$),
      ($e_2 = E^*[e_6[x:=v_2]]$, "Source reduction"),
      ($e_6[x:=v_2] ~ rel(e)_6[x:=rel(v)_2]$, [@relation-subst]),
      ($treq(e_2,e'_2)$, "Case 2"),
    ))

  - Case $E^+ = E^+_1[E^*_1[check(k_1,j_1,square.stroked,v_1)]]$

    Same as the case $E^+ = square.stroked$, inside $rel(E)^+$, by case 3.

  The indy monitors $mon(l,j,j,kappa_1,v_2)$ inside $kappa_3$ are ordinary $mon$ redexes. Each one is related to the compiled monitor at the same position in $rel(e)_6[x:=rel(v)_2]$, so when the source evaluates one, it is one of the $mon$ cases above.

- Case $e_3 = check(k,j,falseb,v) cstepx blame(k,j) = e_4$

  - Case $e_1 = E^+[E^*[check(k,j,falseb,v)]]$

    #mp((
      ($e'_1 = rel(E)^+[ife(falseb,apply((lambda x. handle(heffcheck,rel(E)^*[x])),rel(v)),eblame(j))]$, [$treq(e_1,e'_1)$]),
      ($e'_1 estep1 rel(E)^+[eblame(j)] = e'_2$, "Reduction"),
      ($e_2 = E^+[E^*[blame(k,j)]]$, "Source reduction"),
      ($rel(E)^+[eblame(j)] estep eblame(j)$, rn("Step-E-Error")),
      ($blame(k,j) ~ eblame(j)$, "Relation"),
      ($treq(e_2,e'_2)$, "Definition"),
    ))
]
