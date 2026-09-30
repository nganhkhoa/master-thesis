#import "@preview/curryst:0.6.0": rule, prooftree, rule-set

#import "/proofs/setup.typ": *
#import "/utils.typ": *
#import "/models/language.typ": *

#show: no-ref
#show: great-theorems-init

#let relate(e) = $accent(#e, tilde)$
#let treq(a,b) = $"EQ"(#a,#b)$

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

  If $(e,e') in R_e$, we write $e attach(~, br: R_e) e'$ or $e ~ e'$. We define $relate(e)$ as shorthand for any expression $relate(e)$ satisfying $e ~ relate(e)$.

- $R_E subset.eq langc E times "Untyped" lange E$

  If $(E,E') in R_E$, we write $E attach(~, br: R_E) E'$ or $E ~ E'$. We define $relate(E)$ as shorthand for any context $relate(E)$ satisfying $E ~ relate(E)$.

// - $R_kappa subset.eq langc kappa times "Untyped" lange e$

//   If $(kappa,e) in R_kappa$, we write $kappa attach(~, br: R_kappa) e$ or $kappa ~ e$. We define $relate(kappa)$ as shorthand for any expression $relate(e)$ satisfying $kappa ~ relate(e)$.

And we have a predicate between $langc e$ and $"Untyped" lange e'$.

$E^+  = square.stroked | E^+[E^*[check(k,j,square.stroked,v)]]$

$relate(E)^+  = square.stroked | relate(E)^+[ife(square.stroked, apply((lambda x. handle(heffcheck,relate(E)^*[x])),relate(v)), blame)]$

and their relation is straightforward, they also belong to $E ~ relate(E)$ so we can reuse the syntax.

$
treq(e,e') = cases(
  "true" "if" e = v "and" e' = relate(v),
  "true" "if" e' = handle(heffcheck,relate(e)) "and" e != E^*[check(k,j,e'',v)],
  "true" "if" e = E^+[E^*[check(k,j,e_1,v)]] "and",
  quad quad quad e' = relate(E)^+[ife(e'_1,apply((lambda x. handle(heffcheck,relate(E)^*[x])),relate(v)),eblame(j))] "and",
  quad quad quad treq(e_1,e'_1),
  "true" "if" e = blame(k,j) "and" e' = eblame(j),
  "false" "otherwise",
)
$

#block(width: 100%)[
  #rect(stroke: 0.5pt, inset: 5pt)[
    $tilde.op subset.eq langc E^* times "Untyped" lange E^*$
  ]

  $E^*$ is a context without $check(k,j,e,v)$ in $langc$.

  Define $relate(E)^*$ such that $E^* ~ relate(E)^*$.

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
    [$apply(relate(E)^*,relate(e))$],

    [$apply(v,E^*)$],
    [$tilde$],
    [$apply(relate(v),relate(E)^*)$],

    [$mon(k,l,j,flat(e),E^*)$],
    [$tilde$],
    [$apply(perform(effcheck),tuple(relate(e),relate(E)^*))$],

    [$mon(k,l,j,kappa_1 -> kappa_2,E^*)$],
    [$tilde$],
    [$apply((lambda f. lambda x. apply(f,x)),relate(E)^*_1)$],
    [],[],grid.cell(align:left,colspan:1)[$E^*_1=mon(k,l,j,kappa_2,apply(E^*,mon(l,k,j,kappa_1,x)))$],

    [$mon(k,l,j,dep(kappa_1, lambda y. kappa_2),E^*)$],
    [$tilde$],
    [$apply(relate(e)_1,relate(E)^*)$],
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
    [$relate(v)$],


    [$apply(e_1,e_2)$],
    [$tilde$],
    [$apply(relate(e)_1,relate(e)_2)$],

    [$mon(k,l,j,flat(e_1),e_2)$],
    [$tilde$],
    [$perform(effcheck)tuple(relate(e)_1,relate(e)_2)$],

    [$mon(k,l,j,kappa_1 -> kappa_2,e)$],
    [$tilde$],
    [$apply(relate(e)_1,relate(e))$],
    [],[],grid.cell(align:left,colspan:1)[$e_1=lambda f. lambda x. mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x)))$],

    [$mon(k,l,j,dep(kappa_1, lambda y. kappa_2),e)$],
    [$tilde$],
    [$apply(relate(e)_1,relate(e))$],
    [],[],grid.cell(align:left,colspan:1)[$e_1=lambda f. lambda x. apply((lambda y. mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x)))), mon(l,j,j,kappa_1,x))$],

    [${e_y\/y}e$],
    [$tilde$],
    [$relate(e)[y:=relate(v)_y]$],
    [],[],grid.cell(align:left,colspan:1)[where $e_y = mon(l,j,j,kappa_1,v)$, $e_y cstep1 v_y$ and $v_y ~ relate(v)_y$ (indy argument)],

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

    [$b$],
    [$tilde$],
    [$b$],

    [$N$],
    [$tilde$],
    [$N$],

    [$lambda x. e$],
    [$tilde$],
    [$lambda x. relate(e)$],

    [$guard(v,kappa_1 -> kappa_2,k,l,j)$],
    [$tilde$],
    [$relate(e)$],
    [],[],grid.cell(align:left,colspan:1)[$e=lambda x. mon(k,l,j,kappa_2,apply(relate(v),mon(l,k,j,kappa_1,x)))$],

    [$guard(v,dep(kappa_1, lambda y. kappa_2),k,l,j)$],
    [$tilde$],
    [$relate(e)$],
    [],[],grid.cell(align:left,colspan:1)[$e=lambda x. apply((lambda y. mon(k,l,j,kappa_2,apply(relate(v),mon(l,k,j,kappa_1,x)))), mon(l,j,j,kappa_1,x))$],
  )
]

#lemma(title: "Relation is correct")[
  If $e ~ e'$ and $E ~ E'$ then $E[e] ~ E'[e']$.
]

#proof[
By induction on the structure of $E$.

Base case: $E = square.stroked$. Then $E[e] = e ~ e' = E'[e']$ by assumption.

Inductive cases:
- Case $E = apply(E_1, e_0)$ and $E' = apply(E'_1, e'_0)$ where $E_1 ~ E'_1$ and $e_0 ~ e'_0$.

  By I.H., $E_1[e] ~ E'_1[e']$. By relation definition, $apply(E_1[e], e_0) ~ apply(E'_1[e'], e'_0)$.

- Case $E = apply(v, E_1)$ and $E' = apply(v', E'_1)$ where $v ~ v'$ and $E_1 ~ E'_1$.

  By I.H., $E_1[e] ~ E'_1[e']$. By relation definition, $apply(v, E_1[e]) ~ apply(v', E'_1[e'])$.

- Case $E = mon(k,l,j,flat(e_0),E_1)$ and $E' = apply(perform(effcheck),tuple(relate(e_0),E'_1))$ where $e_0 ~ e'_0$ and $E_1 ~ E'_1$.

  By I.H., $E_1[e] ~ E'_1[e']$. By relation definition, $mon(k,l,j,flat(e_0),E_1[e]) ~ apply(perform(effcheck),tuple(relate(e_0),E'_1[e']))$.

- Case $E = mon(k,l,j,kappa_1 -> kappa_2,E_1)$ and $E' = apply(relate(e_c),E'_1)$ where $kappa_1 -> kappa_2 ~ e_c$ and $E_1 ~ E'_1$.

  By I.H., $E_1[e] ~ E'_1[e']$. By relation definition and contract compilation, $mon(k,l,j,kappa_1 -> kappa_2,E_1[e]) ~ apply(relate(e_c),E'_1[e'])$.

- Case $E = mon(k,l,j,dep(kappa_1, lambda y. kappa_2),E_1)$ and $E' = apply(relate(e_c),E'_1)$ where $e_c = lambda f. lambda x. apply((lambda y. mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x)))), mon(l,j,j,kappa_1,x))$ and $E_1 ~ E'_1$.

  By I.H., $E_1[e] ~ E'_1[e']$. By relation definition, $mon(k,l,j,dep(kappa_1, lambda y. kappa_2),E_1[e]) ~ apply(relate(e_c),E'_1[e'])$.

Note: We don't need explicit check cases here since $E^*$ contexts don't contain checks by definition.

All cases follow from the induction hypothesis and the compositional nature of the relation.
]


#lemma(title: "Breaking down Context E")[
  For all $E$, $E = E^+[E^*]$
]

#proof[
By induction on $E$.

- Case $E = square.stroked$

  Choose $E^+ = E^* = square.stroked$

- Case $E = E_1 e$

  By IH, $E_1 = E^+_1[E^*_1]$

  $E = apply(E^+_1[E^*_1],e)$

  - Case $E^+_1 = square.stroked$

    Then $E = apply(E^*_1,e)$

    Choose $E^+ = square.stroked, E^*=apply(E^*_1,e)$

  - Case $E^+_1 = E^+_2[E^*_2[check(k,j,square.stroked,v)]]$

    Then $E = apply(E^+_2[E^*_2[check(k,j,E^*_1,v)]],e) = (apply(E^+_2,e))[E^*_2[check(k,j,E^*_1,v)]]$

    Choose $E^+ = (apply(E^+_2,e))[E^*_2[check(k,j,square.stroked,v)]], E^*=E^*_1$

  Similarly to other basic cases.

- Case $E = check(k,j,E_1,v)$

  By IH, $E_1 = E^+_1[E^*_1]$

  $E = check(k,j,E^+_1[E^*_1],v) = check(k,j,E^+_1,v)[E^*_1]$

  - Case $E^+_1 = square.stroked$

    Then $E = check(k,j,square.stroked,v)[E^*_1]$

    Let $E^+ = check(k,j,square.stroked,v), E^* = E^*_1$

  - Case $E^+_1 = E^+_2[E^*_2[check(k_1,j_1,square.stroked,v_1)]]$.

    Then $E = check(k,j,E^+_2[E^*_2[check(k_1,j_1,square.stroked,v_1)]],v)[E^*_1]$

    Let $E^+ = check(k,j,E^+_2[E^*_2[check(k_1,j_1,square.stroked,v_1)]],v), E^* = E^*_1$

    (This last step is because $E[E^+_0] = E^+_1$, intuitively, it is true, if you have any context, and plug in a context that is doing some checking, then it becomes the context that is doing some checking.)

]

#lemma(title: "Context composition preserves check structure")[
  If $E^+ = E^+_0[E^*_0[check(k,j,square.stroked,v)]]$ and $E$ is any evaluation context, then $E[E^+] = E^+_1$ for some $E^+_1$ of the form $E^+_1 = E^+_2[E^*_2[check(k',j',square.stroked,v')]]$.
]

#proof[
By induction on the structure of $E$.

Base case: $E = square.stroked$. Then $E[E^+] = E^+ = E^+_0[E^*_0[check(k,j,square.stroked,v)]]$, which is already in the required form.

Inductive cases:
- Case $E = apply(E_1, e)$. By I.H., $E_1[E^+] = E^+_1$ where $E^+_1 = E^+_2[E^*_2[check(k',j',square.stroked,v')]]$.

  Then $E[E^+] = apply(E_1[E^+], e) = apply(E^+_2[E^*_2[check(k',j',square.stroked,v')]], e)$

  $= (apply(E^+_2, e))[E^*_2[check(k',j',square.stroked,v')]]$

  Taking $E^+_3 = apply(E^+_2, e)$, we get the required form.

- Case $E = apply(v, E_1)$. Similar to the previous case.

- Case $E = check(k_0,j_0,E_1,v_0)$. By I.H., $E_1[E^+] = E^+_1$.

  Then $E[E^+] = check(k_0,j_0,E^+_1,v_0)$

  If $E^+_1 = square.stroked$, then $E[E^+] = check(k_0,j_0,square.stroked,v_0)$ which has the required form.

  If $E^+_1 = E^+_2[E^*_2[check(k',j',square.stroked,v')]]$, then:
  $E[E^+] = check(k_0,j_0,E^+_2[E^*_2[check(k',j',square.stroked,v')]],v_0)$

  $= check(k_0,j_0,E^+_2,v_0)[E^*_2[check(k',j',square.stroked,v')]]$

  Taking $E^+_3 = check(k_0,j_0,E^+_2,v_0)$, we get the required form.

- Other cases (mon contexts) follow similarly.

In all cases, composing any context with a check-containing context yields another check-containing context.
]

#lemma(title: "Compiler is subset of relation")[

  If $compile(type(dot,e_1,tau),e_2)$ then $e_1 ~ e^*_2$.

  In this lemma, we use $e^*$ as shorthand to denote $e$ untyped.
] <compiler-is-relation>

#proof[

By induction on structure of $compile(type(dot,e_1,tau),e_2)$.

- Case #prooftree(rule(
    $compile(type(dot,e_3,tau -> boolt), e_5)$,
    $compile(type(dot,e_4,tau), e_6)$,
    $compile(type(dot,mon(k,l,j,flat(e_3),e_4),tau), apply(perform(effcheck, tau: tau), tuple(k, tuple(e_5, e_6))))$,
  ))

  $e^*_2 = apply(perform(effcheck), tuple(k, tuple(e^*_5, e^*_6)))$

  By I.H. $e_3 ~ e^*_5$ and $e_4 ~ e^*_6$.

  Then $e_1 ~ e^*_2$ by relation.

- Case #prooftree(rule(
        $compile(type(dot,e_3,tau_2), e_4)$,
        $compile(type(dot,
            lambda f : tau_1 -> tau_2. lambda x : tau_1. mon(k,l,j,kappa_2,apply(f, mon(l,k,j,kappa_1,x))),
            (tau_1 -> tau_2) -> (tau_1 -> tau_2)),
          e_5)$,
        $compile(type(dot,mon(k,l,j,kappa_1->kappa_2,e_1),tau_1 -> tau_2),apply(e_5, e_4))$,
      ))

    By I.H., $e_3 ~ e^*_4$

    By I.H., $lambda f : tau_1 -> tau_2. lambda x : tau_1. mon(k,l,j,kappa_2,apply(f, mon(l,k,j,kappa_1,x))) ~ e^*_5$

  Then $e_1 ~ e^*_2$ by relation.

- Case #prooftree(rule(
        $compile(type(dot,e_3,tau_1 -> tau_2), e_4)$,
        $compile(type(dot,
            lambda f. lambda x. apply((lambda y. mon(k,l,j,kappa_2,apply(f, mon(l,k,j,kappa_1,x)))), mon(l,j,j,kappa_1,x)),
            (tau_1 -> tau_2) -> (tau_1 -> tau_2)),
          e_5)$,
        $compile(type(dot,mon(k,l,j,dep(kappa_1, lambda y. kappa_2),e_3),tau_1 -> tau_2),apply(e_5, e_4))$,
      ))

    By I.H., $e_3 ~ e^*_4$

    By I.H., $lambda f. lambda x. apply((lambda y. mon(k,l,j,kappa_2,apply(f, mon(l,k,j,kappa_1,x)))), mon(l,j,j,kappa_1,x)) ~ e^*_5$

  Then $e_1 ~ e^*_2$ by relation.
]

== Compiler Correctness

#theorem()[
  If $compile(type(dot,e,tau),e')$ and $e^* = "untyped"(apply(kw("wrap")[tau],(lambda \_. e')))$ and $e cstep1 b$ then $e^* estep1 b$.
]

#proof[

  $e^* estep1 e'_1$ and $treq(e,e'_1)$ by @wrap-step-eq.

  $e'_1 estep1 b$ by @full-simulation.

  $e^* estep1 b$ by combining steps.
]

#lemma(title: "Wrapped compiled program steps to an equivalent state with source program")[

  If $compile(type(dot,e,tau),e')$ and $e^*_1 = "untyped"(apply(kw("wrap")[tau],(lambda \_. e')))$ then it exists $e^*_2$ such that $e^*_1 estep1 e^*_2$ and $treq(e,e^*_2)$.

  In this lemma, we use $e^*$ as shorthand to denote $e$ untyped.
] <wrap-step-eq>

#proof[

By @compiler-is-relation, $e ~ e'^*$.

$e^*_1 estep1 apply(handler(heffcheck),lambda \_. e'^*) estep handle(heffcheck, e'^*) = e^*_2$

By definition, $treq(e,e^*_2)$.

// By case on $compile(type(dot,e,tau),e')$.

// - Case #prooftree(rule(
//     $compile(type(dot,e_3,tau -> boolt), e_5)$,
//     $compile(type(dot,e_4,tau), e_6)$,
//     $compile(type(dot,mon(k,l,j,flat(e_3),e_4),tau), apply(perform(effcheck, tau: tau), tuple(k, tuple(e_5, e_6))))$,
//   ))

//   $
//   e^*_1 &= kw("wrap")(lambda \_. apply(perform(effcheck), tuple(k, tuple(e^*_5, e^*_6)))) \
//   &= apply(handler(heffcheck), (lambda \_. apply(perform(effcheck), tuple(k, tuple(e^*_5, e^*_6))))) \
//   &estep handle(heffcheck, (apply(perform(effcheck), tuple(k, tuple(e^*_5, e^*_6))))) = e^*_2
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
//   &estep handle(heffcheck, apply((lambda f. lambda x. e^*_7),e^*_4)) = e^*_2
//   $

//   $e ~ apply((lambda f. lambda x. e^*_7),e^*_4)$ by @compiler-is-relation.

//   $treq(e,e^*_2)$ by definition.

]

#lemma()[
  If $e cstep1 r$ and $treq(e,e')$ then $e' estep1 relate(r)$.
] <full-simulation>

#proof[
  By breaking down the $cstep1$, and induction on it.

  - Case $v cstep1 v$

    $e' = relate(r)$ because $treq(e,e')$.

    $e' estep1 relate(r)$. Reflexivity.

  - Case $e cstep e_1$ and $e_1 cstep1 r$

    By simulation, we have $e' estep1 e'_1$ such that $treq(e_1,e'_1)$.

    By IH, $e'_1 estep1 relate(r)$.

    By chaining steps, $e' estep1 relate(r)$.
]


We also need to make a claim that in no where in $e'_1$ do we have $perform(eff)$ that $eff != effcheck$.

#lemma()[
  If $e_1 cstep e_2$ and $treq(e_1,e'_1)$ then there exists $e'_2$ such that $e'_1 estep1 e'_2$ and $treq(e_2,e'_2)$.
] <simulation>

#proof(of: <simulation>)[
By case analysis on $e_1 cstep e_2$ with respect to $treq(e_1,e'_1)$. By decomposition lemma, we know that the program can be rewritten into:

$e_1 = E[e_3]$, $e_2 = E[e_4]$ and that $e_3 cstep e_4$ is a redex reduction.

- Case $e_3 = mon(k,l,j,flat(e),v) cstep check(k,j,apply(e,v),v) = e_4$

  - Case $e_1 = v$ is invalid.

  Context breakdown lemma, $E = E^+[E^*]$.

  $e_1 = E^+[E^*[e_3]]$

  - Case $E^+ = square.stroked$

    $e_1 = E^*[e_3] ~ relate(E)^*[apply(perform(effcheck),tuple(relate(e),relate(v)))]$

    By $treq(e_1,e'_1)$ (case 2), $e'_1 = handle(heffcheck,relate(E)^*[apply(perform(effcheck),tuple(relate(e),relate(v)))])$

    $e'_1 estep1 ife(handle(heffcheck,apply(relate(e),relate(v))),apply((lambda x. handle(heffcheck,relate(E)^*[x])),relate(v)),eblame(j)) = e'_2$

    By case 2, $treq(apply(e,v),handle(heffcheck,apply(relate(e),relate(v))))$

    Immediately $treq(e_2,e'_2)$ by case 3.

  - Case $E^+ = E^+_1[E^*_1[check(k_1,j_1,square.stroked,v_1)]]$

    $e_1 = E^+_1[E^*_1[check(k_1,j_1,E^*[e_3],v_1)]]$

    $
    e'_1 =& relate(E)^+_1[ife(handle(heffcheck,relate(E)^*[relate(e)_3]),apply((lambda x. handle(heffcheck,relate(E)^*_1[x])),relate(v)_1),eblame(j_1))] \
    =& relate(E)^+_1[ife(handle(heffcheck,relate(E)^*[apply(perform(effcheck),tuple(relate(e),relate(v)))]),apply((lambda x. handle(heffcheck,relate(E)^*_1[x])),relate(v)_1),eblame(j_1))] \
    estep1& relate(E)^+[ife(handle(heffcheck,apply(relate(e),relate(v))),apply((lambda x. handle(heffcheck, relate(E)^*[x])),relate(v)),eblame(j))] = e'_2
    $

    where $relate(E)^+ = relate(E)^+_1[ife(square.stroked,apply((lambda x. handle(heffcheck,relate(E)^*_1[x])),relate(v)_1),eblame(j_1))]$

    $e_2 = E^+_1[E^*_1[check(k_1,j_1,E^*[check(k,j,apply(e,v),v)],v_1)]]$

    $treq(E^*[check(k,j,apply(e,v),v)], ife(handle(heffcheck,apply(relate(e),relate(v))),apply((lambda x. handle(heffcheck, relate(E)^*[x])),relate(v)),eblame(j)))$ (case 3)

    By case 3, $treq(e_2,e'_2)$.

    (Case 2 is invalid, because of the shape of $e_2$)

- Case $e_3 = check(k,j,trueb,v) cstep v = e_4$

  - Case $e_1 = v$ is invalid.

  - Case $e_1 = E^+[E^*[check(k,j,trueb,v)]]$.

    By $treq(e_1,e'_1)$:

    $e'_1 = relate(E)^+[ife(e'_3,apply((lambda x. handle(heffcheck,relate(E)^*[x])),relate(v)),eblame(j))]$

    $treq(trueb,e'_3)$, because $trueb$ is a value, we obtain $e'_3 = trueb$.

    $e'_1 estep1 relate(E)^+[handle(heffcheck,relate(E)^*[relate(v)])]$

    $e_2 = E^+[E^*[v]]$

    - Case $E^+ = square.stroked$

      Straight up, $treq(E^*[v], handle(heffcheck,relate(E)^*[relate(v)]))$

    - Case $E^+ = E^+_1[E^*_1[check(k_1,j_1,square.stroked,v_1)]]$

      $relate(E)^+ = relate(E)^+_1[ife(square.stroked, apply((lambda x. handle(heffcheck,relate(E)^*_1[x])),relate(v)_1), eblame(j_1))]$

      $e_2 = E^+_1[E^*_1[check(k_1,j_1,E^*[v],v_1)]]$

      $e'_2 = relate(E)^+_1[ife(handle(heffcheck,relate(E)^*[relate(v)]), apply((lambda x. handle(heffcheck,relate(E)^*_1[x])),relate(v)_1), eblame(j_1))]$

      Trivially, $treq(E^*[v],handle(heffcheck,relate(E)^*[relate(v)]))$ (case 2).

      Obtain $treq(e_2,e'_2)$ (case 3).


- Case $e_3 = mon(k,l,j,kappa_1 -> kappa_2, v) cstep guard(v, kappa_1 -> kappa_2, k,l,j) = e_4$

  - Case $e_1 = v$ is invalid.

  Context breakdown lemma, $E = E^+[E^*]$.

  $e_1 = E^+[E^*[e_3]]$

  - Case $E^+ = square.stroked$

    Let $e_5 = lambda f. lambda x. mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x))) = lambda f. lambda x. e_(5a)$

    $e_1 = E^*[e_3] ~ relate(E)^*[apply((lambda f. lambda x. relate(e)_(5a)),relate(v))]$

    By $treq(e_1,e'_1)$ (case 2), $e'_1 = handle(heffcheck,relate(E)^*[apply((lambda f. lambda x. relate(e)_(5a)),relate(v))])$

    $e'_1 estep1 handle(heffcheck,relate(E)^*[lambda x. relate(e)_(5a)[f:=relate(v)]]) = e'_2$

    $e_2 = E^*[guard(v,kappa_1 -> kappa_2,k,l,j)]$

    $guard(v,kappa_1 -> kappa_2,k,l,j) ~ lambda x. relate(e)_(5a)[f:=relate(v)]$ by the relation on values.

    Obtain $treq(e_2,e'_2)$ (case 2).

  - Case $E^+ = E^+_1[E^*_1[check(k_1,j_1,square.stroked,v_1)]]$

    Let $e_5 = lambda f. lambda x. mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x)))$

    $e'_1 = relate(E)^+_1[ife(handle(heffcheck,relate(E)^*[apply(relate(e)_5,relate(v))]),apply((lambda x. handle(heffcheck,relate(E)^*_1[x])),relate(v)_1),eblame(j_1))]$

    $e'_1 estep1 relate(E)^+_1[ife(handle(heffcheck,relate(E)^*[lambda x. relate(e)_(5a)[f:=relate(v)]]),apply((lambda x. handle(heffcheck,relate(E)^*_1[x])),relate(v)_1),eblame(j_1))] = e'_2$

    where $e_(5a) = mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x)))$

    $e_2 = E^+_1[E^*_1[check(k_1,j_1,E^*[guard(v,kappa_1 -> kappa_2,k,l,j)],v_1)]]$

    Since $guard(v,kappa_1 -> kappa_2,k,l,j) ~ lambda x. relate(e)_(5a)[f:=relate(v)]$, we have $treq(e_2,e'_2)$ (case 3).

- Case $e_3 = apply(guard(v_1,kappa_1 -> kappa_2,k,l,j),v_2) cstep mon(k,l,j,kappa_2,apply(v_1, mon(l,k,j,kappa_1,v_2))) = e_4$

  - Case $e_1 = v$ is invalid.

  Context breakdown lemma, $E = E^+[E^*]$.

  $e_1 = E^+[E^*[e_3]]$

  - Case $E^+ = square.stroked$

    $relate(e)_3 = apply(relate(e)_5, relate(v)_2)$ where $e_5 = lambda x. mon(k,l,j,kappa_2,apply(relate(v)_1,mon(l,k,j,kappa_1,x)))$

    By $treq(e_1,e'_1)$ (case 2), $e'_1 = handle(heffcheck, relate(E)^*[relate(e)_3])$

    $e'_1 estep1 handle(heffcheck, relate(E)^*[relate(e)_4]) = e'_2$ by $beta$.

    $e_2 = E^*[e_4]$

    Obtain $treq(e_2,e'_2)$ (case 2).

  - Case $E^+ = E^+_1[E^*_1[check(k_1,j_1,square.stroked,v_1)]]$

    Same as the case $E^+ = square.stroked$, inside $relate(E)^+$, by case 3.

- Case $e_3 = mon(k,l,j,dep(kappa_1, lambda y. kappa_2), v) cstep guard(v, dep(kappa_1, lambda y. kappa_2), k,l,j) = e_4$

  Same as the case $mon(k,l,j,kappa_1 -> kappa_2, v)$, with

  $e_5 = lambda f. lambda x. apply((lambda y. mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x)))), mon(l,j,j,kappa_1,x)) = lambda f. lambda x. e_(5a)$

  $lambda x. relate(e)_(5a)[f:=relate(v)] ~ guard(v, dep(kappa_1, lambda y. kappa_2), k,l,j)$ by the relation on values.

- Case $e_3 = apply(guard(v_1,dep(kappa_1, lambda y. kappa_2),k,l,j),v_2) cstep mon(k,l,j, kappa_3, apply(v_1, mon(l,k,j,kappa_1,v_2))) = e_4$ where $kappa_3 = {mon(l,j,j,kappa_1,v_2)\/y}kappa_2$

  Assume contract predicates are pure (they do not use the store).

  - Case $e_1 = v$ is invalid.

  Context breakdown lemma, $E = E^+[E^*]$. We show $E^+ = square.stroked$, the other case is the same inside $relate(E)^+_1$, by case 3.

  $relate(e)_3 = apply(relate(e)_5, relate(v)_2)$ where $e_5 = lambda x. apply((lambda y. e_(5a)), mon(l,j,j,kappa_1,x))$ and $e_(5a) = mon(k,l,j,kappa_2,apply(relate(v)_1,mon(l,k,j,kappa_1,x)))$

  By $treq(e_1,e'_1)$ (case 2), $e'_1 = handle(heffcheck, relate(E)^*[relate(e)_3])$

  $e'_1 estep1 handle(heffcheck, relate(E)^*[apply((lambda y. relate(e)_(5a)[x:=relate(v)_2]), relate(e)_7)])$ by $beta$, where $e_7 = mon(l,j,j,kappa_1,v_2)$

  The target checks the indy argument $mon(l,j,j,kappa_1,v_2)$ first, the source checks the argument $mon(l,k,j,kappa_1,v_2)$ first. For $kappa_1 = flat(e_p)$ both become $check(l,j,apply(e_p,v_2),v_2)$, so we pair the two checks.

  - Case the check fails.

    Both programs reach $check(l,j,falseb,v_2)$, then $blame(l,j) ~ eblame(j)$ as in the case $check(k,j,falseb,v)$.

  - Case the check succeeds, $mon(l,j,j,kappa_1,v_2) cstep1 v_y$ ($v_y = v_2$ for flat $kappa_1$, otherwise $v_y = guard(v_2,kappa_1,l,j,j)$).

    Let $e_6 = mon(k,l,j,kappa_2,apply(v_1,mon(l,k,j,kappa_1,v_2)))$, then $e_2 = E^*[{mon(l,j,j,kappa_1,v_2)\/y}e_6]$.

    $e'_1 estep1 handle(heffcheck, relate(E)^*[relate(e)_6[y:=relate(v)_y]]) = e'_2$

    By purity, the target's argument check $mon(l,k,j,kappa_1,relate(v)_2)$ succeeds again. Each later evaluation of $mon(l,j,j,kappa_1,v_2)$ inside $kappa_2$ in the source gives $v_y$ again and is matched by zero target steps.

    ${mon(l,j,j,kappa_1,v_2)\/y}e_6 ~ relate(e)_6[y:=relate(v)_y]$ by the indy row.

    Obtain $treq(e_2,e'_2)$ (case 2).

- Case $e_3 = check(k,j,falseb,v) cstep blame(k,j) = e_4$

  - Case $e_1 = E^+[E^*[check(k,j,falseb,v)]]$

    By $treq(e_1,e'_1)$:

    $e'_1 = relate(E)^+[ife(falseb,apply((lambda x. handle(heffcheck,relate(E)^*[x])),relate(v)),eblame(j))]$

    $e'_1 estep1 relate(E)^+[eblame(j)] = e'_2$

    $e_2 = E^+[E^*[blame(k,j)]]$

    By Step-E-Error rule: $relate(E)^+[eblame(j)] estep eblame(j)$

    Since $blame(k,j) ~ eblame(j)$, we have $treq(e_2,e'_2)$.
]
