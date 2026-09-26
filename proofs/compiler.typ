#import "/proofs/setup.typ": *
#import "/utils.typ": *
#import "/models/language.typ": *

#show: no-ref
#show: great-theorems-init

#let relate(e) = $accent(#e, tilde)$

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

$"CompileUntyped"(e) = e'$ if $compile(type(Gamma,tau,e),e'')$ and $e' = "untyped"(e'')$


#theorem()[
  If $"Untyped" lange e' = "CompileUntyped"(langc e)$ and $e cstep1 v$ then $e' estep1 "CompileUntyped"(v)$.
]

#proof[
  By lemma on simulation, and that the $"CompileUntyped"$ relation is a subset of $R_e$.
]

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

#let treq(a,b) = $"EQ"(#a,#b)$

$
treq(e,e') = cases(
  "true" "if" e = v "and" e' = relate(v),
  "true" "if" e' = handle(heffcheck,relate(e)) "and" e != E^*[check(k,j,e'',v)],
  "true" "if" e = E^+[E^*[check(k,j,e_1,v)]] "and",
  quad quad quad e' = relate(E)^+[ife(e'_1,apply((lambda x. handle(heffcheck,relate(E)^*[x])),relate(v)),blame)] "and",
  quad quad quad treq(e_1,e'_1),
  "false" "otherwise",
)
$


#lemma()[
  If $e cstep1 r$ and $treq(e,e')$ then $e' estep1 relate(r)$.
]

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

    $e_1 = E^*[e_3] ~ relate(E)^*[apply(perform(effcheck),tuple(relate(e),v))]$

    Let $e'_1 = handle(heffcheck,relate(E)^*[apply(perform(effcheck),tuple(relate(e),v))])$

    $e'_1 estep1 ife(handle(heffcheck,apply(relate(e),relate(v))),apply((lambda x. handle(heffcheck,relate(E)[x])),relate(v)),blame) = e'_2$

    By case 2, $treq(apply(e,v),handle(heffcheck,apply(relate(e),relate(v))))$

    Immediately $treq(e_2,e'_2)$ by case 3.

  - Case $E^+ = E^+_1[E^*_1[check(k_1,j_1,square.stroked,v_1)]]$

    $e_1 = E^+_1[E^*_1[check(k_1,j_1,E^*[e_3],v_1)]]$

    $
    relate(e)_1 =& relate(E)^+_1[ife(handle(heffcheck,relate(E)^*[relate(e)_3]),apply((lambda x. handle(heffcheck,relate(E)^*[x])),relate(v)_1),blame)] \
    =& relate(E)^+_1[ife(handle(heffcheck,relate(E)^*[apply(perform(effcheck),tuple(relate(e),relate(v)))]),apply((lambda x. handle(heffcheck,relate(E)^*[x])),relate(v)_1),blame)] \
    estep1& relate(E)^+_2[ife(handle(heffcheck,apply(relate(e),relate(v))),apply((lambda x. handle(heffcheck, relate(E)^*[x])),relate(v)),blame)] = e'_2
    $

    $E^+_1[E^*_1[check(k_1,j_1,E^*[check(k,j,apply(e,v),v)],v_1)]]$

    $E^*[check(k,j,apply(e,v),v)] ~ ife(handle(heffcheck,apply(relate(e),relate(v))),apply((lambda x. handle(heffcheck, relate(E)^*[x])),relate(v)),blame)$

    $treq(E^*[check(k,j,apply(e,v),v)], ife(handle(heffcheck,apply(relate(e),relate(v))),apply((lambda x. handle(heffcheck, relate(E)^*[x])),relate(v)),blame))$ (case 3)

    By case 3, $treq(e_2,e'_2)$.

    (Case 2 is invalid, because of the shape of $e_2$)

- Case $e_3 = check(k,j,trueb,v) cstep v = e_4$

  - Case $e_1 = v$ is invalid.

  - Case $e_1 = E^+[E^*[check(k,j,trueb,v)]]$.

    By $treq(e_1,e'_1)$:

    $e'_1 = relate(E)^+[ife(e'_3,apply((lambda x. handle(heffcheck,relate(E)^*[x])),relate(v)),blame)]$

    $treq(trueb,e'_3)$, because $trueb$ is a value, we obtain $e'_3 = trueb$.

    $e'_1 estep1 relate(E)^+[handle(heffcheck,relate(E)^*[relate(v)])]$

    $e_1 cstep E^+[E^*[v]]$

    - Case $E^+ = square.stroked$

      Straight up, $treq(E^*[v], handle(heffcheck,relate(E)^*[relate(v)]))$

    - Case $E^+ = E^+_1[E^*_1[check(k,j,square.stroked,v)]]$

      $relate(E)^+ = relate(E)^+_1[ife(square.stroked, apply((lambda x. handle(heffcheck,relate(E)^*_1[x])),relate(v)), blame)]$

      $e_2 = E^+_1[E^*_1[check(k,j,E^*[v],v)]]$

      $e'_2 = relate(E)^+_1[ife((handle(heffcheck,relate(E)^*[relate(v)])), apply((lambda x. handle(heffcheck,relate(E)^*_1[x])),relate(v)), blame)]$

      Trvially, $treq(E^*[v],handle(heffcheck,relate(E)^*[relate(v)]))$.

      Obtain $treq(e_2,e'_2)$.

]

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

    // [$E[E^*_1[check(k,j,square.stroked, v)]]$],
    // [$tilde$],
    // [$tilde(E)[ife(square.stroked, (lambda x. handle(heffcheck, tilde(E)^*_1[x])) tilde(v), blame)]$],

    // [$E^*_1[check(k,j,E, v)]$],
    // [$tilde$],
    // [$ife(relate(E), (lambda x. handle(heffcheck, tilde(E)^*_1[x])) tilde(v), blame)$],
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
    [$apply((lambda f. lambda x. relate(e)_1),relate(e))$],
    [],[],grid.cell(align:left,colspan:1)[$e_1=mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x)))$],

    // fill: (x, y) => if y in (7, 8) { rgb("eef2ff") },

    [$E^*[check(k, j, e, v)]$],
    [$tilde$],
    [$ife(handle(heffcheck, relate(e)), apply((lambda x. handle(heffcheck, relate(E)^*[x])), relate(v)), blame)$],

    [$E^*[check(k, j, e, v)]$],
    [$tilde$],
    [$ife(relate(e), apply((lambda x. handle(heffcheck, relate(E)^*[x])), relate(v)), blame)$],

    [$blame(k,j)$],[$tilde$],[$blame$],
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
  )
]

#lemma(title: "Relation is correct")[
  If $e ~ e'$ and $E ~ E'$ then $E[e] ~ E'[e']$.
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
