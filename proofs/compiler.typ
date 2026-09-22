#import "setup.typ": *
#import "/utils.typ": *
#import "/models/language.typ": *

#show: no-ref
#show: great-theorems-init

#let relate(e) = $accent(#e, tilde)$

Compiler Correctness by proving (1) $langc ~ "Untyped " lange$, (2) $"Untyped " lange ~ lange$, then obtain $langc ~ lange$. (2) is trivial.

$"CompileUntyped"(e) = e'$ if $compile(type(Gamma,tau,e),e'')$ and $e' = "untyped"(e'')$


#theorem()[
  If $"Untyped" lange e' = "CompileUntyped"(langc e)$ and $e cstep1 v$ then $e' estep1 "CompileUntyped"(v)$.
]

#proof[
  By lemma on simulation, and that the $"CompileUntyped"$ relation is a subset of $R_e$.
]

#let treq(a,b) = $"EQ"(#a,#b)$

// $
// treq(e,e') = cases(
//   "true" "if" ,
//   "true" "if" ,
//   "false" "otherwise",
// )
// $


#lemma()[
  If $e ~ e'$ and $e cstep1 v$ then $handle(heffcheck,e') estep1 relate(v)$. (Similarly with blame? Maybe define $langc r = v | blame(k,j)$, $lange r = v | blame$)
]

#proof[
  By breaking down the $cstep1$, and induction on it.

  - Case $e cstep e_1$ and $e_1 cstep1 v$

    By lemma step simulation there exists a $e'_1$, such that $e_1 ~ e'_1$ and either:
    - $handle(heffcheck, e') estep1 handle(heffcheck,e'_1)$
    - $handle(heffcheck, e') estep1 e'_1$ and $e'_1 = ife(handle(heffcheck,e'_(1a)),e'_(1b),e'_(1c))$
    - $e' estep1 handle(heffcheck,e'_1)$
    - $e' estep1 e'_1$

    By IH, $handle(heffcheck,e'_1) estep1 relate(v)$.

  - Case $v cstep1 v$

    We can obtain $relate(v)$.

    $handle(heffcheck, relate(v)) estep relate(v)$.

    $handle(heffcheck, relate(v)) estep1 relate(v)$. Reflexivity.
]

Let's first define these relations:

- $R_e subset.eq langc e times "Untyped" lange e$

  If $(e,e') in R_e$, we write $e attach(~, br: R_e) e'$ or $e ~ e'$. We define $relate(e)$ as shorthand for any expression $relate(e)$ satisfying $e ~ relate(e)$.

- $R_E subset.eq langc E times "Untyped" lange E$

  If $(E,E') in R_E$, we write $E attach(~, br: R_E) E'$ or $E ~ E'$. We define $relate(E)$ as shorthand for any context $relate(E)$ satisfying $E ~ relate(E)$.

// - $R_kappa subset.eq langc kappa times "Untyped" lange e$

//   If $(kappa,e) in R_kappa$, we write $kappa attach(~, br: R_kappa) e$ or $kappa ~ e$. We define $relate(kappa)$ as shorthand for any expression $relate(e)$ satisfying $kappa ~ relate(e)$.


Through trace analysis, we notice that the expression of $lange$ is always appended with a handle, except for two cases:

- When it is equivalent to a check being performed.
- When the wrapper $w$ is unwrapping itself.

Simulation lemma:

We also need to make a claim that in no where in $e'_1$ do we have $perform(eff)$ that $eff != effcheck$.

#lemma()[
  If $e_1 cstep e_2$ and $e_1 ~ e'_1$ then there exists $e'_2$ such that $e_2 ~ e'_2$ and either:
  - $handle(heffcheck,e_2) estep1 handle(heffcheck,e'_2)$
  - $handle(heffcheck,e_2) estep1 e'_2$ and $e'_2 = ife(handle(heffcheck,e_(2a)),e_(2b),e_(2c))$
  - $e_2 estep1 handle(heffcheck,e'_2)$ and $e_2 = ife(handle(heffcheck,e_(2a)),e_(2b),e_(2c))$
  - $e_2 estep1 e'_2$ and $e_2 = ife(handle(heffcheck,e_(2a)),e_(2b),e_(2c))$

  We limit to if/else expression if it is not prepended with handle.
] <simulation>

#proof(of: <simulation>)[

Doing both case analysis on $e_1 cstep e_2$ and structure of $e_1 = E^*[e_(1a)]$ and $e_1 = E[E^*_1[check(k,j,E^*_2[e_(1b)],v)]]$

- Case of $E_0[ife(trueb,e_3,e_4)] cstep E_0[e_3]$

  - Case $E_0 = E^*$

    $e_1 = E^*[ife(trueb,e_3,e_4)] ~ relate(E)^*[ife(trueb,relate(e)_3,relate(e)_4)] = e'_1$

    $handle(heffcheck,e'_1) estep1 handle(heffcheck,relate(E)^*[relate(e)_3])$

    Let $e'_2 = relate(E)^*[relate(e)_3]$. Immediately, $e_2 ~ e'_2$. Matches case 1.

  - Case $E_0 = E[E^*_1[check(k,j,E^*_2,v)]]$

    $e_1 = E[E^*_1[check(k,j,E^*_2[ife(trueb,e_3,e_4)],v)]] ~ relate(E)[ife(handle(heffcheck, relate(E)^*_2[ife(trueb,relate(e)_3,relate(e)_4)]), apply((lambda x. handle(heffcheck, relate(E)^*_1[x])), relate(v)),blame))] = e'_1$

    $e'_1 estep relate(E)[ife(handle(heffcheck, relate(E)^*_2[relate(e)_3]), apply((lambda x. handle(heffcheck, relate(E)^*_1[x])), relate(v)),blame))] = e'_2$.

    $e'_1 estep1 e'_2$.

    By definition $e_2 ~ e'_2$. Matches case 4.



  Similarly for other trivial cases?

- Case of $E_0[mon(k,l,j,flat(e),v)] cstep E_0[check(k,j,apply(e,v),v)]$

  - Case $E_0 = E^*$

    $e_1 = E^*[mon(k,l,j,flat(e),v)] ~ relate(E)^*[apply(perform(effcheck),tuple(e,v))] = e'_1$

    $handle(heffcheck,e'_1) estep1 ife(handle(heffcheck,apply(relate(e),relate(v))), apply((lambda x. handle(heffcheck,relate(E)^*[x])),relate(v)),blame) = e'_2$.

    $e_2 = E^*[check(k,j,apply(e,v),v)] ~ e'_2$ by definition. Matches case 2.

  - Case $E_0 = E[E^*_1[check(k_0,j_0,E^*_2,v_0)]]$

    $e_1 = E[E^*_1[check(k_0,j_0,E^*_2[mon(k,l,j,flat(e),v)],v_0)]] ~ relate(E)[ife(handle(heffcheck, relate(E)^*_2[relate(e)_3]), apply((lambda x. handle(heffcheck,relate(E)^*_1[x])),relate(v)_0),blame)] = e'_1$

    Where $e_3 = mon(k,l,j,flat(e),v)$. Obtain $relate(e)_3 = apply(perform(effcheck),tuple(relate(e),relate(v)))$.

    $e_2 = E[E^*_1[check(k_0,j_0,E^*_2[check(k,j,apply(e,v),v)],v_0)]]$

    $relate(E)^*$ doesn't have any handle. $relate(E)^*_2$ doesn't have any handle as well.

    $e'_4 = handle(heffcheck, relate(E)^*_2[relate(e)_3]) \ estep1 ife(handle(heffcheck,apply(relate(e),relate(v))),apply((lambda x. handle(heffcheck,relate(E)^*_2[x])),relate(v)),blame) = e'_5$.

    $e_5 = E^*_2[check(k,j,apply(e,v),v)] ~ e'_5$ by definition.

    $e'_1 estep1 relate(E)[ife(e'_5, apply((lambda x. handle(heffcheck,relate(E)^*_1[x])),relate(v)_0),blame)] = e'_2$

    Note that this if expression has no handle. Which we have to add to the relation.

    $e_2 ~ e'_2$. Matches case 4.

- Case $E[mon(k,l,j,kappa_1 -> kappa_2,v)] cstep E[guard(v,kappa_1 -> kappa_2,k,l,j)]$

  // $e_1 = E[mon(k,l,j,kappa_1 -> kappa_2,v)] ~ relate(e)_3 = e'_1$

  // $handle(heffcheck,e'_1) estep1 handle(heffcheck,e'_1)$. Reflexivity.

  // Where $e_3 = E[apply((lambda f. lambda x. apply(f,x)),mon(k,l,j,kappa_2,apply(v,mon(l,k,j,kappa_1,x))))]$

  // By definition $e_2 ~ relate(e)_3$. Matches case 1.

- Case $E[check(k,j,trueb,v)] cstep E[v]$

  - Case $E_0 = E^*$

    $e_1 = E^*[check(k,j,trueb,v)] ~ ife(handle(heffcheck,trueb),apply((lambda x. handle(heffcheck, relate(E)^*[x])),relate(v)),blame) = e'_1$

    $e'_1 estep1 handle(heffcheck, relate(E)^*[relate(v)])$.

    $e_2 ~ relate(E)^*[relate(v)]$. Matches case 3.

  - Case $E_0 = E[E^*_1[check(k_0,j_0,E^*_2,v_0)]]$

    $e_1 = E[E^*_1[check(k_0,j_0,E^*_2[check(k,j,trueb,v)],v_0)]] ~ relate(E)[ife(handle(heffcheck,relate(e)_3), apply((lambda x. relate(E)^*_1[x]), relate(v)_0), blame)] = e'_1$

    Where $e_3 = E^*_2[check(k,j,trueb,v)]$ and,

    $relate(e)_3 = ife(handle(heffcheck, trueb), apply((lambda x. relate(E)^*_2[x]), relate(v)),blame)$.

    $e'_1 estep1 relate(E)[ife(handle(heffcheck, relate(E)^*_2[relate(v)]), apply((lambda x. relate(E)^*_1[x]), relate(v)_0), blame)] = e'_2$

    $e_2 = E[E^*_1[check(k_0,j_0,E^*_2[v],v_0)]]$

    $e_2 ~ e'_2$. Matches case 4.

- Case $E[check(k,j,falseb,v)] cstep E[blame(k,j)]$

- Case $E[blame(k,j)] cstep blame(k,j)$
]

#block(width: 100%)[
  #rect(stroke: 0.5pt, inset: 5pt)[
    $tilde.op subset.eq langc E times "Untyped" lange E$
  ]

  Define $relate(E)$ such that $E ~ relate(E)$.

  Very fuzzy about where I should put the handle? This would break the predicate and also the relation of $R_e$.

  #v(1em)
  #grid(
    columns: (1fr, auto, auto),
    column-gutter: 1em,
    row-gutter: 1.2em,
    align: (right, left, left),

    [$square.stroked$],
    [$tilde$],
    [$square.stroked$],

    [$apply(E,e)$],
    [$tilde$],
    [$apply(relate(E),relate(e))$],

    [$apply(v,E)$],
    [$tilde$],
    [$apply(relate(v),relate(E))$],

    [$mon(k,l,j,flat(e),E)$],
    [$tilde$],
    [$apply(perform(effcheck),tuple(relate(e),relate(E)))$],

    [$mon(k,l,j,kappa_1 -> kappa_2,E)$],
    [$tilde$],
    [$apply((lambda f. lambda x. apply(f,x)),relate(E)_1)$],
    [],[],grid.cell(align:left,colspan:1)[$E_1=mon(k,l,j,kappa_2,apply(E,mon(l,k,j,kappa_1,x)))$],

    // [$mon(k,l,j,dep(kappa_1, y. kappa_2),E)$],
    // [$tilde$],
    // [$handle(heffcheck, lambda x. relate(e_2))$],
    // [],[],grid.cell(align:left,colspan:1)[$e_1=mon(k,l,j,kappa_1,x), x "free in??" E$],
    // [],[],grid.cell(align:left,colspan:1)[$e_2=mon(k,l,j,kappa_2[y:=e_1],apply(E,mon(l,k,j,kappa_1,x)))$],

    [$E[E^*_1[check(k,j,E^*_2,v)]]$],
    [$tilde?$],
    [$E[ife(handle(heffcheck,apply(perform(effcheck),tuple(relate(E)^*,relate(v)))),(lambda x. relate(E)[x]) relate(v),blame)]$],

    [$E[E^*_1[check(k,j,E^*_2,v)]]$],
    [$tilde?$],
    [$relate(E)[ife(relate(E)^*_2,(lambda x. relate(E)^*_1[x]) relate(v),blame)]$],
  )
]

#block(width: 100%)[
  #rect(stroke: 0.5pt, inset: 5pt)[
    $tilde.op subset.eq langc e times "Untyped" lange e$
  ]

  Let $C(e) = e''$ where $compile(type(Gamma,e,tau),e')$ and $e'' = "untype"(e')$.

  $E^*$ is a context where it does not have any $check$ expression. Because the logic of the handler is to rewrite up until the handler.

  #v(1em)
  #grid(
    columns: (1fr, auto, auto),
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

    [$apply(e_1,e_2)$],
    [$tilde$],
    [$apply(relate(e)_1,relate(e)_2)$],

    [$E[mon(k,l,j,flat(e_1),e_2)]$],
    [$tilde$],
    [$relate(E)[perform(effcheck)tuple(relate(e)_1,relate(e)_2)]$],

    [$E[mon(k,l,j,kappa_1 -> kappa_2,e)]$],
    [$tilde$],
    [$relate(E)[apply((lambda f. lambda x. relate(e)_1),relate(e))]$],
    [],[],grid.cell(align:left,colspan:1)[$e_1=mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x)))$],

    // fill: (x, y) => if y in (7, 8) { rgb("eef2ff") },

    [$E[E^*[check(k, j, e, v)]]$],
    [$tilde$],
    [$relate(E)[ife(handle(heffcheck, relate(e)), apply((lambda x. handle(heffcheck, relate(E)^*[x])), relate(v)), blame)]$],

    [$E[E^*[check(k, j, e, v)]]$],
    [$tilde$],
    [$relate(E)[ife(relate(e), apply((lambda x. handle(heffcheck, relate(E)^*[x])), relate(v)), blame)]$],

    [$E[blame(k,j)]$],[$tilde$],[$blame$],
    [$blame(k,j)$],[$tilde$],[$blame$],
  )
]
