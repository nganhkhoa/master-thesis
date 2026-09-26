#import "/proofs/setup.typ": *
#import "/utils.typ": *
#import "/models/language.typ": *

#show: no-ref
#show: great-theorems-init

#let relate(e) = $accent(#e, tilde)$

Proof for compiler from $langc$ to $"Untyped" "Shallow" lange$, the handler semantic is shallow, where the continuation does not reinstall the handler.

#grid(
  columns: (auto,auto,auto),
  gutter: 1.5em,

  [$heffcheck : lab$],
  [$=$],
  grid.cell(align: left,
    [${effcheck -> forall alpha. tuple(blab, tuple(alpha -> boolt, alpha)) -> alpha}$]),

  [$kw("wrap")$], [$=$],
  grid.cell(align: left,
    [$Lambda alpha. med lambda f: unit -> alpha.$]
  ),
  [], [],
  [$apply((mu h. handler({effcheck -> lambda tuple(l,tuple(e,v)). lambda k. apply(h,(lambda \_. (ife(apply(e,v),apply(k,v),eblame(l)))))})), f)$],
  [], grid.cell(colspan: 2, align: right,
    [where $lambda tuple(l,tuple(e,v))$ deconstructs the argument as tuple pattern]),
)

For shallow handler semantic, we can wrap the handler outside. Now, every states are prepended with handle, and we can make the relation easily.


#line(length: 100%)

Compiler Correctness by proving (1) $langc ~ "Untyped " lange$, (2) $"Untyped " lange ~ lange$, then obtain $langc ~ lange$. (2) is trivial.

$"CompileUntyped"(e) = e'$ if $compile(type(Gamma,tau,e),e'')$ and $e' = "untyped"(e'')$


#theorem()[
  If $"Untyped" lange e' = "CompileUntyped"(langc e)$ and $e cstep1 v$ then $e' estep1 "CompileUntyped"(v)$.
]

#proof[
  By lemma on simulation, and that the $"CompileUntyped"$ relation is a subset of $R_e$.
]

#lemma(title: "Relation is equivalence")[
  If $e_1 ~ e'_1$ and $e_1 cstep1 r$ then $handle(heffcheck,e'_1) estep1 relate(r)$.
]

#proof[
By induction on $e_1 cstep1 r$.

- Case $r cstep1 r$.

  $handle(heffcheck,relate(r)) estep1 relate(r)$. Because $relate(r)$ is a value.

- Case $e_1 cstep e_2$ and $e_2 cstep1 r$

  By simulation, exists $e'_2$ where $handle(heffcheck,e'_1) estep1 handle(heffcheck,e'_2)$ and $e_2 ~ e'_2$.

  By IH, $handle(heffcheck,e'_2) estep1 relate(r)$

  By chaining steps, $handle(heffcheck,e'_1) estep1 relate(r)$.
]


#lemma(title: "Simulation")[
  If $e_1 ~ e'_1$ and $e_1 cstep e_2$ then $handle(heffcheck, e'_1) estep1 handle(heffcheck, e'_2)$ and $e_2 ~ e'_2$.
]

#proof[
Using decomposition lemma, $e_1 = E[e_3]$ and $e'_1 = relate(E)[relate(e)_3]$ (because $e_1 ~ e'_1$) and $e_2 = E[e_4]$. By step, $e_3 cstep e_4$.

Proof by case analysis on $e_3 cstep e_4$.

- Case $mon(k,l,j,flat(e),v) cstep check(k,j,apply(e,v),v)$

  $relate(e)_3 = apply(perform(effcheck),tuple(e,v))$

  $handle(heffcheck,e'_1) estep1 handle(heffcheck,ife(apply(relate(e),relate(v)),apply((lambda x. relate(E)[x]), relate(v)),blame))$

  $e_2 ~ ife(apply(relate(e),relate(v)),apply((lambda x. relate(E)[x]), relate(v)),blame) = e'_2$ by definition.

- Case $check(k,j,trueb,v) cstep v$

  $relate(e)_3 = ife(trueb,apply((lambda x. relate(E)[x]), relate(v)),blame)$

  $handle(heffcheck,e'_1) estep1 handle(heffcheck, relate(E)[relate(v)])$

  $e_2 ~ relate(E)[relate(v)] = e'_2$ by definition.
]


#block(width: 100%)[
  #rect(stroke: 0.5pt, inset: 5pt)[
    $tilde.op subset.eq langc E times "Untyped" lange E$
  ]

  Define $relate(E)$ such that $E ~ relate(E)$.

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

    [$E_1[check(k,j,E_2, v)]$],
    [$tilde$],
    [$ife(relate(E)_2, apply((lambda x. relate(E)_1[x]),relate(v)), blame)$],
  )
]

#block(width: 100%)[
  #rect(stroke: 0.5pt, inset: 5pt)[
    $tilde.op subset.eq langc e times "Untyped" lange e$
  ]

  Let $C(e) = e''$ where $compile(type(Gamma,e,tau),e')$ and $e'' = "untype"(e')$.

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

    [$E[check(k, j, e, v)]$],
    [$tilde$],
    [$ife(relate(e), apply((lambda x. relate(E)[x]), relate(v)), blame)$],

    [$E[blame(k,j)]$],[$tilde$],[$blame$],
    [$blame(k,j)$],[$tilde$],[$blame$],
  )
]
