#import "@preview/curryst:0.6.0": rule, prooftree, rule-set

#import "/proofs/setup.typ": *
#import "/utils.typ": *
#import "/models/language.typ": *

#show: no-ref
#show: great-theorems-init

#let relate(e) = $accent(#e, tilde)$
#let treq(a,b) = $"EQ"(#a,#b)$
#let hcheck = $kw("H")$

== Overview

Proof for compiler from $langc$ to $"Untyped" "Shallow" lange$, the handler semantic is shallow, where the continuation does not reinstall the handler.

The only rule that changes from the deep semantics is Step-E-Perform, the continuation $k$ no longer wraps $E$ with $handle(h,dot)$.

#prooftree(rule(
  name: [Step-E-Perform-Shallow],
  $op in.not bop(E) and (op -> f) in h$,
  $k = lambda x. E[x]$,
  $handle(h, E[apply(perform(op), v)]) quad estepx quad apply(apply(f, v), k)$
))

#grid(
  columns: (auto,auto,auto),
  gutter: 1.5em,

  [$heffcheck : lab$],
  [$=$],
  grid.cell(align: left,
    [${effcheck -> forall alpha. tuple(blab, tuple(alpha -> boolt, alpha)) -> alpha}$]),

  [$hcheck$], [$=$],
  grid.cell(align: left,
    [$mu h. handler({effcheck -> lambda tuple(l,tuple(e,v)). lambda k. apply(h,(lambda \_. ife(apply(e,v),apply(k,v),eblame(l))))})$]
  ),

  [$kw("wrap")$], [$=$],
  grid.cell(align: left,
    [$Lambda alpha. med lambda f: unit -> alpha. apply(hcheck, f)$]
  ),
  [], grid.cell(colspan: 2, align: right,
    [where $lambda tuple(l,tuple(e,v))$ deconstructs the argument as tuple pattern]),
)

The handler clause re-installs $hcheck$ around the rest of the program by itself, instead of the continuation doing it. So the whole program always runs under exactly one $handle(heffcheck, dot)$ at the top, and the predicate of a check runs under the same handler as the program. We write $handle(heffcheck, e)$ for the program running under the handler of $hcheck$.

Compared to the deep semantics, there are no states without handle, and there is no nested handle for predicates. This makes the relation much simpler.

#line(length: 100%)

Compiler Correctness by proving (1) $langc ~ "Untyped " lange$, (2) $"Untyped " lange ~ lange$, then obtain $langc ~ lange$. (2) is trivial.

In this proof, we use $e^*$ as shorthand to denote $e$ untyped.

Assumptions:
- Contract predicates are values ($flat(e)$ with $e = lambda x. e_0$) and pure (they do not use the store).
- Tuple contracts and mutable cells are not covered.

== Relation

Let's first define these relations:

- $R_e subset.eq langc e times "Untyped" lange e$

  If $(e,e') in R_e$, we write $e attach(~, br: R_e) e'$ or $e ~ e'$. We define $relate(e)$ as shorthand for any expression $relate(e)$ satisfying $e ~ relate(e)$.

- $R_E subset.eq langc E times "Untyped" lange E$

  If $(E,E') in R_E$, we write $E attach(~, br: R_E) E'$ or $E ~ E'$. We define $relate(E)$ as shorthand for any context $relate(E)$ satisfying $E ~ relate(E)$.

In the shallow semantics, the innermost check captures everything outside of it as its continuation, so a check is related together with its whole context:

$E[check(k,j,e,v)] ~ ife(relate(e), apply((lambda x. relate(E[x])), relate(v)), eblame(k))$

where $e$ has no check in evaluation position. $E$ may contain other checks, $relate(E[x])$ is again related by this rule, and it has one less check.

$
treq(e,e') = cases(
  "true" "if" e' = handle(heffcheck,relate(e)),
  "true" "if" e = E[blame(k,j)] "and" e' = handle(heffcheck,eblame(k)),
  "false" "otherwise",
)
$

#block(width: 100%)[
  #rect(stroke: 0.5pt, inset: 5pt)[
    $tilde.op subset.eq langc E times "Untyped" lange E$
  ]

  Define $relate(E)$ such that $E ~ relate(E)$. If $E$ contains a check, only the last row applies, on the innermost check.

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
    [$apply(perform(effcheck),tuple(k,tuple(relate(e),relate(E))))$],

    [$mon(k,l,j,kappa_1 -> kappa_2,E)$],
    [$tilde$],
    [$apply(relate(e)_1,relate(E))$],
    [],[],grid.cell(align:left,colspan:1)[$e_1$ as in the $mon(k,l,j,kappa_1 -> kappa_2,e)$ row below],

    [$mon(k,l,j,dep(kappa_1, lambda y. kappa_2),E)$],
    [$tilde$],
    [$apply(relate(e)_1,relate(E))$],
    [],[],grid.cell(align:left,colspan:1)[$e_1$ as in the $mon(k,l,j,dep(kappa_1, lambda y. kappa_2),e)$ row below],

    [$E[check(k,j,E_1,v)]$],
    [$tilde$],
    [$ife(relate(E)_1, apply((lambda x. relate(E[x])), relate(v)), eblame(k))$],
    [],[],grid.cell(align:left,colspan:1)[where $E_1$ has no check],
  )

  The other contexts ($tuple(E,e)$, $o(v...,E,e...)$, $ife(E,e_1,e_2)$, ...) are related homomorphically.
]

#block(width: 100%)[
  #rect(stroke: 0.5pt, inset: 5pt)[
    $tilde.op subset.eq langc e times "Untyped" lange e$
  ]

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
    [$apply(perform(effcheck),tuple(k,tuple(relate(e)_1,relate(e)_2)))$],

    [$mon(k,l,j,kappa_1 -> kappa_2,e)$],
    [$tilde$],
    [$apply(relate(e)_1,relate(e))$],
    [],[],grid.cell(align:left,colspan:1)[$e_1=lambda f. lambda x. mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x)))$],

    [$mon(k,l,j,dep(kappa_1, lambda y. kappa_2),e)$],
    [$tilde$],
    [$apply(relate(e)_1,relate(e))$],
    [],[],grid.cell(align:left,colspan:1)[$e_1=lambda f. lambda x. apply((lambda y. mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x)))), mon(l,j,j,kappa_1,x))$],

    [$E[check(k,j,e,v)]$],
    [$tilde$],
    [$ife(relate(e), apply((lambda x. relate(E[x])), relate(v)), eblame(k))$],
    [],[],grid.cell(align:left,colspan:1)[where $e$ has no check in evaluation position (innermost check)],

    [${e_y\/y}e$],
    [$tilde$],
    [$relate(e)[y:=relate(v)_y]$],
    [],[],grid.cell(align:left,colspan:1)[where $e_y = mon(l,j,j,kappa_1,v)$, $e_y cstep1 v_y$ and $v_y ~ relate(v)_y$ (indy argument)],

    [$blame(k,j)$],[$tilde$],[$eblame(k)$],
  )

  The other expressions ($tuple(e_1,e_2)$, $o(e...)$, $ife(e_1,e_2,e_3)$, $mu x. e$, ...) are related homomorphically.
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
  If $E ~ relate(E)$, $e ~ relate(e)$ and $e$ has no check in evaluation position, then $E[e] ~ relate(E)[relate(e)]$.
] <shallow-relation-context>

#proof[
By case on $E$.

- Case $E$ has no check

  By induction on $E$, every row of $E ~ relate(E)$ matches a row of $e ~ relate(e)$ with the hole filled.

- Case $E = E_0[check(k,j,E_1,v)]$ where $E_1$ has no check

  $E[e] = E_0[check(k,j,E_1[e],v)]$ and $E_1[e]$ has no check in evaluation position.

  $E[e] ~ ife(relate(E_1[e]), apply((lambda x. relate(E_0[x])), relate(v)), eblame(k))$ by the check row.

  $relate(E_1[e]) = relate(E)_1[relate(e)]$ by the previous case.

  $= relate(E)[relate(e)]$ by the check row of $E ~ relate(E)$.
]

#lemma(title: "Relation is closed under substitution")[
  If $e ~ relate(e)$ and $v ~ relate(v)$ then $e[x:=v] ~ relate(e)[x:=relate(v)]$.
] <shallow-substitution>

#proof[
  By induction on $e ~ relate(e)$. Every row is homomorphic on $x$, and the bound variables $f$, $x$, $y$ in the rows are chosen fresh.
]

#lemma(title: "Compiler is subset of relation")[

  If $compile(type(dot,e_1,tau),e_2)$ then $e_1 ~ e^*_2$.
] <shallow-compiler-is-relation>

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
        $compile(type(dot,e_3,tau_1 -> tau_2), e_4)$,
        $compile(type(dot,
            lambda f. lambda x. mon(k,l,j,kappa_2,apply(f, mon(l,k,j,kappa_1,x))),
            (tau_1 -> tau_2) -> (tau_1 -> tau_2)),
          e_5)$,
        $compile(type(dot,mon(k,l,j,kappa_1->kappa_2,e_3),tau_1 -> tau_2),apply(e_5, e_4))$,
      ))

  By I.H., $e_3 ~ e^*_4$

  By I.H., $lambda f. lambda x. mon(k,l,j,kappa_2,apply(f, mon(l,k,j,kappa_1,x))) ~ e^*_5$

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

- Other cases are homomorphic, by I.H.
]

== Compiler Correctness

#theorem()[
  If $compile(type(dot,e,tau),e')$ and $e^* = "untyped"(apply(kw("wrap")[tau],(lambda \_. e')))$ and $e cstep1 r$ then $e^* estep1 relate(r)$.

  Where $r$ is a value $v$ or $blame(k,j)$.
]

#proof[

  $e^* estep1 e'_1$ and $treq(e,e'_1)$ by @shallow-wrap-step-eq.

  $e'_1 estep1 relate(r)$ by @shallow-full-simulation.

  $e^* estep1 relate(r)$ by combining steps.
]

#lemma(title: "Wrapped compiled program steps to an equivalent state with source program")[

  If $compile(type(dot,e,tau),e')$ and $e^*_1 = "untyped"(apply(kw("wrap")[tau],(lambda \_. e')))$ then it exists $e^*_2$ such that $e^*_1 estep1 e^*_2$ and $treq(e,e^*_2)$.
] <shallow-wrap-step-eq>

#proof[

By @shallow-compiler-is-relation, $e ~ e'^*$.

$e^*_1 estep1 apply(hcheck,lambda \_. e'^*) estep1 apply(handler(heffcheck),lambda \_. e'^*) estep handle(heffcheck, e'^*) = e^*_2$

By definition, $treq(e,e^*_2)$ (case 1).
]

#lemma()[
  If $e cstep1 r$ and $treq(e,e')$ then $e' estep1 relate(r)$.
] <shallow-full-simulation>

#proof[
  By breaking down the $cstep1$, and induction on it.

  - Case $r cstep1 r$ with $r = v$

    $e' = handle(heffcheck,relate(v))$ because $treq(v,e')$ (case 2 is invalid).

    $e' estep relate(v)$ by Step-E-Return.

  - Case $r cstep1 r$ with $r = blame(k,j)$

    $e' = handle(heffcheck,eblame(k))$ in both cases of $treq$.

    $e' estep eblame(k)$ by Step-E-Error.

  - Case $e cstep e_1$ and $e_1 cstep1 r$

    By simulation, we have $e' estep1 e'_1$ such that $treq(e_1,e'_1)$.

    By IH, $e'_1 estep1 relate(r)$.

    By chaining steps, $e' estep1 relate(r)$.
]

We also need to make a claim that in no where in $relate(e)$ do we have $handle$ or $perform(eff)$ that $eff != effcheck$, so $effcheck in.not bop(E')$ for every target context $E'$ under the top handle.

#lemma(title: "Performing a check")[
  If $E'$ has no $handle$, then

  $
  & handle(heffcheck, E'[apply(perform(effcheck),tuple(k,tuple(relate(e),relate(v))))]) \
  estep1 & handle(heffcheck, ife(apply(relate(e),relate(v)), apply((lambda x. E'[x]),relate(v)), eblame(k)))
  $
] <shallow-perform-check>

#proof[
  $
  & handle(heffcheck, E'[apply(perform(effcheck),tuple(k,tuple(relate(e),relate(v))))]) \
  estep& apply(apply((lambda tuple(l,tuple(e,v)). lambda k. apply(hcheck,(lambda \_. ife(apply(e,v),apply(k,v),eblame(l))))), tuple(k,tuple(relate(e),relate(v)))), (lambda x. E'[x])) "  (Step-E-Perform-Shallow)" \
  estep1& apply(hcheck,(lambda \_. ife(apply(relate(e),relate(v)),apply((lambda x. E'[x]),relate(v)),eblame(k)))) \
  estep1& handle(heffcheck, ife(apply(relate(e),relate(v)),apply((lambda x. E'[x]),relate(v)),eblame(k))) "  (unfold " mu", Step-E-Handler, " beta ")"
  $
]

#lemma()[
  If $e_1 cstep e_2$ and $treq(e_1,e'_1)$ then there exists $e'_2$ such that $e'_1 estep1 e'_2$ and $treq(e_2,e'_2)$.
] <shallow-simulation>

#proof(of: <shallow-simulation>)[
By case analysis on $e_1 cstep e_2$ with respect to $treq(e_1,e'_1)$.

- Case $e_1 = E[blame(k,j)] cstep blame(k,j) = e_2$ (Step-C-Blame)

  - Case $treq(e_1,e'_1)$ is case 2, $e'_1 = handle(heffcheck,eblame(k))$.

    $e'_2 = e'_1$, and $treq(blame(k,j),e'_2)$ (case 2 with $E = square.stroked$).

  - Case $treq(e_1,e'_1)$ is case 1, $e'_1 = handle(heffcheck,relate(E)[eblame(k)])$.

    $e'_1 estep handle(heffcheck,eblame(k)) = e'_2$ by Step-E-Error.

    Obtain $treq(blame(k,j),e'_2)$ (case 2 with $E = square.stroked$).

Otherwise, $e_1$ is not blamed and $treq(e_1,e'_1)$ is case 1. By decomposition lemma, $e_1 = E[e_3]$, $e_2 = E[e_4]$ and that $e_3 cstep e_4$ is a redex reduction.

If $e_3$ is not a check, $e'_1 = handle(heffcheck, relate(E)[relate(e)_3])$ by @shallow-relation-context.

Note that $relate(E)$ is an evaluation context of $lange$ without $handle$. Unlike the deep proof, there is no case split on the checks in $E$, the redex steps under the same top handle.

- Case $e_3 = mon(k,l,j,flat(e),v) cstep check(k,j,apply(e,v),v) = e_4$

  $relate(e)_3 = apply(perform(effcheck),tuple(k,tuple(relate(e),relate(v))))$

  $e'_1 estep1 handle(heffcheck, ife(apply(relate(e),relate(v)), apply((lambda x. relate(E)[x]), relate(v)), eblame(k))) = e'_2$ by @shallow-perform-check.

  $e_2 = E[check(k,j,apply(e,v),v)]$, and $apply(e,v)$ has no check in evaluation position.

  $e_2 ~ ife(apply(relate(e),relate(v)), apply((lambda x. relate(E[x])), relate(v)), eblame(k))$ by the check row.

  $relate(E[x]) = relate(E)[x]$ by @shallow-relation-context.

  Obtain $treq(e_2,e'_2)$ (case 1).

- Case $e_3 = check(k,j,trueb,v) cstep v = e_4$

  $e_1 = E[check(k,j,trueb,v)]$, the check is the innermost one.

  $e'_1 = handle(heffcheck, ife(trueb, apply((lambda x. relate(E[x])), relate(v)), eblame(k)))$ by the check row.

  $e'_1 estep1 handle(heffcheck, relate(E[x])[x:=relate(v)]) = e'_2$

  $e_2 = E[v] = E[x][x:=v] ~ relate(E[x])[x:=relate(v)]$ by @shallow-substitution.

  Obtain $treq(e_2,e'_2)$ (case 1).

- Case $e_3 = check(k,j,falseb,v) cstep blame(k,j) = e_4$

  $e_1 = E[check(k,j,falseb,v)]$, the check is the innermost one.

  $e'_1 = handle(heffcheck, ife(falseb, apply((lambda x. relate(E[x])), relate(v)), eblame(k)))$ by the check row.

  $e'_1 estep handle(heffcheck, eblame(k)) = e'_2$

  $e_2 = E[blame(k,j)]$

  Obtain $treq(e_2,e'_2)$ (case 2).

- Case $e_3 = mon(k,l,j,kappa_1 -> kappa_2, v) cstep guard(v, kappa_1 -> kappa_2, k,l,j) = e_4$

  Let $e_5 = lambda f. lambda x. mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x))) = lambda f. lambda x. e_(5a)$

  $relate(e)_3 = apply(relate(e)_5,relate(v))$

  $e'_1 estep handle(heffcheck, relate(E)[lambda x. relate(e)_(5a)[f:=relate(v)]]) = e'_2$ by $beta$.

  $guard(v,kappa_1 -> kappa_2,k,l,j) ~ lambda x. relate(e)_(5a)[f:=relate(v)]$ by the relation on values.

  Obtain $treq(e_2,e'_2)$ (case 1) by @shallow-relation-context.

- Case $e_3 = mon(k,l,j,dep(kappa_1, lambda y. kappa_2), v) cstep guard(v, dep(kappa_1, lambda y. kappa_2), k,l,j) = e_4$

  Same as the case $mon(k,l,j,kappa_1 -> kappa_2, v)$, with

  $e_5 = lambda f. lambda x. apply((lambda y. mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x)))), mon(l,j,j,kappa_1,x)) = lambda f. lambda x. e_(5a)$

- Case $e_3 = apply(guard(v_1,kappa_1 -> kappa_2,k,l,j),v_2) cstep mon(k,l,j,kappa_2,apply(v_1, mon(l,k,j,kappa_1,v_2))) = e_4$

  $relate(e)_3 = apply(relate(e)_5, relate(v)_2)$ where $e_5 = lambda x. mon(k,l,j,kappa_2,apply(relate(v)_1,mon(l,k,j,kappa_1,x)))$

  $e'_1 estep handle(heffcheck, relate(E)[relate(e)_4]) = e'_2$ by $beta$ and @shallow-substitution.

  Obtain $treq(e_2,e'_2)$ (case 1) by @shallow-relation-context.

- Case $e_3 = apply(guard(v_1,dep(kappa_1, lambda y. kappa_2),k,l,j),v_2) cstep mon(k,l,j, kappa_3, apply(v_1, mon(l,k,j,kappa_1,v_2))) = e_4$ where $kappa_3 = {mon(l,j,j,kappa_1,v_2)\/y}kappa_2$

  $relate(e)_3 = apply(relate(e)_5, relate(v)_2)$ where $e_5 = lambda x. apply((lambda y. e_(5a)), mon(l,j,j,kappa_1,x))$ and $e_(5a) = mon(k,l,j,kappa_2,apply(relate(v)_1,mon(l,k,j,kappa_1,x)))$

  $e'_1 estep handle(heffcheck, relate(E)[apply((lambda y. relate(e)_(5a)[x:=relate(v)_2]), relate(e)_7)])$ by $beta$, where $e_7 = mon(l,j,j,kappa_1,v_2)$

  The target checks the indy argument $mon(l,j,j,kappa_1,v_2)$ first, the source checks the argument $mon(l,k,j,kappa_1,v_2)$ first. For $kappa_1 = flat(e_p)$ both become $check(l,j,apply(e_p,v_2),v_2)$, so we pair the two checks.

  - Case the check fails.

    Both programs reach $check(l,j,falseb,v_2)$, then $blame(l,j)$ and $handle(heffcheck, eblame(l))$ as in the case $check(k,j,falseb,v)$.

  - Case the check succeeds, $mon(l,j,j,kappa_1,v_2) cstep1 v_y$ ($v_y = v_2$ for flat $kappa_1$, otherwise $v_y = guard(v_2,kappa_1,l,j,j)$).

    Let $e_6 = mon(k,l,j,kappa_2,apply(v_1,mon(l,k,j,kappa_1,v_2)))$, then $e_2 = E[{mon(l,j,j,kappa_1,v_2)\/y}e_6]$.

    $e'_1 estep1 handle(heffcheck, relate(E)[relate(e)_6[y:=relate(v)_y]]) = e'_2$

    By purity, the target's argument check $mon(l,k,j,kappa_1,relate(v)_2)$ succeeds again. Each later evaluation of $mon(l,j,j,kappa_1,v_2)$ inside $kappa_2$ in the source gives $v_y$ again and is matched by zero target steps.

    ${mon(l,j,j,kappa_1,v_2)\/y}e_6 ~ relate(e)_6[y:=relate(v)_y]$ by the indy row.

    Obtain $treq(e_2,e'_2)$ (case 1).

- Case $e_3$ is a base reduction ($beta$, $mu$, $injl$, $injr$, $ife$, $o$)

  $relate(e)_3$ is the same redex in $lange$, and $relate(e)_3 estep relate(e)_4$ by the same rule, using @shallow-substitution for $beta$ and $mu$.

  $e'_1 estep handle(heffcheck, relate(E)[relate(e)_4]) = e'_2$

  Obtain $treq(e_2,e'_2)$ (case 1) by @shallow-relation-context.
]
