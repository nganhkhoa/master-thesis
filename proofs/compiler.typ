#import "@preview/curryst:0.6.0": rule, prooftree, rule-set

#import "/proofs/setup.typ": *
#import "/utils.typ": *
#import "/models/language.typ": *

#show: no-ref
#show: great-theorems-init

#let relate(e) = $accent(#e, tilde)$
#let relw(e) = $(#e)^tilde.op$

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

#remark[
  Conventions used throughout this proof.

  - The relation is stated for flat contracts and function contracts, the two contract forms that appear in Compile-Flat and Compile-Func. Dependent and tuple contracts compile by the same scheme (a $lambda$ that re-monitors its argument) and are handled exactly like the function case.

  - The predicate of a flat contract is a value, $flat(lambda x. e)$, as it is in every program of the model. The target builds the tuple $tuple(k,tuple(relate(e),dot))$ before performing, so a non-value predicate would be evaluated eagerly in the target but only at $ckw("check")$ time in the source.

  - For a compound term we write $relw(e)$ for its translation $relate(e)$, so that $relw(e[x:=v])$ is the translation of the whole substitution instance.

  - We write $blame$ for $eblame(k)$ in the target. The blame label $k$ that Compile-Flat threads through the tuple is passed unchanged to $eblame(k)$, and we drop it from the tuple in the tables below to keep them readable.

  - The store $sigma$ is related pointwise, $sigma ~ relate(sigma)$ iff $"dom"(sigma) = "dom"(relate(sigma))$ and $sigma(loc) ~ relate(sigma)(loc)$. Every rule below leaves the store untouched except the cell rules, which touch it identically on both sides, so we omit $sigma$ from the statements.

  - $ckw("check")$ and $ckw("blame")$ never occur under a binder in any state reachable from a compiled program: the compiler never emits them, and reduction only creates them in evaluation position, where substitution never places them under a $lambda$. We use this to treat the relation as a function on the terms that occur in the proof.
]

#line(length: 100%)

Compiler Correctness by proving (1) $langc ~ "Untyped " lange$, (2) $"Untyped " lange ~ lange$, then obtain $langc ~ lange$. (2) is trivial.


#let treq(a,b) = $"EQ"(#a,#b)$


#theorem()[
  If $compile(type(dot,e,tau),e')$ and $e^* = "untyped"(apply(kw("wrap")[tau],(lambda \_. e')))$ and $e cstep1 r$ then $e^* estep1 relate(r)$, where $r$ is a value or $blame(k,j)$. For a base value $r = b$, $relate(r) = b$.
]

#proof[

  $e^* estep1 e'_1$ and $treq(e,e'_1)$ by @wrap-step-eq.

  $e'_1 estep1 relate(r)$ by @full-simulation.

  $e^* estep1 relate(r)$ by combining steps.
]

#lemma(title: "Wrap unfolds to handle")[
  For any untyped $e$, $"untyped"(apply(kw("wrap")[tau],(lambda \_. e))) estep1 handle(heffcheck, e)$.

  Here $heffcheck$ denotes the closed handler obtained by unfolding $mu w$ once inside the handler clause, so that the clause reads $ife(apply(kw("wrap"),(lambda \_. apply(e,v))),apply(k,v),eblame(l))$.
] <wrap-unfold>

#proof[
  Type abstraction and type application are erased by $"untyped"$.

  $
  "untyped"(apply(kw("wrap")[tau],(lambda \_. e)))
  &= apply((mu w. lambda f. apply(handler(heffcheck), f)), (lambda \_. e)) \
  &estep apply((lambda f. apply(handler(heffcheck), f)), (lambda \_. e)) & "SFix" \
  &estep apply(handler(heffcheck), (lambda \_. e)) & "S-App" \
  &estep handle(heffcheck, apply((lambda \_. e), ())) & "Step-E-Handler" \
  &estep handle(heffcheck, e) & "S-App"
  $
]

#lemma(title: "Wrapped compiled program steps to an equivalent state with source program")[

  If $compile(type(dot,e,tau),e')$ and $e^*_1 = "untyped"(apply(kw("wrap")[tau],(lambda \_. e')))$ then it exists $e^*_2$ such that $e^*_1 estep1 e^*_2$ and $treq(e,e^*_2)$.

  In this lemma, we use $e^*$ as shorthand to denote $e$ untyped.
] <wrap-step-eq>

#proof[

By @compiler-is-relation, $e ~ e'^*$.

By @wrap-unfold, $e^*_1 estep1 handle(heffcheck, e'^*) = e^*_2$.

$e$ is a compiled program, so it contains no $ckw("check")$, hence $e != E^*[check(k,j,e'',v)]$.

By definition (case 2), $treq(e,e^*_2)$.

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

- All remaining compile rules (variables, constants, $lambda$, $mu$, application, $"if"$, tuples, injections, primitive operations, cells) translate each construct to the same construct with compiled sub-expressions. The relation has the matching homomorphic row for each of them, so $e_1 ~ e^*_2$ follows from the I.H. on the sub-expressions.
]

Let's first define these relations:

- $R_e subset.eq langc e times "Untyped" lange e$

  If $(e,e') in R_e$, we write $e attach(~, br: R_e) e'$ or $e ~ e'$. We define $relate(e)$ as shorthand for any expression $relate(e)$ satisfying $e ~ relate(e)$.

- $R_E subset.eq langc E times "Untyped" lange E$

  If $(E,E') in R_E$, we write $E attach(~, br: R_E) E'$ or $E ~ E'$. We define $relate(E)$ as shorthand for any context $relate(E)$ satisfying $E ~ relate(E)$.

And we have a predicate between $langc e$ and $"Untyped" lange e'$.

$E^+  = square.stroked | E^+[E^*[check(k,j,square.stroked,v)]]$

$relate(E)^+  = square.stroked | relate(E)^+[ife(square.stroked, apply((lambda x. handle(heffcheck,relate(E)^*[x])),relate(v)), blame)]$

and their relation is straightforward, they also belong to $E ~ relate(E)$ so we can reuse the syntax.

$
treq(e,e') = cases(
  "true" "if" e = v "and" e' = relate(v),
  "true" "if" e' = handle(heffcheck,relate(e)) "and" e != E^*[check(k,j,e'',v)],
  "true" "if" e = E^+[E^*[check(k,j,e_1,v)]] "and",
  quad quad quad e' = relate(E)^+[ife(e'_1,apply((lambda x. handle(heffcheck,relate(E)^*[x])),relate(v)),blame)] "and",
  quad quad quad treq(e_1,e'_1),
  "true" "if" e = E[blame(k,j)] "and" e' = E'[blame] "for any" E "and" E',
  "false" "otherwise",
)
$

The cases are numbered 1 to 4 in this order. Case 4 is the only case that covers a source state containing $ckw("blame")$; a state that has raised blame is about to discard its whole context on both sides, so the contexts need not be related.

The following two facts about $"EQ"$ are used repeatedly and follow directly from case 3.

#lemma(title: "Frame")[
  If $treq(e,e')$ and $E^+ ~ relate(E)^+$ then $treq(E^+[e],relate(E)^+[e'])$.
] <frame>

#proof[
  If $E^+ = square.stroked$ then $relate(E)^+ = square.stroked$ and the claim is the hypothesis.

  Otherwise $E^+ = E^+_1[E^*_1[check(k,j,square.stroked,v)]]$ and $relate(E)^+ = relate(E)^+_1[ife(square.stroked, apply((lambda x. handle(heffcheck,relate(E)^*_1[x])),relate(v)), blame)]$, so $E^+[e] = E^+_1[E^*_1[check(k,j,e,v)]]$ and $relate(E)^+[e'] = relate(E)^+_1[ife(e', apply((lambda x. handle(heffcheck,relate(E)^*_1[x])),relate(v)), blame)]$. This is case 3 with $treq(e,e')$.
]

#lemma(title: "Unframe")[
  If $treq(E^+[e],e')$, $e$ is not a value and $e != E[blame(k,j)]$, then $e' = relate(E)^+[e'']$ for some $e''$ with $treq(e,e'')$.
] <unframe>

#proof[
  We use that $E^+$ contexts compose: if $E^+_a$ and $E^+_b$ are $E^+$ contexts then so is $E^+_a thin [E^+_b]$, and likewise for $relate(E)^+$. Both follow by induction on $E^+_b$ from the grammar.

  By induction on $E^+$.

  - Case $E^+ = square.stroked$. Take $relate(E)^+ = square.stroked$ and $e'' = e'$.

  - Case $E^+ = E^+_1[E^*_1[check(k,j,square.stroked,v)]]$. Let $t = E^*_1[check(k,j,e,v)]$, so $E^+[e] = E^+_1[t]$.

    $t$ is not a value and contains no $ckw("blame")$ in evaluation position, so by IH on $E^+_1$, $e' = relate(E)^+_1[t']$ with $treq(t,t')$.

    $t$ is of the form $E^*[check(k,j,e''',v)]$, so cases 1, 2 and 4 of $treq(t,t')$ do not apply. By case 3, $t = E^+_2[E^*_2[check(k',j',e_1,v')]]$ and $t' = relate(E)^+_2[ife(e'_1,apply((lambda x. handle(heffcheck,relate(E)^*_2[x])),relate(v)'),blame)]$ with $treq(e_1,e'_1)$.

    Since $E^*_1$ contains no $ckw("check")$, the outermost $ckw("check")$ of $t$ is the one written, and there are two possibilities for the decomposition.

    - $E^+_2 = square.stroked$. Then $E^*_2 = E^*_1$, $e_1 = e$, $v' = v$, and $t' = ife(e'_1,apply((lambda x. handle(heffcheck,relate(E)^*_1[x])),relate(v)),blame)$ with $treq(e,e'_1)$. Take $e'' = e'_1$.

    - $E^+_2 != square.stroked$. Then its outermost frame is $E^*_1[check(k,j,square.stroked,v)]$, so by composition $E^+_2 = E^*_1[check(k,j,E^+_3,v)]$ for an $E^+$ context $E^+_3$, and $e = E^+_3[E^*_2[check(k',j',e_1,v')]]$. Correspondingly $relate(E)^+_2 = ife(relate(E)^+_3,apply((lambda x. handle(heffcheck,relate(E)^*_1[x])),relate(v)),blame)$.

      Let $e'' = relate(E)^+_3[ife(e'_1,apply((lambda x. handle(heffcheck,relate(E)^*_2[x])),relate(v)'),blame)]$. Then $treq(e,e'')$ by case 3, and $t' = ife(e'',apply((lambda x. handle(heffcheck,relate(E)^*_1[x])),relate(v)),blame)$.

    In both sub-cases $e' = relate(E)^+_1[ife(e'',apply((lambda x. handle(heffcheck,relate(E)^*_1[x])),relate(v)),blame)] = relate(E)^+[e'']$ with $relate(E)^+ ~ E^+$.
]


#lemma()[
  If $e cstep1 r$ and $treq(e,e')$ then $e' estep1 relate(r)$.
] <full-simulation>

#proof[
  By breaking down the $cstep1$, and induction on it.

  - Case $r cstep1 r$, zero steps.

    - Sub-case $r = v$. By $treq(v,e')$, either $e' = relate(v)$ (case 1) or $e' = handle(heffcheck,relate(v))$ (case 2). In the first, reflexivity. In the second, $handle(heffcheck,relate(v)) estep relate(v)$ by Step-E-Return, since $relate(v)$ is a value.

    - Sub-case $r = blame(k,j)$. By $treq(blame(k,j),e')$, only case 4 applies, so $e' = E'[blame]$. If $E' = square.stroked$, reflexivity. Otherwise $E'[blame] estep blame$ by Step-E-Error, and $blame(k,j) ~ blame$.

  - Case $e cstep e_1$ and $e_1 cstep1 r$

    By @simulation, we have $e' estep1 e'_1$ such that $treq(e_1,e'_1)$.

    By IH, $e'_1 estep1 relate(r)$.

    By chaining steps, $e' estep1 relate(r)$.
]


#remark[
  Nowhere in a state $e'$ with $treq(e,e')$ does $perform(eff)$ occur for $eff != effcheck$: the relation only ever produces $perform(effcheck)$, and the handler clause of $heffcheck$ only mentions $effcheck$. Likewise, no $handle(heffcheck, dot)$ occurs inside a $relate(E)^*$, which is what lets Step-E-Perform fire against the innermost $handle(heffcheck, dot)$ in the Mon-Flat case below.
]

#lemma()[
  If $e_1 cstep e_2$ and $treq(e_1,e'_1)$ then there exists $e'_2$ such that $e'_1 estep1 e'_2$ and $treq(e_2,e'_2)$.
] <simulation>

#proof(of: <simulation>)[
By case analysis on $e_1 cstep e_2$ with respect to $treq(e_1,e'_1)$. The step is either Step-C-Blame or Step-C. We treat Step-C-Blame first.

- Case Step-C-Blame, $e_1 = E[blame(k,j)] cstep blame(k,j) = e_2$ with $E != square.stroked$.

  $e_1$ is not a value and contains $ckw("blame")$ in evaluation position, so only case 4 of $treq(e_1,e'_1)$ applies: $e'_1 = E'[blame]$.

  If $E' = square.stroked$ take $e'_2 = e'_1 = blame$ in zero steps; otherwise $E'[blame] estep blame = e'_2$ by Step-E-Error.

  $treq(blame(k,j),blame)$ by case 4 with $E = E' = square.stroked$.

For Step-C, by the decomposition lemma we know that the program can be rewritten into:

$e_1 = E[e_3]$, $e_2 = E[e_4]$ and that $e_3 cstepx e_4$ is a redex reduction.

By @context-breakdown, $E = E^+[E^*]$, so $e_1 = E^+[E^*[e_3]]$ and $e_2 = E^+[E^*[e_4]]$.

$E^*[e_3]$ is not a value and contains no $ckw("blame")$ in evaluation position ($E^*$ contains no $ckw("blame")$, and no redex is of the form $E[blame(k,j)]$). By @unframe, $e'_1 = relate(E)^+[e'']$ with $treq(E^*[e_3],e'')$.

In every case below we exhibit $e''_2$ with $e'' estep1 e''_2$ and $treq(E^*[e_4],e''_2)$, or with $treq(E^+[E^*[e_4]], relate(E)^+[e''_2])$ directly. Since Step-E is closed under the evaluation context $relate(E)^+$, $e'_1 = relate(E)^+[e''] estep1 relate(E)^+[e''_2] = e'_2$, and $treq(e_2,e'_2)$ follows by @frame.

We split on the redex rule. Rules Mon-Flat, Check-True and Check-False involve the handler; every other rule is local and handled uniformly at the end.

- Case Mon-Flat, $e_3 = mon(k,l,j,flat(e),v) cstepx check(k,j,apply(e,v),v) = e_4$

  $E^*[e_3]$ is not of the form $E'^*[check(k',j',e''',v')]$, so $treq(E^*[e_3],e'')$ holds by case 2:

  $e'' = handle(heffcheck, relate(E)^*[apply(perform(effcheck),tuple(relate(e),relate(v)))])$ by @relation-decomposition.

  $relate(E)^*$ contains no $handle(heffcheck,dot)$, so $effcheck in.not bop(relate(E)^*)$ and Step-E-Perform applies with the continuation $k_c = lambda x. handle(heffcheck,relate(E)^*[x])$:

  $
  e'' &estep apply(apply((lambda tuple(l,tuple(e,v)). lambda k. ife(apply(kw("wrap"),(lambda \_. apply(e,v))),apply(k,v),eblame(l))), tuple(k,tuple(relate(e),relate(v)))), k_c) & "Step-E-Perform" \
  &estep1 ife(apply(kw("wrap"),(lambda \_. apply(relate(e),relate(v)))),apply(k_c,relate(v)),blame) & "S-App" times 2 \
  &estep1 ife(handle(heffcheck,apply(relate(e),relate(v))),apply((lambda x. handle(heffcheck,relate(E)^*[x])),relate(v)),blame) = e''_2 & "by" #[@wrap-unfold]
  $

  The last line steps under the context $ife(square.stroked, e, e)$, which is an evaluation context.

  $apply(e,v)$ is not of the form $E'^*[check(k',j',e''',v')]$ (it is an application of two values), so $treq(apply(e,v),handle(heffcheck,apply(relate(e),relate(v))))$ by case 2.

  $E^*[e_4] = square.stroked[E^*[check(k,j,apply(e,v),v)]]$, so $treq(E^*[e_4],e''_2)$ by case 3 with $E^+ = square.stroked$.

- Case Check-True, $e_3 = check(k,j,trueb,v) cstepx v = e_4$

  $E^*[e_3] = E^*[check(k,j,trueb,v)]$ is of the form $E^*[ckw("check")]$, so case 2 does not apply, and by case 3 (with the outer $E^+ = square.stroked$, the only decomposition since $E^*$ contains no $ckw("check")$):

  $e'' = ife(e'_3,apply((lambda x. handle(heffcheck,relate(E)^*[x])),relate(v)),blame)$ with $treq(trueb,e'_3)$.

  $trueb$ is a value, so $e'_3 = trueb$ (case 1) or $e'_3 = handle(heffcheck,trueb)$ (case 2). In both cases $e'_3 estep1 trueb$, the latter by Step-E-Return.

  $
  e'' &estep1 ife(trueb,apply((lambda x. handle(heffcheck,relate(E)^*[x])),relate(v)),blame) \
  &estep apply((lambda x. handle(heffcheck,relate(E)^*[x])),relate(v)) & "S-If-True" \
  &estep handle(heffcheck,relate(E)^*[relate(v)]) = e''_2 & "S-App"
  $

  $E^*[e_4] = E^*[v]$ is not of the form $E'^*[ckw("check")]$ and $E^*[v] ~ relate(E)^*[relate(v)]$ by @relation-composition, so $treq(E^*[v],e''_2)$ by case 2.

- Case Check-False, $e_3 = check(k,j,falseb,v) cstepx blame(k,j) = e_4$

  Exactly as in Check-True, $e'' = ife(e'_3,apply((lambda x. handle(heffcheck,relate(E)^*[x])),relate(v)),blame)$ with $e'_3 estep1 falseb$.

  $e'' estep1 ife(falseb,dots,blame) estep blame = e''_2$ by S-If-False.

  $e_2 = E^+[E^*[blame(k,j)]]$ and $e'_2 = relate(E)^+[blame]$, so $treq(e_2,e'_2)$ by case 4. (Here we conclude directly rather than through @frame.)

- Case local redex: Mon-Guard, Guard-Func, or any rule of $langb$.

  $E^*[e_3]$ is not of the form $E'^*[ckw("check")]$, because neither $E^*$ nor a local redex contains $ckw("check")$ in evaluation position. So case 2 applies and $e'' = handle(heffcheck,relate(E)^*[relate(e)_3])$ by @relation-decomposition.

  By @local-redex, $relate(e)_3 estep1 relate(e)_4$ with $e_4 ~ relate(e)_4$, and $e_4$ contains no $ckw("check")$ or $ckw("blame")$ in evaluation position.

  Stepping under the evaluation context $handle(heffcheck,relate(E)^*)$, $e'' estep1 handle(heffcheck,relate(E)^*[relate(e)_4]) = e''_2$.

  $E^*[e_4] ~ relate(E)^*[relate(e)_4]$ by @relation-composition, and $E^*[e_4]$ is not of the form $E'^*[ckw("check")]$, so $treq(E^*[e_4],e''_2)$ by case 2.
]

#lemma(title: "Local redexes are simulated")[
  Let $e_3 cstepx e_4$ by Mon-Guard, Guard-Func, or any reduction rule of $langb$, and let $e_3 ~ relate(e)_3$. Then there is $relate(e)_4$ with $relate(e)_3 estep1 relate(e)_4$ and $e_4 ~ relate(e)_4$. Moreover $e_4$ contains no $ckw("check")$ or $ckw("blame")$ in evaluation position.
] <local-redex>

#proof[
  By case analysis on the rule. Write $m = mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x)))$, so that the function-contract rows of the relation read $mon(k,l,j,kappa_1 -> kappa_2,e) ~ apply((lambda f. lambda x. relate(m)),relate(e))$ and $guard(v,kappa_1 -> kappa_2,k,l,j) ~ lambda x. relate(m)[f:=relate(v)]$.

  - Case Mon-Guard, $mon(k,l,j,kappa_1 -> kappa_2,v) cstepx guard(v,kappa_1 -> kappa_2,k,l,j)$.

    $relate(e)_3 = apply((lambda f. lambda x. relate(m)),relate(v)) estep lambda x. relate(m)[f:=relate(v)]$ by S-App.

    $lambda x. relate(m)[f:=relate(v)] = lambda x. relw(m[f:=v])$ by @substitution, which is $relate(e)_4$ by the $ckw("guard")$ row of the value relation.

  - Case Guard-Func, $apply(guard(v_1,kappa_1 -> kappa_2,k,l,j),v_2) cstepx mon(k,l,j,kappa_2,apply(v_1,mon(l,k,j,kappa_1,v_2)))$.

    $relate(e)_3 = apply((lambda x. relate(m)[f:=relate(v)_1]),relate(v)_2) estep relate(m)[f:=relate(v)_1][x:=relate(v)_2]$ by S-App.

    By @substitution twice, this is $relw(m[f:=v_1][x:=v_2]) = relw(mon(k,l,j,kappa_2,apply(v_1,mon(l,k,j,kappa_1,v_2)))) = relate(e)_4$.

  - Case S-App, $apply((lambda x. e),v) cstepx e[x:=v]$.

    $relate(e)_3 = apply((lambda x. relate(e)),relate(v)) estep relate(e)[x:=relate(v)] = relw(e[x:=v])$ by S-App and @substitution.

  - Case SFix, $mu x. e cstepx e[x:=mu x. e]$.

    $relate(e)_3 = mu x. relate(e) estep relate(e)[x:=mu x. relate(e)] = relw(e[x:=mu x. e])$ by SFix and @substitution, using $mu x. e ~ mu x. relate(e)$.

  - Case S-If-True, S-If-False, S-Inj-Left, S-Inj-Right, and the primitive operations.

    The relation is homomorphic on these constructs and base values are related to themselves, so $relate(e)_3$ has the same head form with related operands. The same rule applies in the target and the results are related: for example $ife(trueb,e_5,e_6) ~ ife(trueb,relate(e)_5,relate(e)_6) estep relate(e)_5$, and $injl(tuple(v_1,v_2)) ~ injl(tuple(relate(v)_1,relate(v)_2)) estep relate(v)_1$.

  - Case S-New-Cell, S-Get-Cell, S-Set-Cell.

    Stores are related pointwise. The same location is chosen on both sides for $kw("new")$, $kw("get")$ reads related values, and $kw("set")$ stores related values, so the resulting stores are again related pointwise and the resulting expressions are related.

  For the last claim: $e_4$ is a value, a $ckw("mon")$ of values, or a substitution instance $e[x:=v]$ or $e[x:=mu x. e]$. Values and $ckw("mon")$ contain no $ckw("check")$ or $ckw("blame")$, and substitution places values under the binders of $e$, which by the convention above contain no $ckw("check")$ or $ckw("blame")$.
]

#lemma(title: "Substitution")[
  If $e ~ relate(e)$ and $v ~ relate(v)$ then $e[x:=v] ~ relate(e)[x:=relate(v)]$, that is, $relw(e[x:=v]) = relate(e)[x:=relate(v)]$.
] <substitution>

#proof[
  By induction on $e ~ relate(e)$. The variable row gives $x ~ x$ and both sides substitute to $v ~ relate(v)$; any other variable is unchanged on both sides. Every remaining row of the expression and value relations is homomorphic: it relates a construct to a construct with the same binding structure and related sub-terms, and substitution commutes with each of them. The two $ckw("check")$ rows do not arise, since $ckw("check")$ never occurs under a binder.
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
    [$apply((lambda f. lambda x. relate(e)_1),relate(E)^*)$],
    [],[],grid.cell(align:left,colspan:1)[$e_1=mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x)))$],

    [$ife(E^*,e_1,e_2), tuple(E^*,e), tuple(v,E^*), dots$],
    [$tilde$],
    [$ife(relate(E)^*,relate(e)_1,relate(e)_2), tuple(relate(E)^*,relate(e)), tuple(relate(v),relate(E)^*), dots$],
    [],[],grid.cell(align:left,colspan:1)[every other context frame of $langb$, homomorphically],

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

    [$x$],
    [$tilde$],
    [$x$],

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

    [$mu x. e, ife(e_1,e_2,e_3), tuple(e_1,e_2), injl(e), dots$],
    [$tilde$],
    [$mu x. relate(e), ife(relate(e)_1,relate(e)_2,relate(e)_3), tuple(relate(e)_1,relate(e)_2), injl(relate(e)), dots$],
    [],[],grid.cell(align:left,colspan:1)[every other expression form of $langb$, homomorphically],

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

    [$unit, loc$],
    [$tilde$],
    [$unit, loc$],

    [$tuple(v_1,v_2)$],
    [$tilde$],
    [$tuple(relate(v)_1,relate(v)_2)$],

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
  If $e ~ relate(e)$ and $E^* ~ relate(E)^*$ then $E^*[e] ~ relate(E)^*[relate(e)]$.
] <relation-composition>

#proof[
  By induction on $E^* ~ relate(E)^*$.

  - Case $square.stroked ~ square.stroked$. Then $E^*[e] = e ~ relate(e) = relate(E)^*[relate(e)]$.

  - Case $apply(E^*_1,e_2) ~ apply(relate(E)^*_1,relate(e)_2)$.

    By IH, $E^*_1[e] ~ relate(E)^*_1[relate(e)]$.

    $E^*[e] = apply(E^*_1[e],e_2) ~ apply(relate(E)^*_1[relate(e)],relate(e)_2) = relate(E)^*[relate(e)]$ by the application row.

  - Case $mon(k,l,j,flat(e_2),E^*_1) ~ apply(perform(effcheck),tuple(relate(e)_2,relate(E)^*_1))$.

    By IH, $E^*_1[e] ~ relate(E)^*_1[relate(e)]$.

    $E^*[e] = mon(k,l,j,flat(e_2),E^*_1[e]) ~ apply(perform(effcheck),tuple(relate(e)_2,relate(E)^*_1[relate(e)])) = relate(E)^*[relate(e)]$ by the flat row.

  - Case $mon(k,l,j,kappa_1 -> kappa_2,E^*_1) ~ apply((lambda f. lambda x. relate(e)_1),relate(E)^*_1)$.

    By IH, $E^*_1[e] ~ relate(E)^*_1[relate(e)]$.

    $E^*[e] = mon(k,l,j,kappa_1 -> kappa_2,E^*_1[e]) ~ apply((lambda f. lambda x. relate(e)_1),relate(E)^*_1[relate(e)]) = relate(E)^*[relate(e)]$ by the function row.

  - Every other frame of $langb$ has a matching homomorphic row in the expression relation and follows the same way.
]

#lemma(title: "Relation decomposes")[
  If $E^*[e] ~ e'$ and $E^*[e]$ is not of the form $E'^*[check(k,j,e'',v)]$, then $e' = relate(E)^*[relate(e)]$ for some $relate(E)^* ~ E^*$ and $relate(e) ~ e$.
] <relation-decomposition>

#proof[
  By induction on $E^*$. The two $ckw("check")$ rows are excluded by the hypothesis, and each remaining source form matches exactly one row of the expression relation: an application matches only the application row, $mon(k,l,j,flat(e),dot)$ only the flat row, $mon(k,l,j,kappa_1 -> kappa_2,dot)$ only the function row, and each base frame only its homomorphic row. That row determines the outermost frame of $e'$ and relates the sub-term in the hole, to which the IH applies.
]


#lemma(title: "Breaking down Context E")[
  For all $E$, $E = E^+[E^*]$
] <context-breakdown>

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

  Similarly to other basic cases, and to $E = mon(k,l,j,kappa,E_1)$.

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
