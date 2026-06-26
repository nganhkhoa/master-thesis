#import "@preview/great-theorems:0.1.2": *
#import "@preview/rich-counters:0.2.1": *

#import "/utils.typ": *
#import "/models/language.typ": *

#set heading(numbering: "A.1")

#show: no-ref
#show: great-theorems-init
#show link: text.with(fill: blue)

#let mathcounter = rich-counter(
  identifier: "mathblocks",
  inherited_levels: 1
)

#let theorem = mathblock(
  blocktitle: "Theorem",
  counter: mathcounter,
  numbering: "A.1"
)

#let lemma = mathblock(
  blocktitle: "Lemma",
  counter: mathcounter,
  numbering: "A.1"
)

#let remark = mathblock(
  blocktitle: "Remark",
  prefix: [_Remark._],
  inset: 5pt,
  fill: lime,
  radius: 5pt,
  numbering: "A.1"
)

#let proof = proofblock()

#let rule(r) = $mono(#r)$

= #langb Theorems

#theorem(title: [#langb Type Safety])[

- If $type(dot,e_1,tau)$ and $e_1,mtstore step e_2,store$ for some $store$ then $type(dot,e_2, tau)$.
- If $type(dot,e_1,tau)$ then $e_1$ is a value or exists $e_2,store$ such that $e_1,mtstore step e_2,store$.
] <langb-Type-Safety>


By @langb-Preservation and @langb-Progress.

#theorem(title: [#langb Type Preservation])[

If $type(dot,e_1,tau)$ and $e_1,mtstore step e_2,store$ for some $store$ then $type(dot,e_2, tau)$.
] <langb-Preservation>

#proof(of: <langb-Preservation>)[

By induction on $e_1,sigma step e_2,sigma'$.

- Case $apply(lambda x. e_3,v),store step e_3[x:=v],store$.
#make-proof(
  gap: 4em,
  (
    ( $ e_1 = apply(lambda x. e_3, v) $,          "Given"),
    ( $ e_2 = e_3[x:=v] $,                        "Given"),
    ( $ type(dot, v, tau_1) $,                    rule("Type-App")),
    ( $ type(dot, lambda x. e_3, tau_1 -> tau) $, rule("Type-App")),
    ( $ type(dot, e_3, tau_1 -> tau) $,           rule("Type-Lambda")),
    ( $ type(dot, x, tau_1) $,                    rule("Type-Lambda")),
    ( $ type(dot, e_3[x:=v], tau) $,              text()[@replace-type]),
    ( $ type(dot, e_2, tau) $,                    "" ),
  )
)

- Case $mu x. e_3, sigma step e_3[x:=mu x. e_3], sigma$
#make-proof((
  ( $ e_1 = mu x. e_3 $,                      "Given"),
  ( $ e_2 = e_3[x:=mu x. e_3] $,              "Given"),
  ( $ type(dot, e_3, tau) $,                  rule("Type-Fix")),
  ( $ type(dot, x, tau) $,                    rule("Type-Fix")),
  ( $ type(dot, e_3[x:=mu x. e_3], tau) $,    [@replace-type]),
  ( $ type(dot, e_2, tau) $,                  "" )
))

- Case $ife(trueb, e_3, e_4), sigma step e_3$
#make-proof((
  ( $ e_1 = ife(trueb, e_3, e_4) $,           "Given"),
  ( $ e_2 = e_3 $,                            "Given"),
  ( $ type(dot, e_3, tau) $,                  rule("Type-If")),
  ( $ type(dot, e_2, tau) $,                  "" )
))

- Case $ife(falseb, e_3, e_4), sigma step e_3$ similarly above.

- Case $injl(tuple(v_1, v_2)), sigma step v_1$
#make-proof((
  ( $ e_1 = injl(tuple(v_1, v_2)) $,                  "Given" ),
  ( $ e_2 = v_1 $,                                    "Given" ),
  ( $ type(dot, tuple(v_1, v_2), tuple(tau, tau_1)) $,rule("T-Inj-Left")),
  ( $ type(dot, v_1, tau) $,                          rule("T-Tuple")),
  ( $ type(dot, e_2, tau) $,                          "" )
))

- Case $injr(tuple(v_1, v_2)), sigma step v_2$ similarly above.

- Case $E[newcell(v)], sigma step E[kw("loc")], sigma[kw("loc") -> v]$
#make-proof((
  ( $ e_1 = E[newcell(v)] $,                   "Given" ),
  ( $ e_2 = E[kw("loc")] $,                    "Given" ),
  ( $ type(Gamma, E[newcell(v)], tau) $,       "Given" ),
  ( $ type(Gamma, newcell(v), tau_1) $,        [@langb-decomposition] ),
  ( $ type(Gamma, newcell(v), ref(tau_2)) $,   rule("T-New")),
  ( $ type(Gamma, kw("loc"), ref(tau_2)) $,    rule("T-Loc")),
  ( $ type(Gamma, E[kw("loc")], tau) $,        [@langb-context-replacement] ),
  ( $ type(Gamma, e_2, tau) $,                 "" )
))
]

#theorem(title: [#langb Progress])[
If $type(dot, e_1, tau)$ then $e_1$ is a value or exists $e_2, store$ such that $e_1, mtstore step e_2, store$.
] <langb-Progress>

#proof(of: <langb-Progress>)[
]

#lemma(title: [Decomposition])[
If $type(Gamma, E[e], tau)$ then exists a type $tau_1$, such that $type(Gamma, e, tau_1)$.
] <langb-decomposition>

#proof(of: <langb-decomposition>)[
]

#lemma(title: [Context Replacement])[
If $type(Gamma, E[e_1], tau)$ and $type(Gamma, e_1, tau_1)$ then for any $e_2$ such that, $type(Gamma, e_2, tau_1)$, $type(Gamma, E[e_2], tau)$.
] <langb-context-replacement>

#proof(of: <langb-context-replacement>)[
By induction on $E$.

- Case $E = apply(E_1, e_3)$
#make-proof((
  ( $ E[e_1] = (apply(E_1, e_3))[e_1] $,       "Given" ),
  ( $ E[e_1] = apply(E_1[e_1], e_3) $,         "" ),
  ( $ type(Gamma, apply(E_1[e_1], e_3), tau) $,"Given" ),
  ( $ type(Gamma, e_3, tau_2) $,               rule("Type-App") ),
  ( $ type(Gamma, E_1[e_1], tau_2 -> tau) $,   rule("Type-App") ),
  ( $ type(Gamma, E_1[e_2], tau_2 -> tau) $,   "IH" ),
  ( $ type(Gamma, apply(E_1[e_2], e_3), tau) $,rule("Type-App") ),
  ( $ type(Gamma, (apply(E_1, e_3))[e_2], tau) $,"" ),
  ( $ type(Gamma, E[e_2], tau) $,              "" )
))

- Other cases follow similarly.
]

#lemma(title: [Substitution])[
If $type(Gamma, e_1, tau_1)$ and $type(Gamma\,x:tau_1, e_2, tau_2)$ then $type(Gamma, e_2[x:=e_1], tau_2)$.
] <replace-type>

#proof(of: <replace-type>)[
]
