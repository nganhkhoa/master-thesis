#import "/setup.typ": setup-model
#show: setup-model

#import "@preview/simplebnf:0.1.2": *
#import "@preview/codly:1.3.0": *
#import "@preview/codly-languages:0.1.1": *
#import "@preview/curryst:0.6.0": rule, prooftree, rule-set
#import "@preview/great-theorems:0.1.2": *
#import "@preview/rich-counters:0.2.1": *

#import "language.typ": *

#figure(
  stack(
    spacing: 1em,
    align(left)[
      #box(
        stroke: 1pt + black,
        outset: 5pt,
        [#langc],
      )
      #h(6pt)
      extends #langb
    ],
    align(left)[*Surface syntax*],
    grid(
      columns: (auto, auto),
      bnf(
        Prod($tau$, {
          Or[$...$][]
          Or[$con(tau)$][]
        }),
        Prod($e$, {
          Or[$...$][]
          Or[$mon(k,l,j,kappa,e)$][]
        }),
      ),
      bnf(
        Prod($kappa$, {
          Or[$flat(e)$][]
          Or[$kappa -> kappa | dep(kappa,lambda x: tau. kappa)$][]
        }),
      ),
    ),
    align(left)[*Evaluation syntax*],
    grid(
      columns: (auto, auto),
      bnf(
        Prod($e$, {
          Or[$...$][]
          Or[$check(k,j,e,v)$][]
          Or[$blame(k,j)$][]
        }),
        Prod($v$, {
          Or[$...$][]
          Or[$guard(v,kappa,k,l,j)$][]
        }),
      ),
      bnf(
        Prod($E$, {
          Or[$...$][]
          Or[$mon(k,l,j,kappa,E)$][]
          Or[$check(k,j,E,v)$][]
        }),
      ),
    ),
    v(1em),
  ),
  caption: [#langc language]
) <contracts-syntax>
