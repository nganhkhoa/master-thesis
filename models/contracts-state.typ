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
        [$langcs$],
      )
      #h(6pt)
      extends #langc
    ],
    grid(
      columns: (auto, auto, auto),
      bnf(
        Prod($e^scr("S")$, {
          Or[$...$][]
          Or[$getstate() | modifystate(op, e)$][]
        }),
      ),
      bnf(
        Prod($kappa$, {
          Or[$...$][]
          Or[$flat(e^scr("S"))$][]
        }),
      ),
      bnf(
        Prod($sigma^scr("S")$, {
          Or[Contract State][]
        }),
      ),
    ),
    v(1em),
  ),
  caption: [#langcs language]
) <contracts-state-syntax>

