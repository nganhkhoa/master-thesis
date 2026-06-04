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
        [#lange],
      )
      #h(6pt)
      extends #langb
    ],
    grid(
      columns: (auto, auto),
      bnf(
        Prod($tau$, {
          Or[$...$][]
          Or[$alpha^k | c^k tau ... | teff(tau,epsilon,tau) | forall alpha^k. tau$][]
          Or[$#blab$][]
        }),
        Prod($k$, {
          Or[$*$][]
          Or[$k -> k$][]
          Or[$#eff$][]
          Or[$#lab$][]
        }),
        Prod($e$, {
          Or[$...$][]
          Or[$e[tau]$][]
          Or[$handle(h, e)$][]
          Or[$eblame(e)$][]
        }),
        Prod($h$, {
          Or[${op -> f, ..., }$][]
        }),
        Prod($f$, {
          Or[$Lambda alpha. lambda x : tau. lambda k : tau. e$][]
        }),
      ),
      bnf(
        Prod($v$, {
          Or[$...$][]
          Or[$Lambda alpha^k. v$][]
          Or[$handler(h)$][]
          Or[$perform(op,tau)$][]
          Or[$eblame(p)$][]
        }),
        Prod($p$, {
          Or[Blame Party][]
        }),
        Prod($E$, {
          Or[$...$][]
          Or[$E[tau]$][]
          Or[$handle(h, E)$][]
          Or[$eblame(E)$][]
        }),
        Prod($F$, {
          Or[$square.stroked$][]
          Or[$F + e | v + F | F - e | v - F $][]
          Or[$F and e | v and F | F or e | v or F$][]
          Or[$apply(F, e) | apply(v, F)$][]
          Or[$ife(F, e, e)$][]
          Or[$F[tau]$][]
        }),
      ),
    ),
    v(1em),
  ),
  caption: [#lange language]
) <effects-syntax>
