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
        [#langb],
      )
    ],
    grid(
      columns: (auto, auto),
      bnf(
        Prod($tau$, {
          Or[$o$][]
          Or[$tau -> tau$][]
          Or[$tuple(tau,tau)$][]
          Or[$ref(tau)$][]
        }),
        Prod($e$, {
          Or[$0 | -1 | 1 | ... | "tt" | "ff" | "x"$][]
          Or[$lambda x : tau . e | mu x : tau . e | kw("loc")$][]
          Or[$e + e | e - e | e and e | e or e$][]
          Or[$apply(e, e) | ife(e, e, e)$][]
          Or[$iszero(e)$][]
          Or[$injl(e) | injr(e)$][]
          Or[$newcell(e) | getcell(e) | setcell(e,e)$][]
        }),
      ),
      bnf(
        Prod($o$, {
          Or[num][]
          Or[bool][]
        }),
        Prod($v$, {
          Or[$0 | -1 | 1 | ... | "tt" | "ff" | "x"$][]
          Or[$lambda x. e | kw("loc")$][]
        }),
        Prod($E$, {
          Or[$square.stroked$][]
          Or[$E + e | v + E | E - e | v - E$][]
          Or[$E and e | v and E | E or e | v or E$][]
          Or[$apply(E, e) | apply(v, E) | ife(E, e, e) | iszero(E)$][]
          Or[$injl(E) | injr(E)$][]
          Or[$newcell(E) | getcell(E) | setcell(E,e) | setcell(v,E)$][]
        }),
      ),
    ),
    v(1em),
  ),
  caption: [#langb Language]
) <core-syntax>
