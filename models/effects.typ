#import "/setup.typ": setupdoc
#show: setupdoc

#import "@preview/simplebnf:0.1.2": *
#import "@preview/codly:1.3.0": *
#import "@preview/codly-languages:0.1.1": *
#import "@preview/curryst:0.6.0": rule, prooftree, rule-set
#import "@preview/great-theorems:0.1.2": *
#import "@preview/rich-counters:0.2.1": *

#import "language.typ": *

#let lam = [lambda]
#let hdl = [handler]
#let hnd = [handle]
#let prf = [perform]
#let mode = $m in {d, s}$

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
        Prod($m$, {
          Or[$d$][]
          Or[$s$][]
        }),
        Prod($e$, {
          Or[$...$][]
          Or[$lambda^epsilon x : tau. e$][]
          Or[$e[tau]$][]
          Or[$handle(h, e, m: m)$][]
          Or[$eblame(p)$][]
        }),
        Prod($h$, {
          Or[${op -> f, ..., }$][]
        }),
        Prod($f$, {
          Or[$Lambda alpha. lambda^epsilon x : tau_1.
              lambda^epsilon k : (tau_2 attach(->, tr: epsilon) tau). e$][]
        }),
      ),
      bnf(
        Prod($l$, {
          Or[Error Label][]
        }),
        Prod($v$, {
          Or[$...$][]
          Or[$lambda^epsilon x : tau. e$][]
          Or[$Lambda alpha^k. v$][]
          Or[$handler(h, m: m, eff: epsilon)$][]
          Or[$perform(op, tau: tau, eff: epsilon)$][]
          Or[$eblame(l)$][]
        }),
        Prod($E$, {
          Or[$...$][]
          Or[$E[tau]$][]
          Or[$handle(h, E, m: m, eff: epsilon)$][]
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
