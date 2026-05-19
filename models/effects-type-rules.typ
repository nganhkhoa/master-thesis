#import "@preview/simplebnf:0.1.2": *
#import "@preview/codly:1.3.0": *
#import "@preview/codly-languages:0.1.1": *
#import "@preview/curryst:0.6.0": rule, prooftree, rule-set
#import "@preview/great-theorems:0.1.2": *
#import "@preview/rich-counters:0.2.1": *

#import "language.typ": *

#figure(
  stack(
    rule-set(
      prooftree(rule(
        name: [SomeRule],
        $...$,
        $...$
      )),
    ),
    v(2em),
  ),
  caption: [Type Rules for #lange]
) <effects-type-rules>

