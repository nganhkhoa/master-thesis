#import "/setup.typ": setupdoc
#show: setupdoc

#import "@preview/simplebnf:0.1.2": *
#import "@preview/codly:1.3.0": *
#import "@preview/codly-languages:0.1.1": *
#import "@preview/curryst:0.6.0": rule, prooftree, rule-set
#import "@preview/great-theorems:0.1.2": *
#import "@preview/rich-counters:0.2.1": *

#import "language.typ": *

#figure(
  stack(
    grid(
      columns: (auto,auto,auto, auto),
      gutter: 1.5em,
      [$apply(lambda x. e, v)$], [$stepx$], [$e[x:=v]$], [S-App],
      [$mu x. e$], [$stepx$], [$e[x:=mu x. e]$], [S-Fix],
      [$ife(trueb, e_1,e_2)$], [$stepx$], [$e_1$], [S-If-True],
      [$ife(falseb, e_1,e_2)$], [$stepx$], [$e_2$], [S-If-False],
      [$injl(tuple(v_1,v_2))$], [$stepx$], [$v_1$], [S-Inj-Left],
      [$injr(tuple(v_1,v_2))$], [$stepx$], [$v_2$], [S-Inj-Right],
      [$v_1 o v_2$], [$stepx$], [$delta(o, v_1, v_2)$], [S-Op],
      [$iszero(n)$], [$stepx$], [$b$], [S-Zero],
    ),
    v(2em),
    line(length: 100%),
    v(2em),
    rule-set(
      prooftree(rule(
        name: [Step],
        $e_1 stepx e_2$,
        $E[e_1] step E[e_2]$
      )),
    ),
    v(1em),
  ),
  caption: [Reduction Rules for #langb]
) <base-reduction-rules>

