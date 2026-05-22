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
      columns: (auto, 1fr, auto, auto),
      gutter: 1.5em,
      [$check(k, j, "tt", v)$], [$cstep$], [$v$], [Check-True],
      [$check(k, j, "ff", v)$], [$cstep$], [$blame(k,j)$], [Check-False],

      [$guard(flat(e),v,k,l,j)$], [$cstep$], [$check(k, j, apply(e, v), v)$], [Mon-Flat],

      [$apply(guard(kappa_1 -> kappa_2,v_1,k,l,j),v_2)$], [$cstep$], [$mon(k,l,j,kappa_2,apply(v_1, mon(l,k,j,kappa_1,v_2)))$], [Guard-Func],

      [$apply(guard(kappa_1 ->^d (lambda x. kappa_2),v_1,k,l,j),v_2)$], [$cstep$],
      [$mon(k,l,j, kappa'_2, apply(v_1, mon(k,l,j,kappa_1,v_2)))$],
      [Mon-Dep],

      [],[],grid.cell(colspan: 2, align: right, [where $kappa'_2 = {mon(l,j,j,kappa_1,v_2)\/x}kappa_2$],),

      [$mon(k,l,j,tuple(kappa_1,kappa_2),tuple(v_1,v_2))$], [$cstep$], [$tuple(mon(k,l,j,kappa_1,v_1), mon(k,l,j,kappa_2,v_2))$], [Mon-Tuple],
      [$mon(k,l,j,refc(kappa),v)$], [$cstep$], [$guard(v, kappa, k,l,j)$], [Mon-Cell],
      [$getcell(guard(v,kappa,k,l,j))$], [$cstep$], [$mon(k,l,j,kappa,getcell(v))$], [Mon-Get],
      [$setcell(guard(v_1,kappa,k,l,j),v_2)$], [$cstep$], [$mon(k,l,j,refc(kappa), setcell(v_1, mon(l,k,j,kappa,v_2)))$], [Mon-Set],
    ),
    v(2em),
    rule-set(
      prooftree(rule(
        name: [Blame],
        $E != square.stroked$,
        $E[blame(k, j)] estep blame(k, j)$
      )),
    ),
    v(1em),
  ),
  caption: [Reduction Rules for #langc]
) <contracts-reduction-rules>
