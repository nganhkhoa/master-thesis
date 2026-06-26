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
      [$check(k, j, "tt", v)$], [$cstepx$], [$v$], [Check-True],
      [$check(k, j, "ff", v)$], [$cstepx$], [$blame(k,j)$], [Check-False],

      [$mon(k,l,j,flat(e),v)$],[$cstepx$],[$check(k, j, apply(e, v), v)$],[Mon-Flat],
      [$mon(k,l,j,kappa,v)$],[$cstepx$],[$guard(v,kappa,k,l,j)$],[Mon-Guard],
      [],[],grid.cell(colspan: 2, align: right, [where $kappa != flat(e)$],),

      [$apply(guard(v_1,kappa_1 -> kappa_2,k,l,j),v_2)$], [$cstepx$], [$mon(k,l,j,kappa_2,apply(v_1, mon(l,k,j,kappa_1,v_2)))$], [Guard-Func],

      [$apply(guard(v_1,dep(kappa_1, lambda x. kappa_2),k,l,j),v_2)$], [$cstepx$],
      [$mon(k,l,j, kappa_3, apply(v_1, mon(k,l,j,kappa_1,v_2)))$],
      [Guard-Dep],
      [],[],grid.cell(colspan: 2, align: right, [where $kappa_3 = {mon(l,j,j,kappa_1,v_2)\/x}kappa_2$],),


      [$injl(guard(tuple(v_1,v_2),tuple(kappa_1,kappa_2),k,l,j))$],[$cstepx$],[$guard(v_1,kappa_1,k,l,j)$],[Guard-Inj-Left],
      [$injr(guard(tuple(v_1,v_2),tuple(kappa_1,kappa_2),k,l,j))$],[$cstepx$],[$guard(v_2,kappa_2,k,l,j)$],[Guard-Inj-Right],

      [$getcell(guard(v,kappa,k,l,j))$], [$cstepx$], [$mon(k,l,j,kappa,getcell(v))$], [Mon-Get],
      [$setcell(guard(v_1,kappa,k,l,j),v_2)$], [$cstepx$], [$mon(k,l,j,refc(kappa), e)$], [Mon-Set],

      [],[],grid.cell(colspan: 2, align: right, [where $e = setcell(v_1, mon(l,k,j,kappa,v_2))$]),
    ),
    v(2em),
    rule-set(
      prooftree(rule(
        name: [Step-C-Blame],
        $E != square.stroked$,
        $E[blame(k,j)], sigma cstep blame(k,j), sigma$
      )),
      prooftree(rule(
        name: [Step-C],
        $e_1 cstepx e_2$,
        $E[e_1], sigma cstep E[e_2], sigma$
      )),
    ),
    v(1em),
  ),
  caption: [Reduction Rules for #langc]
) <contracts-reduction-rules>
