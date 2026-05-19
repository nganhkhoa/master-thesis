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
      [$guard(v, "tt", k, l, j)$], [$cstep$], [$v$], [Guard-True],
      [$guard(v, "ff", k, l, j)$], [$cstep$], [$blame(k,j)$], [Guard-False],
      [$guard(v, kappa_1->kappa_2,k,l,j)$], [$cstep$], [$lambda x. mon(k,l,j, kappa_2, apply(v, mon(l,k,j,kappa_1,x)))$], [Guard-Func],
      [$guard(v, kappa_1 ->^d (lambda x : tau. kappa_2),k,l,j)$], [$cstep$],
      [$
      &"let" x_1 = mon(l,k,j,kappa_1,x) \
      &"let" x_2 = mon(l,j,j,kappa_1,x) \
      &lambda x. mon(k,l,j, {x_2\/x}kappa_2, apply(v, x_1))
      $], [Guard-Dep],

      [$mon(k,l,j,flat(e),v)$], [$cstep$], [$guard(v, apply(e, v), k, l, j)$], [Mon-Flat],
      [$mon(k,l,j,kappa_1 -> kappa_2,v)$], [$cstep$], [$guard(v, kappa_1->kappa_2,k,l,j)$], [Mon-Func],
      [$mon(k,l,j,kappa_1 ->^d (lambda x : tau. kappa_2),v)$], [$cstep$], [$guard(v, kappa_1->^d (lambda x : tau . kappa_2),k,l,j)$], [Mon-Dep],

      [$mon(k,l,j,tuple(kappa_1,kappa_2),tuple(v_1,v_2))$], [$cstep$], [$tuple(mon(k,l,j,kappa_1,v_1), mon(k,l,j,kappa_2,v_2))$], [Mon-Tuple],
      [$mon(k,l,j,refc(kappa),v)$], [$cstep$], [$guard(v, kappa, k,l,j)$], [Mon-Cell],
      [$getcell(guard(v,kappa,k,l,j))$], [$cstep$], [$mon(k,l,j,kappa,getcell(v))$], [Mon-Get],
      [$setcell(guard(v_1,kappa,k,l,j),v_2)$], [$cstep$], [$apply(lambda x . mon(k,l,j,refc(kappa), setcell(v_1, mon(l,k,j,kappa,x))), v_2)$], [Mon-Set],
    ),
    v(2em),
    rule-set(
      prooftree(rule(
        name: [Blame],
        $E != square.stroked$,
        $E[blame(l, p)] estep blame(l, p)$
      )),
    ),
    v(1em),
  ),
  caption: [Reduction Rules for #langc]
) <contracts-reduction-rules>
