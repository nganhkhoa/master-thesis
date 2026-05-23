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
      [$apply(lambda x. e, v)$], [$step$], [$e[x:=v]$], [S-App],
      [$mu x. e$], [$step$], [$e[x:=mu x. e]$], [SFix],
      [$ife(trueb, e_1,e_2)$], [$step$], [$e_1$], [S-If-True],
      [$ife(falseb, e_1,e_2)$], [$step$], [$e_2$], [S-If-False],
      [$injl(tuple(v_1,v_2))$], [$step$], [$v_1$], [S-Inj-Left],
      [$injr(tuple(v_1,v_2))$], [$step$], [$v_2$], [S-Inj-Right],
    ),
    v(2em),
    line(length: 100%),
    [not really correct, maybe use different arrow],
    v(2em),
    rule-set(
      prooftree(rule(
        name: [Step],
        $e_1 step e_2$,
        $E[e_1], sigma step E[e_2], sigma$
      )),
      prooftree(rule(
        name: [S-New-Cell],
        $kw("loc") in.not sigma$,
        $E[newcell(v)], sigma step E[kw("loc")], sigma[kw("loc") -> v]$
      )),
      prooftree(rule(
        name: [S-Get-Cell],
        $E[getcell(kw("loc"))], sigma step E[v], sigma$
      )),
      prooftree(rule(
        name: [S-Set-Cell],
        $kw("loc") in sigma$,
        $E[setcell(kw("loc"),v)], sigma step E[kw("loc")], sigma[kw("loc") -> v]$
      )),
    ),
    v(1em),
  ),
  caption: [Reduction Rules for #langb]
) <core-reduction-rules>

