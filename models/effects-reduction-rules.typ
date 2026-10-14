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

#figure(
  stack(
    grid(
      columns: (auto,auto,auto, auto),
      gutter: 1.5em,
      [$(Lambda alpha^k. v)[tau]$], [$estepx$], [$v[alpha:=tau]$], [Step-E-TApp],
      [$apply(#ekw("handler")^epsilon(h), v)$],[$estepx$],[$#ekw("handle")^epsilon(h,(apply(v,())))$], [Step-E-Handler],
      [$#ekw("handle")^epsilon(h,v)$],[$estepx$],[$v$], [Step-E-Return],
    ),
    v(2em),
    rule-set(
      prooftree(rule(
        name: [Step-E-Perform],
        $op in.not bop(E) and (op -> f) in h$,
        $op : forall alpha. tau_1 -> tau_2 in Sigma(l)$,
        $k = #kw("lambda")^epsilon x : tau_2[alpha:=tau] . #ekw("handle")^epsilon(h, E[x])$,
        $#ekw("handle")^epsilon(h, E[apply(#ekw("perform")^epsilon_p(op, tau: tau), v)]) quad estepx quad apply(apply(f[tau], v), k)$
      )),
    ),
    v(2em),
    rule-set(
      prooftree(rule(
        name: [Step-E-Error],
        $E != square.stroked$,
        $E[eblame(p)], sigma estep eblame(p), sigma$
      )),
      prooftree(rule(
        name: [Step-E],
        $e_1 estepx e_2$,
        $E[e_1], sigma estep E[e_2], sigma$
      )),
    ),
    v(2em),
    [*Helper functions*],
    v(1em),
    grid(
      columns: (auto,auto,auto),
      gutter: 1.5em,
      [$bop(square.stroked)$], [$=$], [$diameter$],
      [$bop(apply(E,e))$], [$=$], [$bop(E)$],
      [$colon.tri$], [$colon.tri$], [$colon.tri$],
      [$bop(#ekw("handle")^epsilon(h,E))$],[$=$], [$bop(E) union {op | (op -> f) in h}$],
    ),
    v(1em),
  ),
  caption: [Reduction Rules for #lange]
) <effects-reduction-rules>
