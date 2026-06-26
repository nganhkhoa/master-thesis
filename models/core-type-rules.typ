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
        name: [T-Num],
        $type(Gamma, n, numt)$
      )),
      prooftree(rule(
        name: [T-Bool],
        $type(Gamma, b, boolt)$
      )),
      prooftree(rule(
        name: [T-Tuple],
        $type(Gamma, e_1, tau_1)$,
        $type(Gamma, e_2, tau_2)$,
        $type(Gamma, tuple(e_1,e_2), tuple(tau_1,tau_2))$
      )),
      prooftree(rule(
        name: [T-Var],
        $x : tau in Gamma$,
        $type(Gamma, x, tau)$
      )),
      prooftree(rule(
        name: [T-Lambda],
        $type(Gamma\, x : tau_1, e, tau_2)$,
        $type(Gamma, lambda x : tau_1. e, tau_1 -> tau_2)$
      )),
      prooftree(rule(
        name: [T-Fix],
        $type(Gamma\, x : tau, e, tau)$,
        $type(Gamma, mu x : tau. e, tau)$
      )),
      prooftree(rule(
        name: [T-App],
        $type(Gamma, e_1, tau_1 -> tau_2)$,
        $type(Gamma, e_2, tau_1)$,
        $type(Gamma, apply(e_1,e_2), e_2)$
      )),
      prooftree(rule(
        name: [T-If],
        $type(Gamma, e_1, boolt)$,
        $type(Gamma, e_2, tau)$,
        $type(Gamma, e_3, tau)$,
        $type(Gamma, ife(e_1,e_2,e_3), tau)$
      )),
      prooftree(rule(
        name: [T-Zero],
        $type(Gamma, e, numt)$,
        $type(Gamma, iszero(e), boolt)$
      )),

      prooftree(rule(
        name: [T-Inj-Left],
        $type(Gamma, e, tuple(tau_1,tau_2))$,
        $type(Gamma, injl(e), tau_1)$
      )),
      prooftree(rule(
        name: [T-Inj-Right],
        $type(Gamma, e, tuple(tau_1,tau_2))$,
        $type(Gamma, injr(e), tau_2)$
      )),

      prooftree(rule(
        name: [T-New-Cell],
        $type(Gamma, e, tau)$,
        $type(Gamma, newcell(e), ref(tau))$
      )),
      prooftree(rule(
        name: [T-Get-Cell],
        $type(Gamma, e, ref(tau))$,
        $type(Gamma, getcell(e), tau)$,
      )),
      prooftree(rule(
        name: [T-Get-Cell],
        $type(Gamma, e_1, ref(tau))$,
        $type(Gamma, e_2, tau)$,
        $type(Gamma, setcell(e_1,e_2), ref(tau))$,
      )),
    ),
    v(2em),
  ),
  caption: [Type Rules for #langb]
) <core-type-rules>

