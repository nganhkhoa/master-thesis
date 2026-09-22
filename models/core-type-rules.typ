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
        $type(Gamma | Sigma, n, numt)$
      )),
      prooftree(rule(
        name: [T-Bool],
        $type(Gamma | Sigma, b, boolt)$
      )),
      prooftree(rule(
        name: [T-Tuple],
        $type(Gamma | Sigma, e_1, tau_1)$,
        $type(Gamma | Sigma, e_2, tau_2)$,
        $type(Gamma | Sigma, tuple(e_1,e_2), tuple(tau_1,tau_2))$
      )),
      prooftree(rule(
        name: [T-Var],
        $x : tau in Gamma$,
        $type(Gamma | Sigma, x, tau)$
      )),
      prooftree(rule(
        name: [T-Lambda],
        $type(Gamma\, x : tau_1 | Sigma, e, tau_2)$,
        $type(Gamma | Sigma, lambda x : tau_1. e, tau_1 -> tau_2)$
      )),
      prooftree(rule(
        name: [T-Fix],
        $type(Gamma\, x : tau | Sigma, e, tau)$,
        $type(Gamma | Sigma, mu x : tau. e, tau)$
      )),
      prooftree(rule(
        name: [T-App],
        $type(Gamma | Sigma, e_1, tau_1 -> tau_2)$,
        $type(Gamma | Sigma, e_2, tau_1)$,
        $type(Gamma | Sigma, apply(e_1,e_2), e_2)$
      )),
      prooftree(rule(
        name: [T-If],
        $type(Gamma | Sigma, e_1, boolt)$,
        $type(Gamma | Sigma, e_2, tau)$,
        $type(Gamma | Sigma, e_3, tau)$,
        $type(Gamma | Sigma, ife(e_1,e_2,e_3), tau)$
      )),
      prooftree(rule(
        name: [T-Zero],
        $type(Gamma | Sigma, e, numt)$,
        $type(Gamma | Sigma, iszero(e), boolt)$
      )),

      prooftree(rule(
        name: [T-Inj-Left],
        $type(Gamma | Sigma, e, tuple(tau_1,tau_2))$,
        $type(Gamma | Sigma, injl(e), tau_1)$
      )),
      prooftree(rule(
        name: [T-Inj-Right],
        $type(Gamma | Sigma, e, tuple(tau_1,tau_2))$,
        $type(Gamma | Sigma, injr(e), tau_2)$
      )),

      prooftree(rule(
        name: [T-New-Cell],
        $type(Gamma | Sigma, e, tau)$,
        $type(Gamma | Sigma, newcell(e), ref(tau))$
      )),
      prooftree(rule(
        name: [T-Get-Cell],
        $type(Gamma | Sigma, e, ref(tau))$,
        $type(Gamma | Sigma, getcell(e), tau)$,
      )),
      prooftree(rule(
        name: [T-Get-Cell],
        $type(Gamma | Sigma, e_1, ref(tau))$,
        $type(Gamma | Sigma, e_2, tau)$,
        $type(Gamma | Sigma, setcell(e_1,e_2), ref(tau))$,
      )),
    ),
    v(2em),
  ),
  caption: [Type Rules for #langb]
) <core-type-rules>

