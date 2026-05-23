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
        name: [Type-C-Flat],
        $type(Gamma, e, tau -> boolt)$,
        $type(Gamma, flat(e), con(tau))$
      )),
      prooftree(rule(
        name: [Type-C-Fun],
        $type(Gamma, kappa_1, con(tau_1))$,
        $type(Gamma, kappa_2, con(tau_2))$,
        $type(Gamma, kappa_1 -> kappa_2, con(tau_1 -> tau_2))$
      )),
      prooftree(rule(
        name: [Type-C-DepFun],
        $type(Gamma, kappa_1, con(tau_1))$,
        $type(Gamma, lambda x : tau_1. kappa_2, tau_1 -> con(tau_2))$,
        $type(Gamma, dep(kappa_1, lambda x. kappa_2), con(tau_1 -> tau_2))$
      )),
      prooftree(rule(
        name: [Type-C-Ref],
        $type(Gamma, kappa, con(tau))$,
        $type(Gamma, refc(kappa), con(ref(tau)))$
      )),
      prooftree(rule(
        name: [Type-C-Tuple],
        $type(Gamma, kappa_1, con(tau_1))$,
        $type(Gamma, kappa_2, con(tau_2))$,
        $type(Gamma, tuple(kappa_1,kappa_2), con(tuple(tau_1,tau_2)))$
      )),
      prooftree(rule(
        name: [Type-C-Mon],
        $type(Gamma, kappa, con(tau))$,
        $type(Gamma, e, tau)$,
        $type(Gamma, mon(k,l,j,kappa,e), tau)$
      )),
      prooftree(rule(
        name: [Type-C-Blame],
        $type(Gamma, blame(k,l), tau)$
      )),
    ),
    v(2em),
  ),
  caption: [Type Rules for #langc]
) <contracts-type-rules>
