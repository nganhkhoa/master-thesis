#import "@preview/simplebnf:0.1.2": *
#import "@preview/codly:1.3.0": *
#import "@preview/codly-languages:0.1.1": *
#import "@preview/curryst:0.6.0": rule, prooftree, rule-set
#import "@preview/great-theorems:0.1.2": *
#import "@preview/rich-counters:0.2.1": *

#import "language.typ": *

#figure(
  grid(
    columns: 2,
    column-gutter: 2em,
    row-gutter: 3em,
    align: center + horizon,

    // Row 1
    prooftree(rule(
      name: "T-E-Var",
      $x : tau in Gamma$,
      type($Gamma$, $x$, $tau$, type: "val", eff: []),
    )),

    prooftree(rule(
      name: "T-E-App",
      type($Gamma\,x:tau_1$, $e$, $tau_2$, eff: $epsilon$),
      type($Gamma$, $lambda x:tau_1 . e$, $tau_1 attach(->, tr: epsilon) tau_2$, type: "val", eff: []),
    )),

    // Row 2
    prooftree(rule(
      name: "T-E-Val",
      type($Gamma$, $v$, $tau$, type: "val", eff: []),
      type($Gamma$, $v$, $tau$, eff: $epsilon$),
    )),

    prooftree(rule(
      name: "T-E-TAbs",
      $k != lab$,
      type($Gamma$, $v$, $tau$, type: "val", eff: []),
      type($Gamma$, $Lambda alpha^k . v$, $forall alpha^k . tau$, type: "val", eff: []),
    )),

    // Row 3
    prooftree(rule(
      name: "T-E-App",
      type($Gamma$, $e_1$, $teff(tau_1,epsilon,tau_2)$, eff: $epsilon$),
      type($Gamma$, $e_2$, $tau_1$, eff: $epsilon$),
      type($Gamma$, $apply(e_1,e_2)$, $tau$, eff: $epsilon$),
    )),

    prooftree(rule(
      name: "T-E-Tapp",
      $attach(tack.r.short, br: "wf") tau : k$,
      type($Gamma$, $e$, $forall alpha^k . tau_1$, eff: $epsilon$),
      type($Gamma$, $e[tau]$, $tau_1[alpha:=tau]$, eff: $epsilon$),
    )),

    // Row 4
    grid.cell(colspan: 2, prooftree(rule(
      name: "T-E-Perform",
      $op : forall alpha . tau_1 -> tau_2 in Sigma(l)$,
      $alpha in.not "ftv"(Gamma)$,
      type($Gamma$, $ekw("perform") op tau$, $teff(tau_1[alpha:=tau],chevron.l l|epsilon chevron.r,tau_2[alpha:=tau])$, type: "val", eff: []),
    ))),

    // Row 5
    grid.cell(colspan: 2, prooftree(rule(
      name: "T-E-Ops",
      $op_i : forall alpha . tau_1 -> tau_2 in Sigma(l)$,
      $alpha in.not "ftv"(epsilon,tau)$,
      type($Gamma$, $f_i$, $forall alpha . teff(tau_1,epsilon,(teff((teff(tau_2,epsilon,tau)), epsilon, tau)))$, type: "val", eff: []),
      type($Gamma$, ${op_1 -> f_1, dots, op_n -> f_n}$, $tau$, type: "ops", eff: $l | epsilon$),
    ))),

    // Row 6
    grid.cell(colspan: 2, prooftree(rule(
      name: "T-E-Handler",
      type($Gamma$, $h$, $tau$, type: "ops", eff: $l | epsilon$),
      type($Gamma$, $handler(h)$, $teff((teff(unit,chevron.l l|epsilon chevron.r,tau)),epsilon,tau)$, type: "val", eff: []),
    ))),

    // Row 7
    grid.cell(colspan: 2, prooftree(rule(
      name: "T-E-Handle",
      type($Gamma$, $h$, $tau$, type: "ops", eff: $l | epsilon$),
      type($Gamma$, $e$, $tau$, eff: $chevron.l l|epsilon chevron.r$),
      type($Gamma$, $handle(h,e)$, $tau$, eff: $epsilon$),
    )))
  ),
  caption: [Type Rules for #lange]
) <effects-type-rules>
