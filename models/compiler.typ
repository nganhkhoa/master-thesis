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
        name: [Compile-Flat],
        $compile(type(Gamma,e_1,tau -> boolt), e_3)$,
        $compile(type(Gamma,e_2,tau), e_4)$,
        $compile(type(Gamma,mon(k,l,j,flat(e_1),e_2),tau), apply(perform(effcheck, tau), tuple(k, tuple(e_3, e_4))))$,
      )),
      prooftree(rule(
        name: [Compile-Func],
        $x in.not Gamma$,
        $compile(type(Gamma\,x:tau_1,mon(k,l,j,kappa_2,apply(e,x)),tau_2), e_1)$,
        $compile(type(Gamma\,x:tau_1,mon(l,k,j,kappa_1,x),tau_1),e_2)$,
        $e_3 = e_1[x:=e_2]$,
        $compile(type(Gamma,mon(k,l,j,kappa_1->kappa_2,e),tau_1 -> tau_2),lambda x: tau_1. e_3)$,
      )),
      prooftree(rule(
        name: [Compile-Dep],
        $x,x_kappa in.not Gamma$,
        $compile(type(Gamma\,x:tau_1,mon(l,k,j,kappa_1,x),tau_1),e_1)$,
        $compile(type(Gamma\,x:tau_1,mon(l,j,j,kappa_1,x),tau_1),e_2)$,
        $kappa_3 = {x_kappa\/x}kappa_2$,
        $compile(type(Gamma\,x:tau_1,mon(k,l,j,kappa_3,apply(e,x_1)),tau_2), e_3)$,
        $e_4 = e_3[x_kappa:=e_2]$,
        $#v(4em)compile(type(Gamma,mon(k,l,j,kappa_1->^d lambda x. kappa_2,e),tau_1 -> tau_2),lambda x: tau_1. e_4)$,
      )),
      prooftree(rule(
        name: [Compile-Tuple],
        $x in.not Gamma$,
        $compile(type(Gamma\,x:tuple(tau_1,tau_2),mon(k,l,j,kappa_1,injl(x)),tau_1), e_1)$,

        $compile(type(Gamma\,x:tuple(tau_1,tau_2),mon(k,l,j,kappa_2,injr(x)),tau_2), e_2)$,
        $compile(type(Gamma,e,tuple(tau_1,tau_2)),e_3)$,
        $compile(type(Gamma,mon(k,l,j,tuple(kappa_1,kappa_2),e),tuple(tau_1,tau_2)), apply((lambda x. tuple(e_1,e_2)),e_3))$,
      )),
    ),
    v(2em),
    line(length: 100%),
    v(2em),
    grid(
      columns: (auto,auto,auto),
      gutter: 1.5em,

      [$heffcheck : lab$],
      [$=$],
      grid.cell(align: left,
        [${effcheck -> forall alpha. tuple(blab, tuple(alpha -> boolt, alpha)) -> alpha}$]),

      [$kw("wrap")$], [$=$],
      grid.cell(align: left,
        [$mu w : forall alpha. ((teff((), chevron.l heffcheck chevron.r, alpha)) -> alpha). Lambda alpha. med lambda f: (teff((),chevron.l heffcheck chevron.r,alpha)).$]
      ),

      [], [],
      [$apply(handler({effcheck -> lambda tuple(l,tuple(e,v)). lambda k. ife(apply(w[kw("bool")], (lambda \_. apply(e,v))),apply(k,v),eblame(l))}), f)$],
      [], grid.cell(colspan: 2, align: right,
        [where $lambda tuple(l,tuple(e,v))$ deconstructs the argument as tuple pattern]),
    ),
    v(2em),
  ),
  caption: [Compiler Rules]
) <compiler-rules>
