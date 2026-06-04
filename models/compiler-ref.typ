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
        name: [Compile-New],
        $compile(type(Gamma,e, tau), e_1)$,
        $compile(type(Gamma,newcell(e),ref(tau)), newcell1(e_1))$,
      )),
      prooftree(rule(
        name: [Compile-Get],
        $compile(type(Gamma,e, ref(tau)), e_1)$,
        $compile(type(Gamma,getcell(e),tau), getcell1(e_1))$,
      )),
      prooftree(rule(
        name: [Compile-Get],
        $compile(type(Gamma,e_1, ref(tau)), e_3)$,
        $compile(type(Gamma,e_2, tau), e_4)$,
        $compile(type(Gamma,setcell(e_1,e_2),tau), setcell1(e_3,e_4))$,
      )),
      prooftree(rule(
        name: [Compile-Mon-Ref],
        $x in.not Gamma$,
        $compile(type(Gamma\,x:tuple(unit -> tau, tau -> kw("loc")),mon(k,l,j,tuple("any" -> kappa,kappa -> "any"), x), tuple(unit -> tau, tau -> kw("loc"))), e_1)$,
        $compile(type(Gamma,e,ref(tau)),e_2)$,
        $e_3 = e_1[x:=e_2]$,
        $compile(type(Gamma,mon(k,l,j,refc(kappa),e),ref(tau)), e_3)$,
      )),
    ),
    v(2em),
    line(length: 100%),
    v(2em),
    grid(
      columns: (auto, auto, auto),
      align: (left, center, left),
      gutter: 1em,

      [$newcell$], [$=$], [$lambda v. apply((lambda l. tuple(lambda \_. getcell(l),lambda \v. setcell(l, v))), newcell(v))$],
      [$getcell$], [$=$], [$lambda b. apply(injl(b), unit)$],
      [$setcell$], [$=$], [$lambda b. lambda v. (apply(lambda \_. b, (apply(injr(b),v))))$],
    ),
    v(2em),
  ),
  caption: [Compiler Rules for Mutable Cells]
) <compiler-ref-rules>


