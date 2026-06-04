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
        name: [Compile-Get-State],
        $compile(type(Gamma,getstate(),tau), apply(perform(effstateget, tau), unit))$,
      )),
      prooftree(rule(
        name: [Compile-Modify-State],
        $compile(type(Gamma,e,tau), e_1)$,
        $compile(type(Gamma,modifystate(delta,e),unit), apply(perform(effstateset, tau), e_1))$,
      )),
    ),
    v(2em),
    line(length: 100%),
    v(2em),
    grid(
      columns: (auto,auto,auto),
      align: (center,center,left),
      gutter: 1.5em,

      [$heffcheck : lab$],
      [$=$],
      [${effcheck -> forall alpha. tuple(blab, tuple(alpha -> boolt, alpha)) -> alpha}$],

      [$heffstate : lab$],
      [$=$],
      [${effstateget -> forall alpha. unit -> alpha; effstateset -> forall alpha. alpha -> unit}$],


      [$kw("wrap")_scr("C")$], [$=$],
      [$mu w : (teff((), chevron.l heffcheck chevron.r, boolt)) -> boolt. med lambda f: (teff((),chevron.l heffcheck chevron.r,boolt)).$],
      [], [],
      [$apply(handler({effcheck -> lambda tuple(l,tuple(e,v)). lambda k. ife(apply(w, (lambda \_. apply(e,v))),apply(k,v),eblame(l))}), f)$],
      [], grid.cell(colspan: 2, align: right,
        [where $lambda tuple(l,tuple(e,v))$ deconstructs the argument as tuple pattern]),

      [$kw("wrap")_scr("S")$], [$=$],
      [$Lambda alpha. lambda f : unit -> alpha.$],
      [], [],
      [$apply(handler({effstateget -> lambda x. lambda k. lambda s. apply(apply(k,s),s); effstateset -> lambda x. lambda k. lambda s. apply(apply(k,s),x);}),f_1) $],
      [], grid.cell(colspan: 2, align: right,
        [where $f_1 = lambda \_. (apply((lambda x. lambda s. tuple(x,s)), (apply(f,unit))))$]),


      [$kw("wrap")$], [$=$],
      [$forall alpha. ((teff((), chevron.l heffcheck chevron.r, alpha)) -> alpha). med lambda f: (teff((),chevron.l heffcheck chevron.r,alpha)).$],
      [], [],
      [$apply(handler({effcheck -> lambda tuple(l,tuple(e,v)). lambda k. lambda s. apply((lambda tuple(b,s_1). ife(b, apply(apply(k,v),s_1), eblame(l))), e_1)}), f_1)$],

      [], grid.cell(colspan: 2, align: right,
        [where $f_1 = lambda \_. (apply((lambda x. lambda s. x), (apply(f,unit))))$]),
      [], grid.cell(colspan: 2, align: right,
        [where $e_1 = apply(apply(kw("wrap")_scr("S"), lambda \_. (apply(kw("wrap")_scr("C"), (lambda \_. apply(e,v))))), s)$]),

      [], grid.cell(colspan: 2, align: right,
        [where $lambda tuple(l,tuple(e,v))$ and $lambda tuple(b,s_1)$ deconstructs the argument as tuple pattern]),
    ),
    v(2em),
  ),
  caption: [Compiler Rules for Contract State Handling]
) <compiler-state-rules>

