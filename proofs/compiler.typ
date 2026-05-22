#import "setup.typ": *
#import "/utils.typ": *
#import "/models/language.typ": *

#show: no-ref

#def-theorem(<compiler-type-preservation>)[
If $compile(typecon(dot.op,e_1,tau),e_2)$ then $typeeff(dot.op,e_2,tau,chevron.l effcheck chevron.r)$.
]

#proof[]

#def-theorem(<compiler-handle-all>)[
If $compile(typecon(dot.op,e_1,tau),e_2)$ then $typeeff(dot.op, apply(kw("wrap")[tau],e), tau, mteff)$.
]

#proof[]
