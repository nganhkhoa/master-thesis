#import "@preview/simplebnf:0.1.2": *
#import "@preview/curryst:0.6.0": rule, prooftree, rule-set

#import "/models/language.typ": *
#import "/proofs/setup.typ": *
#import "/utils.typ": load-bib, no-ref


#let using(e_1, x, e_2) = $#e_1 kw("using") #x = #e_2$

Using boxes, contract states can be encoded by just using these boxes inside contract checking code.
We define a new box type called contract-reserved box that can only be used inside contract code.
By providing a different type, we can let the type system rejects contract-reserved boxes inside
original code. Because these are all boxes, we need a specific syntax to introduce them. The
expression $using(e_1,x,e_2)$ initializes a box named $x$ with expression $e_2$, and available for
use inside $e_1$. To make the type system deterministic, we provide new get/set versions for
contract-reserved boxes.

#v(1em)
#figure(
  stack(
    spacing: 1em,
    align(left)[
      #box(
        stroke: 1pt + black,
        outset: 5pt,
        [$#langc^s$],
      )
      #h(6pt)
      extends #langb
    ],
    grid(
      columns: (auto, auto),
      bnf(
        Prod($tau$, {
          Or[$...$][]
          Or[$ref(tau)^c$][]
        }),
        Prod($e$, {
          Or[$...$][]
          Or[$using(e,x,e)$][]
          Or[$getcell(e)^c | setcell(e,e)^c$][]
        }),
      ),
      bnf(
        // Prod($kappa$, {
        //   Or[$...$][]
        //   Or[$kappa times s$][]
        // }),
        Prod($E$, {
          Or[$...$][]
          Or[$using(e,x,E)$][]
          Or[$getcell(E)^c | setcell(E,e)^c | setcell(v,E)^c$][]
        }),
      ),
    ),
    v(1em),
  ),
  caption: [Extending #langc with contract states]
)
#v(1em)


Reduction rule is added easily, by converting the using into a simple application to a lambda.

#figure(
  stack(
    grid(
      columns: (auto, 1fr, auto, auto),
      gutter: 1.5em,

      [$using(e_1,x,e_2)$], [$cstepx$], [$apply((lambda x. e_1), newcell(e_2))$], [CBox-Declare],
    ),
    v(1em),
  ),
  caption: [Reduction Rules for $#langc^s$]
)
#v(1em)

To restrict contract-reserved boxes, we must be able to distinguish between the normal code and contract code.
We define a new relation $type(Gamma, e, tau, type: "c")$, which allows usage of variables typed $ref(tau)^c$.
Obviously, $type(Gamma,e,tau)$ does not allow usage of $ref(tau)^c$. The type judgement for contract code
duplicates those in normal judgement.

#v(1em)
#figure(
  stack(
    rule-set(
      prooftree(rule(
        name: [Type-C-Using],
        $type(Gamma\,x:ref(tau_1)^c, e_1, tau)$,
        $type(Gamma, e_2, tau_1)$,
        $type(Gamma, using(e_1,x,e_2), tau)$
      )),
      prooftree(rule(
        name: [Type-C-Mon],
        $type(Gamma, kappa, con(tau), type: "c")$,
        $type(Gamma, e, tau)$,
        $type(Gamma, mon(k,l,j, kappa, e), tau)$
      )),

      prooftree(rule(
        name: [T-Get-Cell],
        $type(Gamma, e, ref(tau)^c, type: "c")$,
        $type(Gamma, getcell(e)^c, tau, type: "c")$,
      )),
      prooftree(rule(
        name: [T-Get-Cell],
        $type(Gamma, e_1, ref(tau)^c, type: "c")$,
        $type(Gamma, e_2, tau, type: "c")$,
        $type(Gamma, setcell(e_1,e_2)^c, ref(tau)^c, type: "c")$,
      )),
    ),
    v(2em),
  ),
  caption: [Type Rules for $#langc^c$]
)
