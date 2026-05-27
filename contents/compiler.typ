#import "/models/language.typ": *
#import "/proofs/setup.typ": *
#import "/utils.typ": load-bib, no-ref

#show: no-ref

= Formal Compiler

A compiler from #langc to #lange is straightforward for expressions inherited from the #langb language. The compiler keeps these same expressions, albeit each sub-expression must be compiled _recursively_ to ensure no contracts remains after compilation. Remaining expressions are contract-related expressions. Our idea is that a contract check is a side effect, defined as #effcheck. This effect idealy receives a tuple $tuple(l, tuple(e, v))$ of blame label $l$, contract predicate $e$, and to-be-checked value $v$. Then, a flat contract is simly an effect perform with its correct inputs.

Functional contracts are more complex. Because the effect can only be invoked on a flat contract, the compiler recursively expands the expression, pads the expression into a function when it is expecting a function. During the compilation, new variables are generated to pad the expression into a function. The process is also applicable to dependent contracts. However, the dependent contract needs to update the post contract with a contract for argument. This is trivial but requires a duplication of compilation with a different label. The rules are crafted carefully to prevent syntaxs of #lange into #langc while compiling the dependent contracts. The compiled argument contract is delayed substitution, using a random variable as placeholder, until we have the #lange expression which we can safely replace into.

Compilation for tuple contracts are straightforward. Each tuple entries are compiled individualy, and reconstructed into a new tuple. Then, each entries are protected, flat contracts are checked immediately during tuple construction; functions are protected and should be checked when used.

== Handler design

After all flat contracts are converted into performing an effect, we need a handler. A simple handler can be installed like below:

$
h_("naive") &= {effcheck -> lambda tuple(l,tuple(e,v)). lambda k. ife(apply(e,v),apply(k,v),eblame(l))} \
&#text([where $lambda tuple(l,tuple(e,v))$ deconstructs the value into tuple pattern])
$

This handler performs the check for the value $v$, with the predicate/contract $e$. The continuation $k$ is invoked with the value if the check passes, and blame the label $l$ if the contract is violated. At first glance, this handler is correct. In fact, the handler should produce correct semantic, as long as no dependent contracts are used. When dependent contracts are used, $e$ is now populated with monitored arguments, which after compilation should include $apply(perform(effcheck, tau),"arg")$. And since the handler is moved into the continuation $k$, there is no handler at $apply(e,v)$. Take the following program wrapped with the naive handler $h_("naive")$.

#align(left, stack(
  grid(
    columns: (auto, auto),
    align: (left, left),
    gutter: 1em,

    [], [$apply(mon(k,l,j,dep(flat(e_1), lambda y. flat(e_2)), f), 42)$],
    [], grid.cell(align: right, [where $e_1 = lambda x. trueb$, $e_2 = lambda x. x > y$, and $f = lambda x. x + x$]),
    [$#compiles-into$], [$apply((lambda x_1. apply(perform(effcheck, numt), tuple(k, tuple(e_3, apply(f, (apply(perform(effcheck, numt), tuple(l, tuple(e_1, x_1))))))))), 42)$],
    [], grid.cell(align: right, [where $e_3 = {(apply(perform(effcheck, numt), tuple(l, tuple(e_1, x_1))))\/y}e_2$]),
  ),
  v(1em),
  line(length: 100%),
  v(1em),

  grid(
    columns: (auto, auto),
    align: (left, left),
    gutter: 1em,

    [], [$apply(handler(h_"naive"), lambda \_. (apply(lambda x_1. apply(perform(effcheck, numt), tuple(k, tuple(e_3, apply(f, (apply(perform(effcheck, numt), tuple(l, tuple(e_1, x_1)))))))), 42)))$],

    [$estep$], [$handle(h_"naive", (apply(lambda x_1. apply(perform(effcheck, numt), tuple(k, tuple(e_3, apply(f, (apply(perform(effcheck, numt), tuple(l, tuple(e_1, x_1)))))))), 42)))$],
    [$estep$], [$handle(h_"naive", apply(perform(effcheck, numt), tuple(k, tuple(e'_3, apply(f, (apply(perform(effcheck, numt), tuple(l, tuple(e_1, 42)))))))))$],
    [], grid.cell(align: right, [where $e'_3 = {(apply(perform(effcheck, numt), tuple(l, tuple(e_1, 42))))\/y}e_2$]),
    [$estep1$], [$handle(h_"naive", apply(perform(effcheck, numt), tuple(k, tuple(e'_3, apply(f, 42)))))$],
    [$estep1$], [$handle(h_"naive", apply(perform(effcheck, numt), tuple(k, tuple(e'_3, 84))))$],
    [$estep1$], [$ife(apply(e'_3,84),apply((lambda x. handle(h_"naive", x)),84),eblame(k))$],
    [$estep1$], [$ife(84 > (apply(perform(effcheck, numt), tuple(l, tuple(e_1, 42)))), apply((lambda x. handle(h_"naive", x)),84),eblame(k))$],
    [], [_stuck_]
  ),
))

To resolve this issue, we define a recursive function $kw("wrap")$ that will reinstall the handler at $apply(e,v)$ making sure all effects during contract checking is handled. All compilation rules are defined in @compiler-rules. With $kw("wrap")$ defined, we can make some theorems about the compiler.

The compiler should produce same type expression. However, this is problematic when effects are introduced. Recall that the type system separates between pure function, and effectful functions. And type judgement separates between non-effectful computations and effectful computations. Depending on the source, compiled program may have the same type with no effects (no monitors), or same type with some effects (monitors during computation), or purely produce a function wrapped by monitors, or effectfully produce a function wrapped by monitors (monitors during computation).

Regardless, wrapping the compiled program with $kw("wrap")$ should handle all possible effects.

#theorem[
Compiler Type Preservation.

#set align(left)

If $compile(type(dot.op,e_1,tau),e_2)$ then either

- $type(dot.op,e_2,tau, eff: mteff)$ or
- $tau = tau_1 -> tau_2$ and $type(dot.op,e_2,teff(tau_1,effcheck,tau_2), eff: mteff)$ or
- $type(dot.op,e_2,tau, eff: chevron.l heffcheck chevron.r)$ or
- $tau = tau_1 -> tau_2$ and $type(dot.op,e_2,teff(tau_1,effcheck,tau_2), eff: chevron.l heffcheck chevron.r)$.

]<compiler-type-preservation>

#theorem[
Compiler Effect Safety with $kw("wrap")$.

#set align(left)

If $compile(type(dot.op,e_1,tau),e_2)$ then either

- $type(dot.op, apply(kw("wrap")[tau],(lambda \_: kw("unit"). e)), tau, eff: mteff)$.
- $tau = tau_1 -> tau_2$ $type(dot.op, apply(kw("wrap")[tau],(lambda \_: kw("unit"). e)), teff(tau_1,effcheck,tau_2), eff: mteff)$.
]<compiler-handle-all>


#v(1em)
#include "/models/compiler.typ"
#v(1em)



== Compiling Contracts for Mutable Cells

=== Observation

#langc uses $guard(v, kappa, k, l, j)$ as a proxy to mutable cells. Get and set operation go through this guard to enfore contracts at run-time. This proxy makes the action oblivious whether it is a real cell or a guarded value. Consider this simple function that calls $getcell(c)$ for any cell.

$
lambda c. getcell(c)
$

This function should work with both cells $newcell(v)$ and guards constructed from $mon(k,l,j,refc(e),l)$ (where $l$ a location). #lange does not have special reduction rules for mutable cells, therefore, we need a unified interface between cells and protected cells, and rewrite cell operations to use that unified interface.

=== Unified Interface

Our compiler has supports for functions and tuples, this is useful for us to design such unified interface. A mutable cell must support get and set, we can encode this as a tuple of 2 functions. Contracts on a cell is now converted into contracts placed on these get and set functions. Cell's location is enclosed inside the closure, and should be accessible when invoked.

#figure(
  stack(
    grid(
      columns: (auto, auto, auto),
      align: (left, center, left),
      gutter: 1em,

      [$newcell$], [$=$], [$lambda v. apply((lambda l. tuple(lambda \_. getcell(l),lambda \v. setcell(l, v))), newcell(v))$],
      [$getcell$], [$=$], [$lambda b. apply(injl(b), unit)$],
      [$setcell$], [$=$], [$lambda b. lambda v. (apply(lambda \_. b, (apply(injr(b),v))))$],
    ),
  ),
  caption: [Mutable Cells Wrappers]
)

The compiler should first convert all cell operations into this new wrapper. Then convert all $refc(kappa)$ into tuple contracts for get and set functions.

$
mon(k,l,j,refc(kappa),e) #compiles-into mon(k,l,j,tuple("any" -> kappa,"any" -> kappa -> "any"),e)
$
