#import "/models/language.typ": *
#import "/proofs/setup.typ": *
#import "/utils.typ": load-bib, no-ref

#show: no-ref

= Formal Compiler

In this section, we discuss a compiler from #langc to #lange. It is straightforward that many expressions are inherited from the #langb language, and the compiler keeps these same constructions. What is left are contract-related expressions. To reiterate our idea that a contract is a side effect, we define such effect as #effcheck. This effect idealy receives a tuple of $tuple(l, tuple(e, v))$ where $l$ is the blame label, $e$ is the contract predicate, and $v$ is the protected value. Then, a flat contract [Compile-Flat] is simly an invocation of such effect with its correct inputs.

Functional contracts are more complex. Because the effect can only be invoked on a flat contract, the compiler recursively expands the expression, pads the expression into a function when it is expecting a function. During the execution, new variables are generated to pad the expression into a function. The process is also applicable to dependent contracts. However, the dependent contract needs to update the post contract with a contract for argument. This is trivial but requires a duplication of compilation with a different label.

After all flat contracts are converted into performing an effect, we need a handler. A simple handler can be installed like below:

$
h &= {effcheck -> lambda tuple(l,tuple(e,v)). lambda k. ife(apply(e,v),apply(k,v),eblame(l))} \
&#text([where $lambda tuple(l,tuple(e,v))$ deconstructs the value into tuple pattern])
$

This handler performs the check for the value $v$, with the predicate/contract $e$. The continuation $k$ is invoked with the value if the check passes, and blame the label $l$ if the contract is violated. At first glance, this handler is correct. In fact, the handler should produce correct semantic, as long as no dependent contracts are used. When dependent contracts are used, $e$ is now populated with monitored arguments, which after compilation should include $apply(perform(effcheck, tau),"arg")$. And since the handler is moved into the continuation $k$, there is no handler at $apply(e,v)$.

TODO: add example here

#v(1em)
#include "/models/compiler.typ"
#v(1em)

To resolve this issue, we define a recursive function $kw("wrap")$ that will reinstall the handler at $apply(e,v)$ making sure all effects during contract checking is handled. All compilation rules are defined in @compiler-rules. With $kw("wrap")$ defined, we can make some theorems about the compiler.

#theorem[
Compiler Type Preservation.

If $compile(type(dot.op,e_1,tau),e_2)$ then $type(dot.op,e_2,tau, eff: chevron.l heffcheck chevron.r)$.

]<compiler-type-preservation>

#theorem[
Compiler Effect Safety with $kw("wrap")$.

If $compile(type(dot.op,e_1,tau),e_2)$ then $type(dot.op, apply(kw("wrap")[tau],e), tau, eff: mteff)$.
]<compiler-handle-all>

