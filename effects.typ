#import "models/language.typ": *
#import "utils.typ": load-bib, no-ref

#show: no-ref

== #lange Language

=== Example



=== Formal

We continue to extend the *Core* language with effects and effect handlers in @effects-syntax. This is done by typing the effects separately from the base types. This practice has been introduced to formalize the Koka#footnote(link("https://koka-lang.github.io/")) language. The approach we take here resembles the System $F^epsilon$ language introduced in @ningning2020effect. We added polymorphism through type application, and kinds to *Core* language. Two special kinds are added to represent effects (#eff) and effect labels (#lab). A label $l in #lab$ is a group of operations. And an effect $e in #eff$ is composed by chaining #lab together with other effects. An empty effect $mteff$ defines no labels, therefore no effects can be performed. In otherwords, #eff defines the set of effects that can be performed. A function can now produce some effects $epsilon in #eff$, and is represented in its type $teff(tau_1,epsilon,tau_2)$.

The language is then extended with handlers, handler installation ($handle(h,e)$), and calling/performing an effect ($perform(op, tau)$). Handlers are a set of operations distinguishable by the operation's name. A handler denotes a single effect usually by its label $l in #lab$. Performing an effect is analogous function application, therefore $perform(op,tau)$ is treated as a value, where application for it has a distinct reduction rule. The evaluation context is thus extended to support handler installation.

#v(1em)
#include "models/effects.typ"
#v(1em)

Typing for an effect language requires some consideration. Following the works in @ningning2020effect, we define the type judgement relationship $typeeff(Delta,e,tau,epsilon)$ between a type context $Delta$, an expression $e$ and assert it against type $tau$ with some possible effects $epsilon$. Variables and base values do not have effects, they can take any effects. For this reason, we define $typeeff(Delta,v,tau,,type: "val")$. Handlers are typed using $typeeff(Delta,h,tau,l | epsilon,type: "ops")$, that it handles a _single_ effect $l$, other effects in $epsilon$ remains unhandled, and all operations returns $tau$. All type rules unique to #lange is presented in @effects-type-rules.

#v(1em)
#include "models/effects-type-rules.typ"
#v(1em)

Lastly the semantic model of #lange is presented in @effects-reduction-rules. A handler can be installed to a function as a shorthand, where it applies the function with a unit argument, which to be ignored. The reduction for handling an effect calling is encoded as _deep handler_. Supporting the shallow should be straightforward by not installing the handler again in the continuation $k$. There is little advantage to support shallow handlers, therefore, only deep handlers are used. While looking for the handler, we make sure we get the innermost handler that can handle the operation.

#v(1em)
#include "models/effects-reduction-rules.typ"
#v(1em)
