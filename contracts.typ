#import "models/language.typ": *
#import "utils.typ": load-bib, no-ref

#show: no-ref

== #langc Language

=== Example

=== Formal

We define #langc, in @contracts-syntax, by extending the Core language with contracts. Contracts protect an expression, ensuring that the evaluated value conform to the contracts defined. Contracts are defined for all possible types of value. Base values, including booleans and numbers, are trivial to enfore a contract on them. While functions need to check for both its argument and return result. Not only that, functions are first-class citizen in the language, and we can form higher-order functions. A contract for function may want to "see" the argument when checking the result, such is the idea of dependent contracts. Both contracts higher-order functions, and dependent contracts semantics are discussed in @robert2013icfp.

The language supports contracts for tuples. Their contracts will be applied individually during execution. Mutable cells contracts follow the work of @christos2011on, where a special contract type $refc(kappa)$ is used to protect the cell's value.

#v(1em)
#include "models/contracts.typ"
#v(1em)

When a contract violation occurs, a blame is thrown with the party, caller or callee. The semantics for correct blaming has been studied under @christos2011on and @christos2012complete. Therefore, we use _indy_ semantics for dependent contracts.

The type system is straightforward, readers interested in the type rules for #langc can consult the Appendix. We provide the semantics for the language in @contracts-reduction-rules.

#include "models/contracts-reduction-rules.typ"
