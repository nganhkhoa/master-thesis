#import "/models/language.typ": *
#import "/utils.typ": load-bib, no-ref

#show: no-ref

== #langc Language

=== Example

Contracts provide a run-time validation of programs, similar to how assertions work. Contracts extend basic assertions to support functions, especially higher-order ones, correctness. Past research has move from pre/post condition placing on functions, into obligations @robert2013icfp, or monitors. These constructions support blame tracking, enabling the developer to know _who_, which function, is responsible for a violation.

@contracts-example-1 illustrates a function protected with a monitor. This function should return a value that is even. When applied with 10, it is checked by the function's _domain contract_. Since the function does not impose any properties for its argument, the contract passes. The body of the function is executed normally, but its result must pass the function's _range contract_. Because 11 is not an even number, the program terminates with a blame.

#figure(
  stack(
    v(1em),
    grid(
      columns: (2em, auto, 4em),
      align: (left, left, right),
      gutter: 0.8em,

      [],
      [$apply(mon(k,l,j,flat(lambda x. trueb) -> flat(kw("iseven")), lambda x. x + 1), 10)$],
      [],

      [$cstep$],
      [$apply(guard(lambda x. x + 1, flat(lambda x. trueb) -> flat(kw("iseven")), k, l, j),10)$],
      [],

      [$cstep$],
      [$mon(k,l,j, flat(kw("iseven")), apply((lambda x. x + 1), mon(l,k,j, flat(lambda x. trueb), 10)))$],
      [],

      [$cstep$],
      [$mon(k,l,j, flat(kw("iseven")), apply((lambda x. x + 1), guard(10, lambda x. trueb, l, k, j)))$],
      [],

      [$cstep$],
      [$mon(k,l,j, flat(kw("iseven")), apply((lambda x. x + 1), check(l,j, apply((lambda x. trueb), 10), 10)))$],
      [],

      [$cstep$],
      [$mon(k,l,j, flat(kw("iseven")), apply((lambda x. x + 1), check(l,j, trueb, 10)))$],
      [],

      [$cstep$],
      [$mon(k,l,j, flat(kw("iseven")), apply((lambda x. x + 1), 10))$],
      [],

      [$cstep1$],
      [$mon(k,l,j, flat(kw("iseven")), 11)$],
      [],

      [$cstep1$],
      [$blame(k,j)$],
      [],
    ),
    v(1em),
  ),
  caption: [Contracts in action]
) <contracts-example-1>

=== Formal

We define #langc, in @contracts-syntax, by extending the #langb language with contracts. Contracts protect an expression, ensuring that the evaluated value conform to the contracts defined. Contracts are defined for all possible types of value. Base values, including booleans and numbers, are trivial to enfore a contract on them. While functions need to check for both its argument and return result. Not only that, functions are first-class citizen in the language, and we can form higher-order functions. A contract for function may want to "see" the argument when checking the result, such is the idea of dependent contracts. Both contracts higher-order functions, and dependent contracts semantics are discussed in @robert2013icfp.

The language supports contracts for tuples. Their contracts will be applied individually during execution. Mutable cells contracts follow the work of @christos2011on, where a special contract type $refc(kappa)$ is used to protect the cell's value.

#v(1em)
#include "/models/contracts.typ"
#v(1em)

#v(1em)
#include "/models/contracts-type-rules.typ"
#v(1em)

When a contract violation occurs, a blame is thrown with the party, caller or callee. The semantics for correct blaming has been studied under @christos2011on and @christos2012complete. Following previous works, We use _indy_ semantics for dependent contracts. We use $guard(v,kappa,k,l,j)$ as the run-time proxy to value $v$ procted under a contract $kappa$. Guard is a value, the semantics adapt to usage of guards, and expand further, sometimes back to monitor to evaluate inner expressions. A guard on a basic value will trigger a $check(k,j,apply(e,v),v)$ and returns the value $v$ if it passes the predicate $e$, or returns a $blame(k,j)$ to party $k$ with contract location $j$. The evaluation rules for #langc is presented in @contracts-reduction-rules.

#include "/models/contracts-reduction-rules.typ"
