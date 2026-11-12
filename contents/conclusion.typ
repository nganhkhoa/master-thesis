#import "/setup.typ": setupdoc
#show: setupdoc

#import "@preview/simplebnf:0.1.2": *
#import "@preview/curryst:0.6.0": rule, prooftree, rule-set
#import "@preview/great-theorems:0.1.2": great-theorems-init

#import "/models/language.typ": *
#import "/proofs/setup.typ": appendix-theorem, appendix-lemma, appendix-number, proof

#import "/utils.typ": load-bib, no-ref

#show: no-ref

#show: great-theorems-init

#let theorem = appendix-theorem
#let lemma = appendix-lemma

= Conclusion

== Contract checking as Effects is Possible

Our formal models have proven that contracts checking can be compiled into a effects, and with an appropriate handler wrapper installed to the whole compiled program, the semantics are preserved. From the results obtained, we can conclude two facts, (1) contracts semantics can be emulated using effects and effect handlers, and (2) contracts do not bring extra expressiveness to effect handlers. The first fact is a direct result from the simulation proof(s) given by compilation of local, shallow, and deep handlers. The second fact is from the local compilation. While contracts do not add more expressiveness [to effects and effect handlers], the local compilation model is not useful. We have suggested modeling for the option contracts, and trace contracts under the shallow wrapper non-local compilation. Therefore, the expressiveness argument is both correct and incorrect.

While the compilation preserves semantics, it is not considered the "correct" contract behavior. Contracts provide guards around a value, when that value is used the contract is triggered. The compilations provide the similar behavior, but breaks when it models option contracts. Option contracts wrap around a value, while our method overrides the environment to disable the check instead of wrapping the check around the value or function. A simple distinction is when there are two values protected under option contracts, but only one is executed. Option contract semantics can control which one is executed because it attaches to the contract. Our method must create two different scope for these values at their executing place. This scope creation is hard when we consider both values as functions, and used in a complex, intertwined manner.

== Shallow or Deep handlers

We introduced three different compilation strategies, two of which use shallow handlers, and one uses deep handlers. It is widely agreed that the use of deep handlers is more useful, because effects might be invoked multiple times. Therefore, having a single handler that automatically re-installs itself after each invocation aligns with how programmers view effects. We analyzed the local and non-local compilation strategies and see which handler type should we used.

In the local compiler, the shallow handler is the better choice. By analyzing the perform site, $handle(h, apply(perform(heffcheck), v), m:m)$ captures the context $E = square.stroked$. Therefore, the continuation is $k_1 = lambda x. handle(h, x)$ for deep handler, and $k_2 = lambda x. x$ for shallow handler. The continuation is invoked with $v$ yields $apply(k_1,v) estep1 v$ and $apply(k_2,v) estep1 v$. The handler disappear immediately, although deep handler may take an extra step for discarding handler with a value. Performance wise, shallow handler is more optimal. To be precise, for each contract executed, the deep handler version takes an extra step. As a result, the reduction step count increments the more contract the program executes.

In the non-local compiler, we actually have three different wrappers instead of introduced two. The other unmentioned wrapper is similarly to the shallow wrapper it wraps the whole if else clause but using the wrapper of deep non-local compiler. Let call them by compiler I (shallow wrapper), II (deep wrapper as introduced), III (deep wrapper as previously described). Tracing their execution on nested checks, dependent contracts or flat contract with contract code, III eventually adds more nested handle frames and produces the most reduction steps. Both I and II preserve strictly a single handle frame on the "top", II's continuation has a handle re-installed but is dormant. Because I is a shallow handler, it does not need extra steps to remove the handler on value continuation and reduces some reduction steps.

We proved that regardless of local or non-local compiler, shallow and deep handlers provide the same equivalence to #langc semantics with some [minimal] overhead when using deep handlers. However, as previously stated, deep handlers are more practical and implemented widely. Users should implement our compilation model using shallow handlers, and use deep handlers only if the language only supports deep handlers, for example the Koka language.

== Effectful Contracts

Our formal models can model simple contracts into effects, but it cannot assert any certainty whether it can also model effectful contracts. Effectful contracts requires contracts for two types of effects, main program effects, and contract effects. The effectful contract model manipulates the contracts by installing contract dynamically, which can be a hurdle to model those contracts into effects. Although a simple observation that effectful contracts basically install checks at effect's entry and effect's exit (continuation invocation), we are unsure if such compilation is possible.

== Practicality

The OCaml implementation has proven practical of the formal model, by using attributes to mark contracts, and let the rewritter to resemble the [non-local] compiler model. The practicality is proven through building a Current-Environment-Storage-Continuation (CESK) machine with some important functionalities protected with contracts. With the correct contract usage, we eliminate writing code for malformed cases. Although in the context of OCaml, it does not provide much usefulness compared to pattern matching where every cases are considered.

== Comparison to Racket

Racket has chaperones, an opaque proxy over protected value. This proxy maintains the value equality checker, but on usage, runs the contract attached to the value. Our OCaml implementation cannot provide the opaque proxy because we wrap values under [new] lambdas. This is expected, since chaperone are built-in under the language runtime of Racket, and OCaml has no equivalent construction. Regardless of this, we have modeled contracts for boxes and vectors by providing a wrapper struct where methods are functional and contracts are installed onto these functions.

Racket contracts have no state management built-in. Users want state contracts should either use mutable boxes or the `trace-contract` library. Our OCaml implementation encodes states without extra effort by using handler's state encoding trick through lambdas.

The above facts do not show that our implementation is superior to Racket's contract system, nor that it is inferior. The two models have their limitations. However, an interesting question arises. What if our implementation supports chaperone, or if Racket supports effects. We think that utilizing the chaperone models, and adopting effects into Racket might provide a better model. Chaperone maintains the object equality, and effects compilation provides contract states without hassle.
