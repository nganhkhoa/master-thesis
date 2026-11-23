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

= Conclusion <chapter-conclusion>

== Contract checking as Effects is Possible

Our formal development studies translations of flat, functional, and dependent
contracts into effects and handlers. It gives simulation results for three
variants: an in-place handler and shallow and deep whole-program handlers. These
results concern the modeled contract system and the outcomes covered by the
proofs; they are not a general expressiveness comparison between languages.

The whole-program handler approach also provides a basis for exploring other
checking policies. For example, a dynamically scoped handler can skip checks,
and a handler can carry state across checks. The OCaml implementation illustrates
behaviors inspired by option, trace, and effectful contracts. These examples do
not establish a translation or semantic equivalence for those richer systems.
In particular, disabling checks within a dynamic scope is not the same as an
option contract attached to a particular value: the distinction matters when
values with different contracts are used in intertwined computations.

== Shallow or Deep handlers

We introduced three different compilation strategies, two of which use shallow handlers, and one uses deep handlers. It is widely agreed that the use of deep handlers is more useful, because effects might be invoked multiple times. Therefore, having a single handler that automatically re-installs itself after each invocation aligns with how programmers view effects. We analyzed the in-place and whole-program handler placement strategies and see which handler type should we used.

With an in-place handler, the shallow handler is the better choice. By analyzing the perform site, $handle(h, apply(perform(heffcheck), v), m:m)$ captures the context $E = square.stroked$. Therefore, the continuation is $k_1 = lambda x. handle(h, x)$ for deep handler, and $k_2 = lambda x. x$ for shallow handler. The continuation is invoked with $v$ yields $apply(k_1,v) estep1 v$ and $apply(k_2,v) estep1 v$. The handler disappear immediately, although deep handler may take an extra step for discarding handler with a value. Performance wise, shallow handler is more optimal. To be precise, for each contract executed, the deep handler version takes an extra step. As a result, the reduction step count increments the more contract the program executes.

For whole-program handlers, we actually have three different wrappers instead of introduced two. The other unmentioned wrapper is similarly to the shallow wrapper it wraps the whole if else clause but using the deep whole-program handler wrapper. Let call them by compiler I (shallow wrapper), II (deep wrapper as introduced), III (deep wrapper as previously described). Tracing their execution on nested checks, dependent contracts or flat contract with contract code, III eventually adds more nested handle frames and produces the most reduction steps. Both I and II preserve strictly a single handle frame on the "top", II's continuation has a handle re-installed but is dormant. Because I is a shallow handler, it does not need extra steps to remove the handler on value continuation and reduces some reduction steps.

The simulation results cover the in-place shallow variant and the shallow and deep whole-program handler variants. The reduction-step observations above describe the modeled executions and do not establish a general runtime performance bound.

== Recursion handlers

For whole-program handler wrappers, a recursive handler (shallow) or a recursive wrapper (deep) are used. Both of these install recursive functions onto the handler code, this might not work, for example in Koka#footnote(link("https://github.com/koka-lang/koka/discussions/824")[https://github.com/koka-lang/koka/discussions/824]). If the required recursion is not supported, the in-place handler variant is another approach for the modeled contract semantics; it does not by itself provide the shared checking policies explored with whole-program handlers.

== System $F^epsilon$ and CBPV

#lange is based on System $F^epsilon$ and not Call-By-Push-Value (CBPV) and it may not correctly formulate the full effect handlers calculus. In @lukas2020doo, the effect handlers calculus, Frank, is modeled in CBPV and it has support for recursive handlers. These two languages, System $F^epsilon$ and Frank, based on two different core calculus that adapting the compiler to Frank may not be easy. Regardless, they share the same effect handlers semantics, and System $F^epsilon$ is closer to common programming languages.

== Effectful Contracts

Our formal models can model simple contracts into effects, but it cannot assert any certainty whether it can also model effectful contracts. Effectful contracts requires contracts for two types of effects, main program effects, and contract effects. The effectful contract model manipulates the contracts by installing contract dynamically, which can be a hurdle to model those contracts into effects. Although a simple observation that effectful contracts basically install checks at effect's entry and effect's exit (continuation invocation), we are unsure if such compilation is possible.

== Practicality

The OCaml implementation illustrates an application of the formal model, by using attributes to mark contracts, and let the rewritter to resemble the whole-program handler compilation model. The implementation is illustrated by building a Current-Environment-Storage-Continuation (CESK) machine with some important functionalities protected with contracts. With the correct contract usage, we eliminate writing code for malformed cases. Although in the context of OCaml, it does not provide much usefulness compared to pattern matching where every cases are considered.

== Comparison to Racket

Racket has chaperones, an opaque proxy over protected value. This proxy maintains the value equality checker, but on usage, runs the contract attached to the value. Our OCaml implementation cannot provide the opaque proxy because we wrap values under [new] lambdas. This is expected, since chaperone are built-in under the language runtime of Racket, and OCaml has no equivalent construction. Regardless of this, we have modeled contracts for boxes and vectors by providing a wrapper struct where methods are functional and contracts are installed onto these functions.

Racket contracts have no state management built-in. Users want state contracts should either use mutable boxes or the `trace-contract` library. Our OCaml implementation encodes states without extra effort by using handler's state encoding trick through lambdas.

The above facts do not show that our implementation is superior to Racket's contract system, nor that it is inferior. The two models have their limitations. However, an interesting question arises. What if our implementation supports chaperone, or if Racket supports effects. We think that utilizing the chaperone models, and adopting effects into Racket might provide a better model. Chaperone maintains the object equality, and effects compilation provides contract states without hassle.
