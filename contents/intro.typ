#import "/setup.typ": setupdoc
#show: setupdoc

#import "@preview/codly:1.3.0": *
#import "@preview/codly-languages:0.1.1": *

#import "/models/language.typ": *
#import "/proofs/setup.typ": appendix-theorem, appendix-lemma, proof
#import "/utils.typ": load-bib, no-ref

#show: codly-init.with()
#codly(languages: codly-languages)

#show: no-ref

= Introduction

In software engineering, correctness is crucial but hard to achieve. Correctness is understood as the desired behaviors of a single function or a group of functions, such as a protocol. Programmers often write specifications to describe their desired behaviors. Types and type systems are an example of a specification. However, some behaviors may be outside what type systems can express. Consider a withdrawal function `withdraw(balance, amount)` withdrawing a certain amount from the balance and returning the new balance. Type systems are likely troubled to express the user's balance is subtracted by the correct amount. For these complex behaviors, programmers often write assertions code inserted at function's entrace or exit. These entrace and exit assertions form an abstraction that is best known as "Design by Contracts". If any assertion fails, the execution stops. In some implementations, an execution is thrown.

Contracts, first appeared in Eiffel @meyer1992eiffel in the late 1980s, is a specification notion for complex runtime behaviors. Instead of assertions, users write pre-conditions and post-conditions and attach them to functions. Their long development have standardized the basic contract system, consisting of _flat_, _function_, and _dependent_ contracts. A flat contract is a predicate over values that are static, such as numbers, or strings. Function contract gives each argument its own contract and a contract for the function's result. Dependent contract extends function contract to allow arguments usage in the result's contract, which is useful to guarantee conformance between the function's output and its inputs. Furthermore, @robert2002contracts introduced contracts support for higher-order functions, where functions can be used as arguments. Contracts must always be satisfied, or the execution is stopped and a _blame_ is reported. Blames give contracts meaning, by reporting the responsible party for the violation.

// In function contracts, blame separates between the party providing the arguments, and the party providing the function. Dependent contract blaming is more tricky because contract calls contract, which makes the party unobvious. Fortunately, @christos2012complete showed how blames for dependent contracts should be implemented.

Using the above contract system, a programmer can write a specification for the withdrawal example, ensuring the balance is correctly withdrawn. The specification is a dependent contract, when the function returns with the new balance, it takes the original balance and amount arguments to validate. Going a step further, the programmer can implement a banking protocol taking a withdrawal function, for different currency system. By placing a contract over the banking protocol argument, the programmer can still guarantee any withdrawal functions' behavior. In an update, the programmer modifies the function into `withdraw(user,amount)`, where a user object is provided instead of his balance. Now, the programmer wants to ensure only the user object is modified. The contract system discussed thus far cannot express this requirement.

// blame is too big here that we don't use anywhere else

The basic contract system has difficulties expressing guarantees about effectful code. Programs, more often than not, are effectful by mutation, or exceptions, etc. The contract research community has spent years coming up with different contract systems for each type of effects because the literature then lacked a universal effect system. Recently, [algebraic] effect handlers @gordon2013handling emerged as the universal effect system. Under the context of effect handlers, @cameron2024effectful designed an _effectful contract_ system capable of expressing contracts for effectful code universally, through an introduction of a new contract type: _effect-handler contracts_. Their system can express contracts for mutation, exceptions, protocols ordering, etc., allowing richer contracts to be expressed. In the updated example, the programmer can now write effectful contract(s) storing the original user's balance and use them on function exit, furthermore guarantee mutation against the user's balance only.

== Thesis

My observation is that contract checkings are a type of effects and can be modeled by effect handlers. Contracts should not interfere with the logic of a correct execution. Therefore, every contract checking is considered a side-effects, one that adds nothing during a correct execution. Because effect handlers implement a universal effect system, they should therefore be able to express contract checking natively. In connection to effectful contract system, effect handlers should be implemented with only effect handlers.

My work tries to understand to what extend can effect handlers implement a contract system. More importantly, can effect handlers be used to implement an effectful contract system. If yes, then how much code should be changed. The thesis follows:

#pad(left: 3em)[
  #emph[
    An effectful contract system can be built from algebraic effect handlers through whole-program translation.
  ]
]

== Contributions

We define two formal models of software contracts, #langc, and effect handlers, #lange.
These two models serve as the basis for our contributions:

- Three translations from well-typed #langc programs to #lange. The translations
  produce well-typed #lange programs, and preserve the semantics of source program.
  The translations' properties are formally proven. We also provide Redex models
  based on these translations with examples.

- An OCaml implementation based on effectful checking, with examples exploring
  contracts behaviors such as Option contracts @christos2013option, Trace contracts
  @cameron2023trace, and Effectful contracts @cameron2024effectful. These examples
  further prove our thesis on the richness of contracts obtained from contract
  checking as effects and effect handlers.

== Organization

The rest of this dissertation is organized as follows. @chapter-background introduces
the #langb language modeled under the PCF language by @gordon1977lcf; the #langc language extending #langb with contracts extensions;
and the #lange language extending #langb into System $F^epsilon$ of @ningning2020effect. @chapter-compiler describes the
analytical process of designing three translations from #langc to #lange, and their formal models. Following the formal
models in the previous chapter, @chapter-implementation discusses their implementation in
Redex, and OCaml. Finally, @chapter-conclusion gives the final remarks based on the results
obtained from our experiements, and some observations. All formal proofs are provided in
the appendices.
