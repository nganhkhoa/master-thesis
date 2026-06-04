#import "nuthesis.typ": nuthesis

#import "proofs/setup.typ": *
#import "models/language.typ": langc, lange
#import "utils.typ": load-bib

#show: nuthesis.with(
  title: "Contract Checking as Effects",
  author: "Anh Khoa Nguyen",
  degree: "Master of Science",
  field: "Computer Science",
  campus: "EVANSTON, ILLINOIS",
  graduation-month: "December",
  graduation-year: 2026,

  abstract: [
    nice
  ],

  acknowledgements: [
    Text for acknowledgments goes here. You can thank your advisors,
    peers, and family.
  ],

  preface: [
    This is the preface (optional).
  ],

  dedication: [
    This is the dedication (optional).
  ]
)

// ==========================================
// THE BODY OF YOUR THESIS STARTS HERE
// ==========================================

= Introduction

Software contracts, or _behavioral contracts_, allow programmers to
attach assertions to values, and functions. These assertions are runtime
guarantees, on violation, an error is thrown, blaming the violating party.
Contracts are most useful when placed on a function, enforcing the function's
input and output values. While first-order functional contracts are useful,
they are too simple. Higher-order functional contracts allows programmers to
enforce contracts for higher-order functions. Dependent contracts are
functional contracts allowing usage of the function argument during
post-condition contract checking.

Recently, algebraic effect handlers has gained a large attraction, and is
adopted in OCaml since version 5.0. Effect handlers open a new way to identify
effects and handling them. Handlers are defined to handle one or many effects.
A handler for an effect can stop the program or continue with some result.
Handlers do not have state by default, but it can be implemented by applying
the new states to the continuation closure, and let the underlying computation
receives a state argument.

Combining the contract system and effect handlers is a new approach. Effectful
Contract @cameron2024effectful demonstrates how both systems can be combined,
providing contracts for effectful code. Contracts in their system remain a
language feature. In this dissertation, instead of combining the effects and
contracts, we ask ourselves whether contract checking itself can become an
effect, and reuse the capabilities of handlers.


#pad(left: 3em)[
  _Contract checking can be encoded as effects, and delegate them to
  handlers can unify all contracts in the same context, while separated from main code._
]

== Contributions

This dissertation provides concrete evidence to the thesis claim. We model the two
languages #langc representing software contracts, and #lange representing effect handlers.
Then a formal model for a compiler between #langc and #lange is presented. This compiler
is proven correct, and effect safe. Moreover, we provide an implementation of such compiler
by providing a preprocessor to convert OCaml code annotated with contracts into run-able
OCaml code based off this compiler model. Lastly, we provide a Redex PLT model to test our theorems.

Structure ...

= Formal Language Models

#include "contents/core.typ"
#include "contents/contracts.typ"
#include "contents/effects.typ"

#include "contents/compiler.typ"

#include "contents/implementation.typ"

// ==========================================
// REFERENCES & APPENDICES
// ==========================================

#load-bib(main: true)

#set heading(numbering: "A.1")
#counter(heading).update(0)

= Contract Erasure

// #include "proofs/contract-erasure/attemp7.typ"


= Effects Safety

// #include "proofs/effects/context.typ"
// #include "proofs/effects/progress.typ"
// #include "proofs/effects/preservation.typ"


= Compiler Soundness

#include "proofs/compiler.typ"
