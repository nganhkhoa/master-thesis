#import "nuthesis.typ": nuthesis

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
  _Contracts checking can be encoded as side-effects and benefited from context sharing when handled using effect handlers._
]

== Contributions

This thesis explores the ``contracts checking as effects'' approach to
implementing software contracts. Through experiments, we show that this
approach accomodates functional contracts, dependent contracts, and the
challenging higher-order contracts. We also discovered that as effects, their
contexts can be shared if they are under the same handler. Sharing contracts
context opens new capabilities to optimizations and contract state sharing.
This disseration shows the above idea by providing a compiler model between
CPCF @christos2011on and System $F^epsilon$ @ningning2020effect. We also provide
an implementation in OCaml as a practical implementation.

The rest of the thesis is organized as follows: Chapter \ref{chap:contracts}
and Chapter \ref{chap:effects} introduces the two formal languages #langc
based on CPCF, and #lange based on System $F^epsilon$; Chapter
\ref{chap:compiler} discusses a theoretical compiler from #langc to #lange as
a demonstration to ``contract checking as effects''; Chapter \ref{chap:ocaml}
introduces the OCaml language and its native support for effect handlers;
Chapter \ref{chap:implementation} provides the implementation of the
theoretical compiler in OCaml using PPX rewritter; Chapter \ref{chap:compare}
compares our implementation in OCaml to the Racket's contract system; Chapter
\ref{chap:final} concludes our remarks.

= Formal Language Models

#include "core.typ"
#include "contracts.typ"
#include "effects.typ"

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
