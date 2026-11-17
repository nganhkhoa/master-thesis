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

Software correctness depends not only on the types of values, but also on properties
of those values. For example, a function that accepts an integer may require that
number to be in some range, and its result must resonates with the input. _Software
contracts_ can express these requirements and constraint them during runtime using
_monitors_. A monitor is attached to a value, and when that value is passed on as a
function argument, function return, or function invocation, it validates and reports
violations. Implementing monitors requires checks to be inserted at the appropriate
location. Monitors for higher-order functions @robert2013icfp create monitors for
function-like arguments, and dependent monitors must create monitors for inputs to
be used during result's monitor execution.

In addition to value validations, monitors must also report blame. Each monitor is
appended with labels, where each labels represent a party, for use when blame is
reported. In @christos2011on, these labels are provided and exchanged during monitor
execution such that it reports the correct party responsible for the violation.

The above construction is mostly local, a monitor can only observe a single execution.
Trying to remove this limitation, a monitor on a function called multiple times may
use previous invocation information to benefit itself. Previously, @cameron2023trace
introduced Trace Contracts attempted this problem by providing a global queue every
time a _trace monitor_ is invoked. In their derived work, @cameron2024effectful,
monitors are built on top of effect handlers, and capable of providing more useful
constraints such as restricted exceptions, or union contracts.

Effects and effect handlers, introduced in @gordon2003algebraic, model side-effects,
as a two-fold: effect invocations and handlers. Effect invocations are modeled as
functions with dynamic body. Function bodies are defined only if there is a handler
already installed. Each handler can be designed to create a different context, which
implements mutable states without explicit mutable boxes. Handlers come in two flavors,
deep and shallow, where the difference is that deep handler automatically reinstall
the handler again, so that subsequent code can still invoke the effect and be handled
by the same handler. Practically deep handlers are more useful, for example, a
print effect can be invoked multiple times. At the time of writing, the only mainstream
language supports effect handlers by default is OCaml 5 @k2021retrofitting.

Stated previously, contract with effects (and effect handlers) bring tremendous benefits
from plain/higher-order contract systems. Our work asks whether contract checking itself
can be an effect. In particular, instead of inlining contract checking code, these checks
are deferred in handler(s). Based on the construction and semantics preservation, we can
argue about the expressiveness of effect handlers over contracts. During our work, it shows
that such construction exists and our thesis follows:

#pad(left: 3em)[
  #emph[
    While encoding contracts as effects does not increase the expressiveness of effects, delicate handler constructions make it possible to unify contracts into a single context. This unification enables contract states and communication between contracts without relying on mutable boxes.
  ]
]

== Contributions

This dissertation contributes the following:

- An extension of effect handlers language, System $F^epsilon$ @ningning2020effect,
  with recursive functions.

- Three compilation schemes based off of the type-directed compilations addressing
  the handler location. The two type-directed compilations of contract monitors into
  effects are: local and non-local. Local compilation compiles flat contracts with
  handler, and non-local does not.

- Simulation proofs for all three compilation schemes, showing that they preserves
  the contract semantics. If the source program reaches a value, then the target
  program reaches a value; if the source program reaches a blame of party, then
  the target program reaches an error labeled the same blame party.

- Suggested extension to the compilation schemes to support option contracts
  @christos2013option, trace contracts @cameron2023trace, effect contracts
  @cameron2024effectful.

- Redex models for the compilation schemes as a runable formal model.

- OCaml implementation of the formal model. The implementation provides
  option contracts, and trace contracts.

== Organization

This dissertation is organized in the following order. First, we define the #langb
in @chapter-base, which is the base for #langc, introduced in @chapter-contracts, and
#lange, introduced in @chapter-effects. Subsequently, an analysis of compiler construction
and the three compiler schemes is discussed in @chapter-compiler. Following the formal
compiler, @chapter-implementation presents the Redex models, and the OCaml implementation.
Finally, @chapter-conclusion concludes our remarks based on the results obtained from
experiments, and observations. Formal proofs are provided in the appendices.
