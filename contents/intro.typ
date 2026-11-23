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
contracts_ can express these requirements and constrain them during runtime using
_monitors_. A monitor is attached to a value, and when that value is passed on as a
function argument, function return, or function invocation, it validates and reports
violations. Implementing monitors requires checks to be inserted at the appropriate
location. @robert2013icfp introduced monitors and provided a semantics for higher-order
functional contracts. The authors also provided monitors for dependent contracts where
function's result contracts can use the function's input, and must be constrained.

In addition to value validations, monitors must also report blame. Each monitor is
appended with labels, where each label represents a party, for use when a blame is
reported. @christos2011on instructed what these labels are and how should them be
exchanged during monitor execution such that it reports the correct party responsible
for the violation.

Functional contracts are restricted to its own execution and this limitation restricts
several contract types where interaction between them is crucial. For example,
protocol conformance requires knowing if the previous steps have been conducted;
or a [strictly] recursive function requires each recursive step's input to reduce.
Multiple works attempted this problem, of which the work by @cameron2023trace stands out.
The authors introduced Trace Contracts which provide monitors with a global state queue
where different contracts can use to communicate.

Functions may trigger side-effects, such as exceptions, and one wishes to constrains them,
either to allow some exceptions, or restrict pure functions. Recently, @cameron2024effectful
adapted monitors to effects in a language with effect handlers. Their work, Effectful
Contracts, superseeded Trace Contracts. Not only can these contracts provide contract
interaction, but also restrict side-effects. To understand their work, one should get
familiar with effects and effect handlers.

Effects and their handlers model side-effects systems using two basic constructions:
perform, and handlers. Effects are named with their definitions provided through a
handler previously installed. A simple analogy, effects are functions where their
body can be changed depending on the environment. Using some specific structures,
effect handlers can be used to model states without using mutable boxes.

== Thesis

Through observations, contracts are similar to side-effects, and it proposes an idea:
implementing contracts using effects and effect handlers. While Effectful Contracts
create a new contract type for effects, our idea treats contracts as if they are
side-effects, contract checking is performing a checking effect. Our claim is that
if contracts can be modeled into effects and effect handlers, and effectful contracts
can build highly complex contract specifications, then effects and effect handlers
by itself can provide these specifications. Our thesis is therefore:

#pad(left: 3em)[
  #emph[
    Effects and effect handlers can implement functional contract system through
    local rewrites, and they can also implement richer contract systems through
    whole program transformations.
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
  behaviors inspired by option contracts @christos2013option, trace contracts
  @cameron2023trace, and effectful contracts @cameron2024effectful. These examples
  further prove our thesis on the richness of contracts obtained from contract
  checking as effects and effect handlers.

== Organization

The rest of this dissertation is organized as follows. @chapter-background introduces
the PCF language (called #langb), with its extension to contracts as CPCF (called #langc),
and a model of effect handler language (called #lange). @chapter-compiler describes the
analytical process designing translations from #langc to #lange. Following the formal
model in the previous chapter, @chapter-implementation shows how it is implemented in
Redex, and OCaml. Finally, @chapter-conclusion gives the final remarks based on the results
obtained from our experiements, and some observations. All formal proofs are provided in
the appendices.
