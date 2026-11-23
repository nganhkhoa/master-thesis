#import "@preview/great-theorems:0.1.2": great-theorems-init
#import "/proofs/setup.typ": appendix-theorem
#import "/models/language.typ": *
#import "/utils.typ": load-bib, no-ref

#show: no-ref
#show: great-theorems-init

// Use the shared theorem counter with numeric chapter numbers in the body.
#let theorem = appendix-theorem.with(numbering: "1.1")

== #langb Language <chapter-base>

This chapter re-introduces the some parts of the PCF language @gordon1977lcf as #langb.
The language is a call-by-value semantics with three types, numbers, booleans, tuples,
unit, and functions. Unit types' purpose is to delay execution of a computation by
encapsulating them under a lambda accepting an argument of unit type. #langb follows
the PCF semantics, with extra rules for tuples.

@base-syntax is the #langb language syntax, with its type rules and reduction semantics
in @base-type-rules, and @base-reduction-rules respectively.

The purpose of #langb is the base for the two main languages #langc and #lange. While
#langc only extends with monitor terms, #lange extends the system into a System $F_omega$
with kinds, type abstraction, and type applications.

#langb is safe by progress and preservation.

#theorem(title: [#langb Type Safety])[

  1. If $type(dot, e, tau)$ and $e step e'$ then $type(dot,e',tau)$
  2. If $type(dot, e, tau)$ then $e$ is a value or $e step e'$ for some $e'$.
] <langb-Type-Safety>

#include "/models/base.typ"
#include "/models/base-type-rules.typ"
#include "/models/base-reduction-rules.typ"
