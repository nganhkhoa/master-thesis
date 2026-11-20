#import "/setup.typ": setupdoc
#show: setupdoc

#import "/models/language.typ": *
#import "/utils.typ": load-bib, no-ref

#show: no-ref

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

#include "/models/base.typ"
#include "/models/base-type-rules.typ"
#include "/models/base-reduction-rules.typ"
