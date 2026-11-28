#import "@preview/great-theorems:0.1.2": great-theorems-init
#import "/proofs/setup.typ": appendix-theorem
#import "/models/language.typ": *
#import "/utils.typ": load-bib, no-ref

#show: no-ref
#show: great-theorems-init

// Use the shared theorem counter with numeric chapter numbers in the body.
#let theorem = appendix-theorem.with(numbering: "1.1")

== #langb Language <chapter-base>

The purpose of this section is to introduce a typed call-by-value #langb language, extended from PCF @gordon1977lcf. This language contains the common values, expressions, types, type rules and semantics that are shared between #langc and #lange.

The language supports the basic types $tau$ of unit $unit$, numbers $numt$, booleans $boolt$, tuples $tuple(tau,tau)$, and lambdas (or functions) $tau -> tau$. Values $v$ are variables $x$, unit $unit$, numbers $n$, boolean $trueb,falseb$, tuples $tuple(v_1,v_2)$, and lambdas $lambda x : tau. e$. It follows to support expressions $e$ that are applications $apply(e_1,e_2)$, and operations under numbers, booleans, and tuples. It also supports an if/else expression $ife(e_1,e_2,e_3)$. The $unit$ type, and value are used to build delayed evaluation, $lambda x : unit . e$. Because the variable in a delayed function is not used, we often write $lambda \_. e$ (with or without type). They are intended to be used in #lange, while appear extra in #langc. The full syntax for #langb is provided in @base-syntax.

Let $"fv"(e)$ denotes the set of free variables in $e$, it is defined as:

$
"fv"(x) &= {x} \
"fv"(lambda x : tau. e) &= "fv"(e) \\ {x} \
"fv"(apply(e_1,e_2)) &= "fv"(e_1) union "fv"(e_2) \
... &= ... \
$

The typing judgement $type(Gamma,e,tau)$ is read as "under environment $Gamma$ expression $e$ has type $tau$". Typing a program starts with an empty context $type(dot,e,tau)$. The context is an _unordered list_ of bindings from variable to its type, $x : tau$. The typing judgement is defined with weakening, if $type(Gamma,e,tau)$ then $type(Gamma\,x:tau',e,tau)$ for $x in.not "fv"(e)$. The rules are standard type derivation and is defined in @base-type-rules.

The semantics of #langb follows the call-by-value with evaluation context defined as left-to-right evaluation. Reduction $e_1 stepx e_2$ is defined for redexes, and the whole program steps by $e_1 step e_2$. The reduction $e_1 step1 e_2$ is the reflexive transitive closure of $e_1 step e_2$.

Redexes reductions for functions application, $apply((lambda x : tau. e),v) stepx e[x:=v]$ replaces _free_ occurances of $x$ in $e$ with $v$. If/else expression steps by conditional $trueb$ or $falseb$. And tuples reductions $injl(tuple(v_1,v_2)) stepx v_1$ or $injr(tuple(v_1,v_2)) stepx v_2$ obtain the left or right element, respectively, of the tuple value.

#langb is safe by progress and preservation.

#theorem(title: [#langb Type Safety])[

  1. If $type(dot, e, tau)$ and $e step e'$ then $type(dot,e',tau)$
  2. If $type(dot, e, tau)$ then $e$ is a value or $e step e'$ for some $e'$.
] <langb-Type-Safety>

#include "/models/base.typ"
#include "/models/base-type-rules.typ"
#include "/models/base-reduction-rules.typ"
