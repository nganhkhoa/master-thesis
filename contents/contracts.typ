#import "/setup.typ": setupdoc
#show: setupdoc

#import "/models/language.typ": *
#import "/utils.typ": load-bib, no-ref
#import "@preview/great-theorems:0.1.2": great-theorems-init

#import "/proofs/setup.typ": appendix-theorem, rn

#show: great-theorems-init
// Body statements share the chapter-scoped counter with the appendices.
#let theorem = appendix-theorem.with(numbering: "1.1")

#show: no-ref

== Software Contracts and #langc <chapter-contracts>

This section introduces the concepts of software contracts: monitors, and blames alongside the formal language model #langc. Then it follows up with a few examples using the #langc language. The rest of the document refers to software contracts as contracts.

_Contracts describe obligations_ of two parties, the client and the server over a piece of code, function, provided by the server. The client's obligation is to provide correct input(s), and the server's obligation is to return correct output(s). Obviously the code itself cannot observe the interaction between client and server. Therefore, a thin wrapper is placed around the function to observe interactions. This thin wraper is called a monitor, first introduced as an _obligation expression_ by @robert2002contracts for higher-order contracts. The monitor keeps track of the parties involved, and reports the party failing to meet its obligation.

When writing programs, the function definition, its usage and contract may be defined separatedly. A function can be defined in module $A$, used in module $B$, and its contract defined in module $C$. The monitor is placed during compilation time, or before runtime (for interpreter) at occurances of its usage in module $B$. Together they form the monitor labels: $A$ for the server, $B$ for the client, and $C$ for the contract location. Similar techniques are applied to naming labels for monitors, usually involve module names, or function names.

The first extension from #langb into #langc is contract $kappa$. There are three types of contracts: flat $flat(e)$, function $kappa_1 -> kappa_2$ and dependent $dep(kappa_1,lambda y. kappa_2)$. Contracts have their own type $con(tau)$. In #langc, contracts are not values or expressions.

A flat contract $flat(e)$, when being used under a base value, numbers, or booleans, or tuples, the predicate $e$ runs against the value and should return $trueb$. If the predicate returns $falseb$, the contract is unsatisfied. A predicate $e$ has type $tau -> boolt$, the flat contract of this predicate is of type $con(tau)$.

A function contract $kappa_1 -> kappa_2$ has a domain contract $kappa_1$ and a range contract $kappa_2$. The domain contract describes the obligation of the client's supplied argument. The range contract describes the obligation of the result returned by the server. When the function is called, the monitor ensures the argument is monitored under the domain contract. And the result is monitored under the range contract. Thus, argument, whether a base value or a function, is forced to oblige under contract $kappa_1$. The same process applies with return value under contract $kappa_2$. If $kappa_1$ has type $con(tau_1)$ and $kappa_2$ has type $con(tau_2)$, then the function contract $kappa_1 -> kappa_2$ has type $con(kappa_1 -> kappa_2)$.

Dependent contract $dep(kappa_1,lambda y. kappa_2)$ also has domain and range contracts, except its range contract $kappa_2$ can use the argument through the variable $y$. In fact, the argument in the range contract is also protected under $kappa_1$. If the argument is a function, then invoking it under range contract context must also oblige. The typing of dependent contract is similarly to function contract. If $kappa_1$ has type $con(tau_1)$ and $kappa_2$ has type $con(tau_2)$, then the dependent contract $kappa_1 -> kappa_2$ has type $con(kappa_1 -> kappa_2)$, except $kappa_2$ is typed under the extended context with $y$ of type $tau_1$.

#langc has tuples as inherited by #langb, but does not provide tuple contracts.

With contract $kappa$, a monitor $mon(k,l,j,kappa,e)$ protects an expression $e$. The labels identify parties involved in the contract: $k$ identifies the server providing the protected expression, $l$ identifies its client, and $j$ identifies the party providing the contract. Monitor keeps the obligation propagated as described above. During the evaluation, monitor switches to a check expression $check(k,l,e,v)$ or a guard value $guard(v,kappa,k,l,j)$. A check means a flat contract checking is being performed. A guard is a monitor waiting for a function application. These two runtime constructs will become less obscure when we discuss the semantics of #langc. Besides these two constructs, #langc also has a blame expression $blame(k,j)$ reporting error at party $k$ from a contract at party $j$. The syntax extension into #langc can be found in @contracts-syntax.

The typing judgement of #langc is extended from that of #langb, reusing the syntax $type(Gamma,e,tau)$. The same syntax is also being used to type a contract $type(Gamma,kappa,con(tau))$, reads "under context $Gamma$, the contract $kappa$ is a contract for any expressions of type $tau$", because variables may appear in contracts. Typing of contracts was described during the explanation contracts above. Monitor typing ensures contract and expression types are compatible. #langc only accepts programs where contracts of type $con(tau)$ are used with expressions of type $tau$. Although check expressions, and guard values do not appear in the surface syntax, they are also given their own type rules for Type Preservation theorem. Check expression checking code is of type $boolt$, and guard value is typed similarly to a monitor. The added type rules for #langc is in @contracts-type-rules.

#langc semantics are defined by redex reduction $e_1 cstepx e_2$ and whole program reduction $e_1 cstep e_2$ with reflexive transitive closure $e_1 cstep1 e_2$. #langc also reuse the redex reduction of #langb by #rn("Step-C-Base"). Because the language is a call-by-value, its evaluation context is extended from #langb with $mon(k,l,j,kappa,E)$ and $check(k,j,E,v)$. Blame expression propagates and eventually stop the execution as in #rn("Step-C-Blame"). All reduction rules are displayed in @contracts-reduction-rules.

The redex reduction of #langc is simple. Monitors over flat contract convert into a check expression applying the predicate to its value by #rn("Mon-Flat"), and monitors of other contract types converted into a guard by #rn("Mon-Guard"). A finished check with true removes the check by #rn("Check-True"), but converts to a blame expression if false by #rn("Check-False"). Guards are function-like, and on application it converts into a monitor protecting the argument, as well as the result by #rn("Guard-Func") or #rn("Guard-Dep"). For dependent contract application, the range contract replaces the argument with a monitor over the argument.

Guard applications switch their labels accordingly to the indy semantics by @christos2011correct. The indy semantics ensure that blame labels reflect the correct party responsible for the violation. Previously we define $mon(k,l,j,kappa,e)$ with labels $k$ for the server, $l$ for the client, and $j$ for the contract. By #rn("Mon-Flat") and #rn("Check-False"), the blame label is always the "server" label. Therefore, during guard applications, the monitor around the argument switches the labels, updating the blame label to the client. If the argument does not conform, the blame belongs to the client. The result of the application remains the same labels. The argument in the range contract has also switch its labels. The switch credits the client as the "server", and the contract is the "client". Intuitively, if this argument is a base value, it is provided by the client and he should be responsible; if the argument is a function, and invoked during range contract, the range contract becomes the client [providing the argument to invoke the function].

// Programs use contract $kappa$ around an expression $e$ with a monitor $mon(k,l,j,kappa,e)$, where $k,l,j$ are blame labels. A monitor only works when $e$ is a value. If $e$ is not a function, then it must be a flat contract. A flat contract on a value immediately performs a contract checking, $mon(k,l,j,flat(e),v) cstepx check(k,j,apply(e,v),v)$. In the context of a $check(k,j,e,v)$, a contract checking for value $v$ is being performed with checking routine $e$. A successful check unwraps the value $v$. When $e$ is a function, the monitor converts into a special value $guard(v,kappa,k,l,j)$.

// Software contracts was first mentioned in designed by contracts techniques, first appeared in the Eiffel language @meyer1992eiffel. In their purest construction, functions can be annotated with pre-condition for its parameters and a post-condition for its result. During run-time, arguments are checked against the pre-conditions, and the result is checked against the post-condition. The use of pre-condition and post-condition as run-time checks are commonly referred to as _contracts_. The contract system of Eiffel was very basic, it can only support contracts for basic value and cannot work with higher-order functions. In @robert2002contracts, the authors introduce higher-order contracts through the use of obligations, which are referred to as monitors in today's literature.

// Contracts are surface syntax while monitors are run-time wrappers. Contracts are specified separatedly, consider it similar to how a programmer defines a function $f = lambda x. e$ with its contract $kappa$ in a module. Then in places where $f$ is used, it is being rewritten into a monitor, $mon(k,l,j,kappa,lambda x. e)$ where $kappa$ is the contract over the protected expression $lambda x. e$, and $k,l,j$ are labels which will be discussed later. Mainly there are three contract types: flat $flat(e)$, functional $kappa_1 -> kappa_2$, and dependent $dep(kappa_1,lambda x. kappa_2)$. There are several semantics for monitors, for illustration purposes, we assume the same semantics in @robert2002contracts. A monitor of flat contract triggers when the expression is a value,

// $mon(k,l,j,flat(e),v) cstep ife(apply(e,v),v,blame(k,j))$.

// A monitor over function contract will pad the expression (using lambdas) to install monitors to its argument, and result,

// $mon(k,l,j,kappa_1 -> kappa_2, e) cstep lambda x. mon(l,k,j,kappa_2,apply(e,mon(k,l,j,kappa_1,x)))$.

// Similarly for dependent contracts, but because the codomain contract can use the argument, this argument is also installed with a monitor,

// $mon(k,l,j,dep(kappa_1, lambda y. kappa_2), e) cstep lambda x. mon(l,k,j,kappa_3,apply(e,mon(k,l,j,kappa_1,x)))$,

// where $kappa_3$ is $kappa_2$ replacing every occurances of free variable $y$ to $mon(l,j,j,kappa_1,x)$.

// Readers may have noticed that monitor's labels are changed during execution of functional and dependent contracts monitors. The labels is useful for defining the blaming party, answering the sole question: "Who is responsible for breaking the violation?" The use of three labels and the exchanging of labels during reduction described above is taken from @christos2012complete's indy semantics. In the same work, the authors provide intermediate contract checking value, $check(k,j,e,v)$, as a way to hide away the flat contract if/else conditional code,

// $mon(k,l,j,flat(e),v) cstep check(k,j,apply(e,v),v)$,

// with $check(k,j,trueb,v) cstep v$ and $check(k,j,falseb,v) cstep blame(k,j)$

// The next three sections introduce additional contract models that are not part of the generic translation from #langc to #lange. They are worth discussing because they can be encoded using the translation [to some extend]. Readers primarily interested in the formal translation may skip ahead to the #langc language section, which defines its source language.

=== Examples

@contracts-example-1 illustrates a function protected with a monitor. This function should return a value that is even. When applied with 10, it is checked by the function's _domain contract_. Since the function does not impose any properties for its argument, the contract passes. The body of the function is executed normally, but its result must pass the function's _range contract_. Because 11 is not an even number, the program terminates with a blame.

#figure(
  stack(
    v(1em),
    grid(
      columns: (2em, auto, 4em),
      align: (left, left, right),
      gutter: 0.8em,

      [],
      [$apply(mon(k,l,j,flat(lambda x. trueb) -> flat(kw("iseven")), lambda x. x + 1), 10)$],
      [],

      [$cstep$],
      [$apply(guard(lambda x. x + 1, flat(lambda x. trueb) -> flat(kw("iseven")), k, l, j),10)$],
      [],

      [$cstep$],
      [$mon(k,l,j, flat(kw("iseven")), apply((lambda x. x + 1), mon(l,k,j, flat(lambda x. trueb), 10)))$],
      [],

      [$cstep$],
      [$mon(k,l,j, flat(kw("iseven")), apply((lambda x. x + 1), guard(10, lambda x. trueb, l, k, j)))$],
      [],

      [$cstep$],
      [$mon(k,l,j, flat(kw("iseven")), apply((lambda x. x + 1), check(l,j, apply((lambda x. trueb), 10), 10)))$],
      [],

      [$cstep$],
      [$mon(k,l,j, flat(kw("iseven")), apply((lambda x. x + 1), check(l,j, trueb, 10)))$],
      [],

      [$cstep$],
      [$mon(k,l,j, flat(kw("iseven")), apply((lambda x. x + 1), 10))$],
      [],

      [$cstep1$],
      [$mon(k,l,j, flat(kw("iseven")), 11)$],
      [],

      [$cstep$],
      [$check(k,l,apply(kw("iseven"),11), 11)$],
      [],

      [$cstep1$],
      [$check(k,l,falseb, 11)$],
      [],

      [$cstep1$],
      [$blame(k,j)$],
      [],
    ),
    v(1em),
  ),
  caption: [Contracts in action]
) <contracts-example-1>

@contracts-example-2 illustrates a dependent contract whose domain is itself a function contract. Let $kappa_f = flat(lambda x. iszero(x)) -> flat(lambda x. trueb)$, $f = lambda h. 0$, and $g = lambda x. x$. The dependent contract $kappa_d = dep(kappa_f, lambda h. flat(lambda z. iszero(apply(h,1))))$ calls its function argument while checking the result. The function $f$ returns 0 without calling $g$, but the contract calls $g$ with 1. Since $kappa_f$ requires the argument to be zero, this call fails and blames the contract party $j$.

#figure(
  stack(
    v(1em),
    grid(
      columns: (2em, auto, 4em),
      align: (left, left, right),
      gutter: 0.8em,

      [], [$apply(mon(k,l,j,kappa_d,f),g)$], [],
      [$cstep$], [$apply(guard(f,kappa_d,k,l,j),g)$], [],
      [$cstep$],
      [$mon(k,l,j,flat(lambda z. iszero(apply(mon(l,j,j,kappa_f,g),1))),
        apply(f,mon(l,k,j,kappa_f,g)))$], [],
      [$cstep1$],
      [$mon(k,l,j,flat(lambda z. iszero(apply(mon(l,j,j,kappa_f,g),1))),0)$], [],
      [$cstep$],
      [$check(k,j,apply((lambda z. iszero(apply(mon(l,j,j,kappa_f,g),1))),0),0)$], [],
      [$cstep$], [$check(k,j,iszero(apply(mon(l,j,j,kappa_f,g),1)),0)$], [],
      [$cstep$], [$check(k,j,iszero(apply(guard(g,kappa_f,l,j,j),1)),0)$], [],
      [$cstep$],
      [$check(k,j,iszero(mon(l,j,j,flat(lambda x. trueb),
        apply(g,mon(j,l,j,flat(lambda x. iszero(x)),1)))),0)$], [],
      [$cstep$],
      [$check(k,j,iszero(mon(l,j,j,flat(lambda x. trueb),
        apply(g,check(j,j,apply((lambda x. iszero(x)),1),1)))),0)$], [],
      [$cstep1$],
      [$check(k,j,iszero(mon(l,j,j,flat(lambda x. trueb),
        apply(g,check(j,j,falseb,1)))),0)$], [],
      [$cstep1$], [$blame(j,j)$], [],
    ),
    v(1em),
  ),
  caption: [A dependent contract calling its function argument]
) <contracts-example-2>

// === Language Model

// We define #langc language extended from #langb with monitors. The surface syntax has only one new expression, $mon(k,l,j,kappa,e)$ where $kappa$ is a contract, $e$ is the protected expression, and $k,l,j$ are labels for blame reporting. There are three main types of contracts, flat $flat(e)$, functional $kappa_1 -> kappa_2$, and dependent $dep(kappa_1,lambda y. kappa_2)$. #langc provides tuple contracts as syntactic sugar applied recursively,

// $mon(k,l,j,tuple(kappa_1,kappa_2),e) = apply((lambda v. tuple(mon(k,l,j,kappa_1,injl(v)),mon(k,l,j,kappa_2,injr(v)))),e)$

// During evaluation, two new expressions might arise, $check(k,j,e,v)$ and $blame(k,j)$, along with a new value type $guard(v,kappa,k,l,j)$. During evaluation if a contract is violated it reduces into $blame(k,j)$ with two labels $k$ the party responsible (to blamed), and $j$ the contract-providing party. A monitor of a flat contract reduces to a $check(k,j,e,v)$, indicating that a contract checking is happening, with checking code $e$ and value $v$. Checking code evaluates to true or false. If true, check is removed off value, else blame is returned using the labels of check. For other contract types, a monitor turns into a dormant $guard(v,kappa,k,l,j)$, treated as a function value. When it is applied to a value, it breaks down the contract to monitor the argument, and the function's result.

// To type #langc, we need a new type $con(tau)$ to type contracts. The type of flat contract depends on the predicate input type, $flat(e) : con(tau)$ where $e : tau -> boolt$. Functional and dependent contracts are typed $con(tau_1 -> tau_2)$ each corresponse to domain contract type, and codomain contract type. A monitor $mon(k,l,j,kappa,v)$ is then typed easily by making sure the contract $kappa$ is typed $con(dot)$ of protected value $v$ type. To ensure type safety is hold, $check(k,j,e,v)$, $guard(v,kappa,k,l,j)$ and $blame(k,j)$ expressions must be typed as well. $blame(k,j)$ accepts any type; $check(k,j,e,v)$ checking code $e$ is typed bool, and the expression type resonates with value $v$; $guard(v,kappa,k,l,j)$ shares the same type with protected value $v$, with contract $kappa$ has contract type of type of $v$ as well.

=== Type Safety

#langc is safe by progress and preservation. Because the language can stop on blame expressions, the progress theorem is added an extra case.

#theorem(title: [#langc Type Safety])[

  1. If $type(dot, e, tau)$ and $e cstep e'$ then $type(dot,e',tau)$.
  2. If $type(dot, e, tau)$ then $e$ is a value or $e = blame(k,j)$ or $e cstep e'$ for some $e'$.
] <langc-Type-Safety>

=== Contract Erasure

#let erase(e) = $"erase"(#e)$

#langc satisfies the erasure theorem by erasure function $erase(e)$ as a homomorphic function over expressions $e in langc$ that removes monitors.

$erase(mon(k,l,j,kappa,e)) = erase(e)$.


#theorem(title: "Contract Erasure Theorem")[

  If $e' = erase(e)$ and $e cstep1 b$, then $e' step1 b$.
] <langc-contract-erasure>

#include "/models/contracts.typ"
#include "/models/contracts-type-rules.typ"
#include "/models/contracts-reduction-rules.typ"
