#import "/setup.typ": setupdoc
#show: setupdoc

#import "/models/language.typ": *
#import "/utils.typ": load-bib, no-ref

#show: no-ref

= Software Contracts and #langc <chapter-contracts>

Software contracts was first mentioned in designed by contracts techniques, first appeared in the Eiffel language @meyer1992eiffel. In their purest construction, functions can be annotated with pre-condition for its parameters and a post-condition for its result. During run-time, arguments are checked against the pre-conditions, and the result is checked against the post-condition. The use of pre-condition and post-condition as run-time checks are commonly referred to as _contracts_. The contract system of Eiffel was very basic, it can only support contracts for basic value and cannot work with higher-order functions. In @robert2013icfp, the authors introduce higher-order contracts through the use of obligations, which are referred to as monitors in today's literature.

Contracts are surface syntax while monitors are run-time wrappers. Contracts are specified separatedly, consider it similar to how a programmer defines a function $f = lambda x. e$ with its contract $kappa$ in a module. Then in places where $f$ is used, it is being rewritten into a monitor, $mon(k,l,j,kappa,lambda x. e)$ where $kappa$ is the contract over the protected expression $lambda x. e$, and $k,l,j$ are labels which will be discussed later. Mainly there are three contract types: flat $flat(e)$, functional $kappa_1 -> kappa_2$, and dependent $dep(kappa_1,lambda x. kappa_2)$. There are several semantics for monitors, for illustration purposes, we assume the same semantics in @robert2013icfp. A monitor of flat contract triggers when the expression is a value,

$mon(k,l,j,flat(e),v) cstep ife(apply(e,v),v,blame(k,j))$.

A monitor over function contract will pad the expression (using lambdas) to install monitors to its argument, and result,

$mon(k,l,j,kappa_1 -> kappa_2, e) cstep lambda x. mon(l,k,j,kappa_2,apply(e,mon(k,l,j,kappa_1,x)))$.

Similarly for dependent contracts, but because the codomain contract can use the argument, this argument is also installed with a monitor,

$mon(k,l,j,dep(kappa_1, lambda y. kappa_2), e) cstep lambda x. mon(l,k,j,kappa_3,apply(e,mon(k,l,j,kappa_1,x)))$,

where $kappa_3$ is $kappa_2$ replacing every occurances of free variable $y$ to $mon(l,j,j,kappa_1,x)$.

Readers may have noticed that monitor's labels are changed during execution of functional and dependent contracts monitors. The labels is useful for defining the blaming party, answering the sole question: "Who is responsible for breaking the violation?" The use of three labels and the exchanging of labels during reduction described above is taken from @christos2012complete's indy semantics. In the same work, the authors provide intermediate contract checking value, $check(k,j,e,v)$, as a way to hide away the flat contract if/else conditional code,

$mon(k,l,j,flat(e),v) cstep check(k,j,apply(e,v),v)$,

with $check(k,j,trueb,v) cstep v$ and $check(k,j,falseb,v) cstep blame(k,j)$

The next three sections introduce additional contract models that are not part of the generic translation from #langc to #lange. They are worth discussing because they can be encoded using the translation [to some extend]. Readers primarily interested in the formal translation may skip ahead to the #langc language section, which defines its source language.

== Option Contracts

#let option(kappa,e) = $ckw("option")(#kappa,#e)$
#let optionv(k,l,j,kappa,e) = $ckw("O")^(#k,#l)_#j (#kappa,#e)$
#let exercise(o) = $ckw("exercise")(#o)$

In @christos2013option, the authors define option contracts. A value attached with an option contract is dormant, unless it is being forced to execute. The option contract, $option(dep(kappa_1,lambda x. kappa_2),e)$, is two-phase validation when applied under the monitor. First the monitor ensures the value matches some preliminary checking $e$. Once the preliminary check completes, it converts to an option check value, $optionv(k,l,j,kappa,v)$. This option check value acts as a faded monitor. Only when it is being forced, would it become a working monitor and starts checking contracts,

$exercise(optionv(k,l,j,kappa,v)) cstep mon(k,l,j,kappa,v)$

== Trace Contracts

#let trace(v_1,v_2) = $ckw("tr") #v_1 med #v_2$
#let co(alpha,v) = $ckw("co") #alpha med #v$

#pad(left: 2em)[
Disclaimer: This section adapts the formal model loosely for demonstration purposes.
]


@cameron2023trace describes a novel contract type that deals with states. A trace contract $trace(v_b,v_p)$ has an initializer $v_b$, and a predicate $v_p$. The initializer takes a collector $co(alpha,v_p)$ and returns a contract. The idea is that $v_b$ is the contract of the protected value, but because it requires a collector, it must receives the collector to bind it in the contract scope. The collector itself is a contract that runs every input against the predicate $v_p$. The collector is generated on-the-fly during monitor execution,

$mon(k,l,j,trace(v_b,v_p),e) cstep mon(k,l,j,apply(v_b,(co(alpha,v_p))),e)$, where $alpha$ is a new address.

With the collector, when the monitor is used/applied with an argument, it is added into the colletor. Then the predicate checks the collector list,

$apply(mon(k,l,j,co(alpha,v_p),f),v) cstep apply(mon(k,l,j,apply(v_p,("add!" alpha med v)),f),v)$,

where $("add!" alpha med v) cstep alpha$, and updates the global list with $alpha |-> v$

During run-time, a global list of addresses is maintained. It is repsonsible for the generation of $alpha$ address each time the collector is created. Using this global list, predicate trace contract predicate $v_p$ can access previous contracts invoked values.

== Effectful Contracts

#pad(left: 2em)[
Disclaimer 1: This section uses some terminologies of effect handlers. Readers are advised to read @chapter-effects to understand about effect handlers before reading this section.
]

#pad(left: 2em)[
Disclaimer 2: This section adapts the formal model loosely for demonstration purposes.
]

#let coneff(kappa_1,kappa_2) = $#kappa_1 gt.closed #kappa_2$

@cameron2024effectful shows how contracts should be updated to integrate them into effect handlers languages. First, a contract to constrain effects. Since effects invocation is similarly to function application, the effect contract $coneff(kappa_1,kappa_2)$ inserts checks around the effect invocation,

$mon(k,l,j,coneff(kappa_1,kappa_2),E[apply(perform(eff),v)]) cstep E[mon(k,l,j,kappa_2,apply(perform(eff),mon(l,k,j,kappa_1,v)))]$.

However, this transition only happens during an effect invocation. ...???

But the program code is not the only place where effects can be invoked, contracts can invoke them too. The author suggests a different handler semantics for effects inside contract, and provide a special contract that installs this contract-effect-handler. This construction ensures that if the contract requires a separated handler (for state management), it is given a separated context, and program code cannot intefere with the context. However, contracts can still invoke program's effects.

== #langc language

This section introduces our #langc language. First, we provide some examples. @contracts-example-1 illustrates a function protected with a monitor. This function should return a value that is even. When applied with 10, it is checked by the function's _domain contract_. Since the function does not impose any properties for its argument, the contract passes. The body of the function is executed normally, but its result must pass the function's _range contract_. Because 11 is not an even number, the program terminates with a blame.

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

      [$cstep1$],
      [$blame(k,j)$],
      [],
    ),
    v(1em),
  ),
  caption: [Contracts in action]
) <contracts-example-1>

== Language Model

We define #langc, in @contracts-syntax, by extending the #langb language with contracts. Contracts protect an expression, ensuring that the evaluated value conform to the contracts defined. Contracts are defined for all possible types of value. Base values, including booleans and numbers, are trivial to enfore a contract on them. While functions need to check for both its argument and return result. Not only that, functions are first-class citizen in the language, and we can form higher-order functions. A contract for function may want to "see" the argument when checking the result, such is the idea of dependent contracts. Both contracts higher-order functions, and dependent contracts semantics are discussed in @robert2013icfp.

The language supports contracts for tuples. Their contracts will be applied individually during execution. Mutable cells contracts follow the work of @christos2011on, where a special contract type $refc(kappa)$ is used to protect the cell's value.

#include "/models/contracts.typ"

#include "/models/contracts-type-rules.typ"

When a contract violation occurs, a blame is thrown with the party, caller or callee. The semantics for correct blaming has been studied under @christos2011on and @christos2012complete. Following previous works, We use _indy_ semantics for dependent contracts. We use $guard(v,kappa,k,l,j)$ as the run-time proxy to value $v$ procted under a contract $kappa$. Guard is a value, the semantics adapt to usage of guards, and expand further, sometimes back to monitor to evaluate inner expressions. A guard on a basic value will trigger a $check(k,j,apply(e,v),v)$ and returns the value $v$ if it passes the predicate $e$, or returns a $blame(k,j)$ to party $k$ with contract location $j$. The evaluation rules for #langc is presented in @contracts-reduction-rules.

#include "/models/contracts-reduction-rules.typ"
