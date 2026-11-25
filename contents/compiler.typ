#import "/setup.typ": setupdoc
#show: setupdoc

#import "@preview/simplebnf:0.1.2": *
#import "@preview/curryst:0.6.0": rule, prooftree, rule-set
#import "@preview/great-theorems:0.1.2": great-theorems-init, mathblock

#import "/models/language.typ": *
#import "/proofs/setup.typ": appendix-theorem, appendix-lemma, appendix-number, proof, rn, mathcounter

#import "/utils.typ": load-bib, no-ref

#show: no-ref

#show: great-theorems-init

#let theorem = appendix-theorem
#let lemma = appendix-lemma
#let corollary = mathblock(blocktitle: "Corollary", counter: mathcounter, numbering: "1.1")

= Compiler <chapter-compiler>

In this chapter we describe a compiler from #langc to #lange. Before the formal compilation rules are introduced, we give a short tour on the analysis of designing the rules. First off, the rules are inspired by the compilation of @robert2013icfp. All contracts can be compiled recursively by padding a new lambda for functional contracts, unfolding until flat contract. Through observation, instead of compiling flat contracts into $ife(apply(p,v),v,"blame")$, this phrase is pushed into the handler and an effect is performed. Immediately, we can see an easy compilation strategy.

$apply(handler({effcheck^1 -> lambda \_. lambda k. ife(apply(p,v),apply(k,v),"blame")}, m:s), (lambda \_. (apply(perform(effcheck^1), unit))))$

There are two main questions to this approach that when answered, it shows why this is undesired. First, do we need a different effect for each different contract? Consider if each contract is given a different effect and stack the handler together, then the compiler must carefully order them handlers. Consider two handlers $h_1,h_2$ nested in that order resolving effect $epsilon_1,epsilon_2$ respectively. If effect $epsilon_1$ is invoked first, the handler $h_2$ is pushed into the continuation. If the condition code triggers $epsilon_2$, handler $h_2$ is not in-scope to resolve. This problem is why a single handler should be used. By using tuples, or similar techniques to encode the predicate, value, and even blame label into the first argument of handler, we can make a generic handler for any contract checking code.

$apply(handler({effcheck -> lambda tuple(l,tuple(p,v)). lambda k. ife(apply(p,v),apply(k,v),eblame(l))}, m:s), (lambda \_. (apply(perform(effcheck), tuple(l,tuple(p,v))))))$
#v(1em)

Where writing $lambda tuple(l,tuple(p,v))$ is a short hand to deconstruct the tuples, which can be done through tuple projection. After this construction, all contract checking can be unified under a single effect $effcheck$.

The second question asks where should handler(s) be put? Obviously it can be placed directly where the effect is performed. We call this an _in-place handler_ placement. Then we experiment whether we can pull the handler far away from the effect site. Without changing the handler, we try installing it at the top most place of the program. For functional contracts, this handler works. However, dependent contracts will get stuck with this handler, as shown in the example of @naive-handler-stuck.

#figure(caption: "Naive handler stuck")[

$
h_("naive") &= {effcheck -> lambda tuple(l,tuple(e,v)). lambda k. ife(apply(e,v),apply(k,v),eblame(l))} \
&#text([where $lambda tuple(l,tuple(e,v))$ deconstructs the value into tuple pattern])
$

#align(left, stack(
  grid(
    columns: (auto, auto),
    align: (left, left),
    gutter: 1em,

    [], [$apply(mon(k,l,j,dep(flat(e_1), lambda y. flat(e_2)), f), 42)$],
    [], grid.cell(align: right, [where $e_1 = lambda x. trueb$, $e_2 = lambda x. x > y$, and $f = lambda x. x + x$]),
    [$#compiles-into$], [$apply((lambda x_1. apply(perform(effcheck, tau: numt), tuple(k, tuple(e_3, apply(f, (apply(perform(effcheck, tau: numt), tuple(l, tuple(e_1, x_1))))))))), 42)$],
    [], grid.cell(align: right, [where $e_3 = e_2[y:=apply(perform(effcheck, tau: numt), tuple(l, tuple(e_1, x_1)))]$]),
  ),
  v(1em),
  line(length: 100%),
  v(1em),

  grid(
    columns: (auto, auto),
    align: (left, left),
    gutter: 1em,

    [], [$apply(handler(h_"naive", m: d), lambda \_. (apply(lambda x_1. apply(perform(effcheck, tau: numt), tuple(k, tuple(e_3, apply(f, (apply(perform(effcheck, tau: numt), tuple(l, tuple(e_1, x_1)))))))), 42)))$],

    [$estep$], [$handle(h_"naive", (apply(lambda x_1. apply(perform(effcheck, tau: numt), tuple(k, tuple(e_3, apply(f, (apply(perform(effcheck, tau: numt), tuple(l, tuple(e_1, x_1)))))))), 42)), m: d)$],
    [$estep$], [$handle(h_"naive", apply(perform(effcheck, tau: numt), tuple(k, tuple(e'_3, apply(f, (apply(perform(effcheck, tau: numt), tuple(l, tuple(e_1, 42)))))))), m: d)$],
    [], grid.cell(align: right, [where $e'_3 = e_2[y:=apply(perform(effcheck, tau: numt), tuple(l, tuple(e_1, 42)))]$]),
    [$estep1$], [$handle(h_"naive", apply(perform(effcheck, tau: numt), tuple(k, tuple(e'_3, apply(f, 42)))), m: d)$],
    [$estep1$], [$handle(h_"naive", apply(perform(effcheck, tau: numt), tuple(k, tuple(e'_3, 84))), m: d)$],
    [$estep1$], [$ife(apply(e'_3,84),apply((lambda x. handle(h_"naive", x, m: d)),84),eblame(k))$],
    [$estep1$], [$ife(84 > (apply(perform(effcheck, tau: numt), tuple(l, tuple(e_1, 42)))), apply((lambda x. handle(h_"naive", x, m: d)),84),eblame(k))$],
    [], [_stuck_]
  ),
))

] <naive-handler-stuck>


The reason why the above handler cannot work with dependent contracts is because during the handling of the contract, it may call into another contract. But because it is currently handling the contract, there is no handler to handle the nested contract effect. By abusing the recursive function $mu$, we can construct a more elegant wrapper that solves dependent contracts effects. Through our experiement, we have two versions of the wrapper, one that uses deep handler, and one that uses shallow handler. All three variants preserve the semantics: the in-place handler and the deep and shallow whole-program handlers.

A whole-program handler works through our experiments, and is also proven. But can we move the handler closer? A quick answer is "No". A good answer is "It depends". The problem arises when we try to push the handler deeper is when an effect is stored inside a lambda. Consider the program in @handler-placement-analysis, the program is an application between $g$ and the argument. The argument runs some contract checking before returning a function $f$. By the analysis, if $g$ does not call $f$, the handler can be pushed to near $mon(k',l',j',e',v')$. Because $f$ is invoked, placing the handler only around the argument computation does not cover the later check inside $f$; a handler around the whole program covers both. This case is a simple case to demonstrate the placement problem. Readers can consider cases where variables are bounded where each of them may or may not have a contract. Therefore, a recursive/homomorphic compiler is not suitable to analyze the absent or presence of such effect.

#figure(caption: "Handler placement analysis case")[
  $
  f &= lambda x. mon(k,l,j,e,x) \
  g &= lambda f. apply(f,1) \
  "main" &= apply(g,(apply((lambda y. f),(mon(k',l',j',e',v')))))
  $
] <handler-placement-analysis>

== Formal Model

From the analysis, we have two compilation rule #rn("C-in-place"), for compilation with in-place handlers, and #rn("C-whole-program"), for compilation with a whole-program handler. Formally they are defined using the following judgements:

- $compile(type(Gamma,e,tau),e',m:l)$ for compilation with in-place handlers
- $compile(type(Gamma,e,tau),e')$ for compilation with a whole-program handler

The compilation rule $compile(type(Gamma,e,tau),e')$ is read as "under environment $Gamma$, expression $e in langc$ has type $tau$ can be compiled into $e' in lange$ using whole-program handler", and similarly for $compile(type(Gamma,e,tau),e',m:l)$ but using in-place handlers. Both compilers are recursive and homomorphic over expression $e in langc$. The compilers are defined using a type-directed compilation because we compile from typed $langc$ to typed $lange$. The only difference between the two compilation rules is the flat contract compilation. Where the in-place handlers compiler place the handler at effect perform site, and whole-program handler does not. For flat contract, we pick a pre-defined effect $heffcheck$ with an operation $effcheck$ that is defined in $Sigma$ during type checking the target program as:

$
effcheck : forall alpha. tuple(blab, tuple(teff(alpha,effs(heffcheck),boolt),alpha)) -> alpha in Sigma(heffcheck)
$

Function contract compilation rule #rn("Compile-Func") for $mon(k,l,j,kappa_1 -> kappa_2, e)$ is padded into a lambda function applied with compiled $e$, to preserve the evaluation ordering. Similarly for dependent contract compilation rule #rn("Compile-Dep") for $mon(k,l,j,dep(kappa_1, lambda y. kappa_2), e)$, but it must carefully resolve the dependent argument. Both of these rules require fresh variables which are picked such that it does not match free variables appear in the to-be-compiled expression. The compilations assume effects $effs(heffcheck)$ for all lambdas, handlers, and performs. This is done through a type conversion, $tau^*$, defined in @type-conversion. The compilation rules for contracts are provided in @compiler-rules, other rules are omitted and assumed through recursiveness and homomorphic over expression $e in langc$.

From the previous section analysis, a whole-program handler is required. To provide the handler, we provide wrapper function that takes the compiled program. We provide three translations $rn("T1"), rn("T2"), rn("T3")$ from well-typed #langc to #lange, these translations preserve the source program semantics.

#let wrapd = $kw("wrap")_d$
#let wraps = $kw("wrap")_s$

#figure(caption: [Translation from well-typed #langc to #lange])[

$
rn("T1")(e) &= apply(wrapd[tau^*], (lambda \_ : unit. e')) &&"where" compile(type(dot,e,tau),e') \
rn("T2")(e) &= apply(wraps[tau^*], (lambda \_ : unit. e')) &&"where" compile(type(dot,e,tau),e') \
rn("T3")(e) &= e' &&"where" compile(type(dot,e,tau),e',m:l) \
$

$
#let hc = $effs(heffcheck)$
#let hcheck = $kw("H")$

wrapd = & mu w : forall alpha. teff((teff(unit,hc,alpha)),mteff,alpha). Lambda alpha. lambda f : teff(unit,hc,alpha). apply(handler(h_w, m: d), f) \
h_w = & {effcheck -> Lambda beta. lambda tuple(l,tuple(e,v)). lambda k : teff(beta,mteff,alpha). ife(apply(w[boolt], (lambda \_ : unit. apply(e,v))),apply(k,v),eblame(l))} \
wraps = & Lambda alpha. med lambda f: unit -> alpha. apply(hcheck, f) \
hcheck = & mu h. handler({effcheck -> lambda tuple(l,tuple(e,v)). lambda k. apply(h,(lambda \_. ife(apply(e,v),apply(k,v),eblame(l))))}, m: s)
$
] <translations>


#include "/models/compiler.typ"


== Compiler Guarantees

=== Compiler type equivalence

The compiler should preserve the type up to equivalence of $tau^*$. The in-place handler compiler produces expression with no effect because the flat contract has a handler. The whole-program handler compiler produces expression with a effect $heffcheck$. As a corollary, this applies for closed-program compilation as well.

#let tc(t) = $#t^*$
#let hc = $effs(heffcheck)$

#theorem(numbering: "1.1", title: "In-Place Compiler Type Equivalence")[

  If $compile(type(Gamma,e,tau),e',m:l)$, then $type(tc(Gamma),e',tc(tau),eff:mteff)$.
] <compiler-type-ts-in-place>

#theorem(numbering: "1.1", title: "Whole-Program Compiler Type Equivalence")[

  If $compile(type(Gamma,e,tau),e')$, then $type(tc(Gamma),e',tc(tau),eff:hc)$.
] <compiler-type-ts-preservation>

#corollary(title: "Closed-Program In-Place Compiler Type Equivalence")[

  If $compile(type(dot,e,tau),e',m:l)$, then $type(dot,e',tc(tau),eff:mteff)$.
] <compiler-type-ts-in-place-closed>

#corollary(title: "Closed-Program Whole-Program Compiler Type Equivalence")[

  If $compile(type(dot,e,tau),e')$, then $type(dot,e',tc(tau),eff:hc)$.
] <compiler-type-ts-closed>

=== Translation type safety

From the compiler equivalence theorems, translation from well-typed source program produces a well-type target program. This follows the typing of $wrapd$ and $wraps$ for $rn("T1"),rn("T2")$ and a direct result from compiler equivalence for $rn("T3")$.

#theorem(numbering: "1.1", title: "T1 Type Safety")[
  If $type(dot,e,tau)$ and $rn("T1")(e) = e'$, then $type(dot,e',tc(tau),eff:mteff)$.
] <compiler-type-ts-effect-safety>

#theorem(numbering: "1.1", title: "T2 Type Safety")[
  If $type(dot,e,tau)$ and $rn("T2")(e) = e'$, then $type(dot,e',tc(tau),eff:mteff)$.
] <compiler-type-ts-effect-safety-shallow>

#theorem(numbering: "1.1", title: "T3 Type Safety")[
  If $type(dot,e,tau)$ and $rn("T3")(e) = e'$, then $type(dot,e',tc(tau),eff:mteff)$.
] <compiler-type-ts-effect-safety-local>

=== Translation equivalence

Let $r = b | blame(k,j)$, then the translations preserve semantics of source well-typed programs.

#theorem(numbering: "1.1", title: "T1 Equivalence")[
  If $rn("T1")(e) = e'$ and $e cstep1 r$, then $e' estep1 r$.
] <compiler-correctness>

#theorem(numbering: "1.1", title: "T2 Equivalence")[
  If $rn("T2")(e) = e'$ and $e cstep1 r$, then $e' estep1 r$.
] <compiler-shallow-correctness>

#theorem(numbering: "1.1", title: "T3 Equivalence")[
  If $rn("T3")(e) = e'$ and $e cstep1 r$, then $e' estep1 r$.
] <compiler-local-correctness>

== Contracts Hijacking (and Option Contracts)

#let option(kappa,e) = $ckw("option")(#kappa,#e)$
#let optionv(k,l,j,kappa,e) = $ckw("O")^(#k,#l)_#j (#kappa,#e)$
#let exercise(o) = $ckw("exercise")(#o)$

@christos2013option defined option contracts. A value attached with an option contract is dormant, unless it is being forced to execute. The option contract, $option(dep(kappa_1,lambda x. kappa_2),e)$, is two-phase validation when applied under the monitor. First the monitor ensures the value matches some preliminary checking $e$. Once the preliminary check completes, it converts to an option check value, $optionv(k,l,j,kappa,v)$. This option check value acts as a faded monitor. Only when it is being forced, would it become a working monitor and starts checking contracts,

$exercise(optionv(k,l,j,kappa,v)) cstep mon(k,l,j,kappa,v)$

Our translation, using whole-program handler, can simulate to some extend of option contracts. Users can provide a different handler scope inside the program, alternating the contract execution policy. Immediately, a do-nothing handler ${effcheck -> Lambda alpha. lambda x. lambda k. apply(k,x)}$ simulates optional contract checking. However, this approach changes the environment, rather than a monitor wrapper over the object. Consider the program where an option contract protected function $mon(k,l,j,option(kappa_f, "tester"),f)$ applied with and use a non-optional contract protected function $mon(m,n,o,kappa_g,g)$. Without forcing optional contract, contracts in $g$ still executes. However, if we adapt to using handlers, the whole environment around the application is modified, and contracts in $g$ is skipped.

This intercepting handler is best described as contract hijacking. It allows users to change the logic of contract checking dynamically. While disabling contract checking relaxes the runtime contrains, it also raises some security concerns to users disabling checks to critical code segments.

== States (and Trace Contracts) <compiler-formal-states>

=== Trace Contracts

#let trace(v_1,v_2) = $ckw("tr") #v_1 med #v_2$
#let co(alpha,v) = $ckw("co") #alpha med #v$

@cameron2023trace describes a novel contract type that deals with states. A trace contract $trace(v_b,v_p)$ has an initializer $v_b$, and a predicate $v_p$. The initializer takes a collector $co(alpha,v_p)$ and returns a contract. The idea is that $v_b$ is the contract of the protected value, but because it requires a collector, it must receives the collector to bind it in the contract scope. The collector itself is a contract that runs every input against the predicate $v_p$. The collector is generated on-the-fly during monitor execution,

$mon(k,l,j,trace(v_b,v_p),e) cstep mon(k,l,j,apply(v_b,(co(alpha,v_p))),e)$, where $alpha$ is a new address.

With the collector, when the monitor is used/applied with an argument, it is added into the colletor. Then the predicate checks the collector list,

$apply(mon(k,l,j,co(alpha,v_p),f),v) cstep apply(mon(k,l,j,apply(v_p,("add!" alpha med v)),f),v)$,

where $("add!" alpha med v) cstep alpha$, and updates the global list with $alpha |-> v$

During run-time, a global list of addresses is maintained. It is repsonsible for the generation of $alpha$ address each time the collector is created. Using this global list, predicate trace contract predicate $v_p$ can access previous contracts invoked values.

=== States and Trace Contracts Adaptation

All translations are capable of encoding states by providing them a states handler. This handler, with get and set operations for each states, is initialized with the initial values for each state. Different states are supported through lambdas encoding or tuples. @states-handler demonstrates a states handler for two different states value, with a wrapper that takes in the translated program. The handler is deep to allow multiple calls into the states handler, if shallow handler is used, then use the recursive form like #wraps handler.

#figure(caption: [States handler])[
  $
  H &= handler(h_s, m: d) \
  h_s(effstateget^1) &= lambda u. lambda k. lambda s_1. lambda s_2.
    apply(apply(k,s_1),s_1) \
  h_s(effstateset^1) &= lambda s'_1. lambda k. lambda s_1. lambda s_2.
    apply(apply(k,s'_1),s'_1) \
  h_s(effstateget^2) &= lambda u. lambda k. lambda s_1. lambda s_2.
    apply(apply(k,s_2),s_2) \
  h_s(effstateset^2) &= lambda s'_2. lambda k. lambda s_1. lambda s_2.
    apply(apply(k,s'_2),s'_2) \

  e & "is source program in" langc \
  e' &= rn("T1")(e) "or" rn("T2")(e) "or" rn("T3")(e) \


  kw("wrap") &= lambda f. apply(apply(apply(H,(lambda \_. apply((lambda r. lambda s_1. lambda s_2. r),f))),s_1),s_2)
  $
] <states-handler>

The state handler can be attached into the #wraps handler. Because the the translation #rn("T2") is neatly placed under a handler across the program invocation, states handler can be merged into contract checking handler as in @shallow-state-handler.

#figure(caption: [States handler merged in #rn("T2")])[
  $
  H &= mu H. handler(h_s, m: s) \
  h_s(effcheck) &= lambda tuple(l,tuple(p,v)). lambda k. lambda s.
    apply(apply(H,(lambda \_. ife(apply(p,v),apply(k,v),eblame(l)))),s) \
  h_s(effstateget) &= lambda u. lambda k. lambda s.
    apply(apply(H,lambda \_. apply(k,s)),s) \
  h_s(effstateset) &= lambda s'. lambda k. lambda s.
    apply(apply(H,lambda \_. apply(k,s')),s'). \
  kw("wrap")_s &= lambda f. apply(apply(H,(lambda \_. apply((lambda r. lambda s. r),f))),s)
  $
] <shallow-state-handler>

Because the formal model by @cameron2023trace is un-typed with first-class contracts, we can only give a suggestion how one should adapt trace contracts into the states handler. For each trace contract $trace(v_b,v_p)$, a new state is defined with an identifier. Contract constructor is not needed anymore since the state is created before the program run. The predicate $v_p$ is invoked on each function's input can obtain the state through get operation, and set the new state using set operation of the given state.

It is suggestive that one moves away from trace contracts, and introduce their own state contract that is easier for compilation. Our OCaml implementation, in @chapter-implementation, does exactly this.

== Effectful Contracts

=== Effectful Software Contracts

#let coneff(kappa_1,kappa_2) = $#kappa_1 gt.closed #kappa_2$

@cameron2024effectful shows how contracts should be updated to integrate them into effect handlers languages. They classify these four terms, of which three of them are added to build the Effectful Contracts system:

- *Main-Effect Handlers* which is the effect handler for _program_ code,
- *Main-Effect Contracts* which is the contract system for _program_ code's effects,
- *Contract-Effect Handlers* which is the effect handler for _contract_ code,
- *Contract-Effect Contracts* which is the contract system for _contract_ code,

Main-Effect Handlers is the normal effect handler system that #lange has provided. The other three extensions are explained below.

*Main-Effect Contracts* $coneff(kappa_1,kappa_2)$ inserts monitors around the effect invocation, guarding the invocation of an effect by the main program,

$
handle(h, mon(k,l,j,coneff(kappa_1,kappa_2),E[apply(perform(op),v)]), m:d) \
quad cstep apply(apply(f,mon(k,l,j,kappa_1,v)),(lambda x. handle(h,E[mon(l,k,j,kappa_2,x)],m:d))), \
#text[where $op -> f in h$]
$

As can be seen, the handler body $f$ is invoked with a monitor protected value, and the continuation protects the result of the handler. However, this only cares for one monitor. Generalized, users can write programs with nested effectful contracts,

$mon(k,l,j,coneff(kappa_1,kappa_2), mon(m,n,o,coneff(kappa_3,kappa_4), v))$.

During effect perform, all contracts will be merged, so the effect's input is protected with $mon(l,k,j,kappa_1,mon(n,m,o,kappa_3,v))$, and similarly for the effect's result. The reduction rule above assumes all effects are intercepted the same, which is not desired. The reduction can be extended to include effect filtering, either by marking monitor with allowed effects, or contracts bind the effect when called. Regardless, this requires effect name as a value.

*Contract-Effect Handler* provides handlers for contract code's effect. Their argument was that effects invoked by the program code and the contract code must be non-inteference. Their solution is to create a new handler semantics, $handle(h, eff:lozenge.stroked,e)$, for contracts that only contract code can execute.

*Contract-Effect Contracts* provides an automatic to install handlers without writing the handler. This is embedded as a contract type, $lozenge.stroked h in kappa$. They allow conjuction of contracts with this, $kappa inter.sq lozenge.stroked h$ and during runtime, the corresponding Contract-Effect Handler $handle(h, eff:lozenge.stroked, dot)$ is created.

=== Main-Effect Contracts Adaptation

Our translation can be extended to provide Main-Effect Contracts. Assumed that effectful contract $mon(k,l,j,coneff(kappa_1,kappa_2),e)$, and other monitor expressions are added directly to $lange$, now protected expression $e$ can invoke effects. First, let $kappa_1,kappa_2$ are contracts that perform no effects, so only main program code can perform effects. Then, the translation for effectful contract is to create a new scoped handler over $e$. The below should describe our translation idea without focusing on typing.

#rule-set(
  prooftree(rule(
    name: [Compile-Effectful-Contract],
    $I = mon(k,l,j,kappa_1,x)$,
    $O = mon(k,l,j,kappa_2,apply(perform(op),I))$,
    $compile(type(Gamma\,x,O,tau_2), K)$,
    $h = { op -> Lambda alpha. lambda x. lambda k. apply(k,K) }$,
    $compile(type(Gamma,e_1,tau_1),e_2)$,
    $compile(type(Gamma,mon(k,l,j,coneff(kappa_1,kappa_2),e_1),tau_1), handle(h,e_2,m:d))$,
  ))
)

This compiler ensures that if we have nested effectful contracts, they will be invoked and the above handler(s) catchs. Of course, the main effect handler remains at the top. The checking order for input is inside-to-outside, and for output is outside-to-inside. Because the checking is subsequent, there should be no difference in semantics. However, this remains a suggestion without any proof.

=== Contract-Handler Contracts Adaptation

Contract-Effect Handlers and Contract-Handler Contracts are tricky to implement into our translation(s). These two pieces support contracts interaction, by using state-encoding handler. Because this handler is accessible to the contract code only, and it is generated during runtime, contracts can have different scope to access states. If scoping is not important, global state(s) can be used, as per trace contract adaptation, translation #rn("T2") has already supported contract interaction.

// #figure(caption: "Shallow check handler with contract-controlled state outside handler")[
//   $
//   H_1 &= mu H. handler(h_1, m: s) \
//   H_2 &= mu H. handler(h_2, m: d) \
//   h_1(effcheck) &= lambda tuple(l,tuple(p,v)). lambda k.
//     apply(H,(lambda \_. ife(apply(p,v),apply(k,v),eblame(l)))) \
//   h_2(effstateget) &= lambda u. lambda k. lambda s.
//     apply(apply(H,lambda \_. apply(k,s)),s) \
//   h_2(effstateset) &= lambda s'. lambda k. lambda s.
//     apply(apply(H,lambda \_. apply(k,s')),s'). \
//   kw("wrap")_s &= lambda f. apply(apply(H_2,(apply(H_1,lambda \_. f))),s)
//   $
// ] <shallow-state-handler-2>

However, if contract scoping is preferred, adapting this new contract type is not straightforward. If we look closely, wrappers $wrapd,wraps$ can appear in the program at many places, if we do not care about sharing states. Then, Contract-Handler Contracts can install a new handler scope, with the wrappers to handle contract checking. Doing it this way separates the checking of contract, and contract effect states. Following the semantics of Contract-Handler Contracts, the protected value must be a _function accepting one argument_. The following compilation should be suffice:

#rule-set(
  prooftree(rule(
    name: [Compile-ContractHandler],
    $compile(type(Gamma,e,tau_1 -> tau_2),e')$,
    $compile(type(Gamma,h,tau_h),h')$,
    $compile(type(Gamma,mon(k,l,j,lozenge.stroked h,e),tau_1 -> tau_2), apply((lambda f : tau_1 -> tau_2. lambda x : tau_1. apply(h',(lambda \_. wraps (lambda \_. apply(f,x))))), e'))$,
  ))
)

Where $compile(type(Gamma,h,tau_h),h')$ compiles the handler functions because they may contain monitors. The compiled program still need to be wrapped under $wrapd$ or $wraps$. During runtime, the contracts' effects are handled under the contract handler scope. Because $wraps (lambda \_. apply(f,x))$ returns a value (or blame), the contract handler is removed on completion.

=== Adaption conclusion

These are suggestive compilations/adaptions of Effectful Software Contracts. While the adaptations of Main-Effect Contracts, and Contract-Handler Contracts adaptions are reasonable, we have not proven their semantics equivalence compared to the original semantics. However, in @chapter-implementation, we show that our #rn("T2") translation with support for Main-Effect Contracts, and using the global state is sufficient to implement the capabilities mentioned by @cameron2024effectful: #rn("ALLOW CALL"), #rn("EXCEPTION"), #rn("FRAMING"), #rn("GHOST STATE"), #rn("MUST CALL"), #rn("NON-REENTRANCE"), #rn("PURE"), #rn("RESTRICTED EFFECTS"), #rn("TERMINATION"), and #rn("UNION CONTRACTS").
