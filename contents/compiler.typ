#import "/setup.typ": setupdoc
#show: setupdoc

#import "@preview/simplebnf:0.1.2": *
#import "@preview/curryst:0.6.0": rule, prooftree, rule-set
#import "@preview/great-theorems:0.1.2": great-theorems-init

#import "/models/language.typ": *
#import "/proofs/setup.typ": appendix-theorem, appendix-lemma, appendix-number, proof

#import "/utils.typ": load-bib, no-ref

#show: no-ref

#show: great-theorems-init

#let theorem = appendix-theorem
#let lemma = appendix-lemma

= Compiler

Following the compiler of @robert2013icfp, we can compile all contracts recursively by padding a new lambda for functional contracts, unfolding until flat contract. Through observation, instead of compiling flat contracts into $ife(apply(p,v),v,"blame")$, this phrase is pushed into the handler and an effect is performed. Immediately, we can see an easy compilation strategy.

$apply(handler({effcheck^1 -> lambda \_. lambda k. ife(apply(p,v),apply(k,v),"blame")}, m:s), (lambda \_. (apply(perform(effcheck^1), unit))))$

There are two main questions to this approach that when answered, it shows why this is undesired. First, do we need a different effect for each different contract? Second, where should we put the handler? The first question is relatively yes, if we push the whole if/else clause into the handler. Which we can simplify by using tuples, or similar techniques for encoding the predicate, value, and even blame label into the first argument of handler. Using tuple, we can rewrite into:

$apply(handler({effcheck -> lambda tuple(l,tuple(p,v)). lambda k. ife(apply(p,v),apply(k,v),eblame(l))}, m:s), (lambda \_. (apply(perform(effcheck), tuple(l,tuple(p,v))))))$

Where we write $lambda tuple(l,tuple(p,v))$ as a short hand to deconstruct the tuples, which can be done through tuple projection. After this construction, all contract checking can be unified under a single effect $effcheck$. The second question is rather hard to answer. Obviously it can be placed directly where the effect is performed. We call this a _local compilation_ (of contracts into effects). Then we experiment whether we can pull the handler far away from its local position. Without changing the handler, we try installing it at the top most place of the program. For functional contracts, this handler works. However, dependent contracts will get stuck with this handler, as shown in the example of @naive-handler-stuck.

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


The reason why the above handler cannot work with dependent contracts is because during the handling of the contract, it may call into another contract. But because it is currently handling the contract, there is no handler to handle the nested contract effect. One may argue that if each contract is given a different effect and stack the handler together, it might solve this problem, but then we need to work out the order of the handler#footnote("Handler captures context, and if the outside handler is invoked first, the inside handler is now inside the continuation not outside, and it cannot handle effects called in condition code."). By abusing the recursive function $mu$, we can construct a more elegant wrapper that solves dependent contracts effects. Through our experiement, we have two versions of the wrapper, one that uses deep handler, and one that uses shallow handler. All three compiler versions, local, deep, shallow, preserve the semantics.

Careful readers may aware that the handler is pulled to the outside of the [compiled] program, and may also wonder if we can push it further inside the program (except local compilation). A quick answer is "No". A good answer is "It depends". The problem arises when we try to push the handler deeper is when an effect is stored inside a lambda. Consider the program in @handler-placement-analysis, the program is an application between $g$ and the argument. The argument runs some contract checking before returning a function $f$. By the analysis, if $g$ does not call $f$, the handler can be pushed to near $mon(k',l',j',e',v')$. However, because $f$ is invoked, we need to place the handler outside the whole program. This case is a simple case to demonstrate the placement problem. Readers can consider cases where variables are bounded where each of them may or may not have a contract. Therefore, a recursive/homomorphic compiler is not suitable to analyze the absent or presence of such effect.

#figure(caption: "Handler placement analysis case")[
  $
  f &= lambda x. mon(k,l,j,e,x) \
  g &= lambda f. apply(f,1) \
  "main" &= apply(g,(apply((lambda y. f),(mon(k',l',j',e',v')))))
  $
] <handler-placement-analysis>

== Formal Model

Our compiler is homomorphic over expression $e$. Because it compiles from typed #langc to typed #lange, the compiler is defined through type-directed compilation. Although we have three different compiler models, two of them (Shallow and Deep) has the same compilation except for the wrapper. Therefore, we only provide two different compilers. The interesting contract compilation rules are provided in @compiler-rules.

- $compile(type(Gamma,e,tau),e',m:l)$ for local compilation
- $compile(type(Gamma,e,tau),e')$ for non-local compilation

#include "/models/compiler.typ"

== Contracts Hijacking (and Option Contracts)

When using non-local compilers, because the handler are moved outside, users can provide a different handler scope inside the program. This handler can alternate the contract execution policy. This allows us to provide optional contracts, where the handler continue without executing the contract predicate, or executing the contract predicate but ignore the result on purpose.

Consider the following example:

$
f &= mon(k,l,j,flat(e_1) -> flat(e_2), lambda x. x) \
"main" &= apply((lambda f. ("ignore" (apply(f,1))) + (apply(f,2))),f)
$

Where $"ignore"$ is compiled into a wrapper handler that does not check ${effcheck -> Lambda alpha. lambda x. lambda k. apply(k,x)}$. During the execution of $apply(f,1)$, it is executed inside this handler context and all contract checking are ignored. In @christos2013option, the author describe the option contract that attaches to the value, and are explicitly executed. Our model for optional contracts are different, but should share the same semantics. Contracts are executed by default, but can be "turned off". Its model are closer to _Togglable Contracts_. To turn the contract on again, another handler can be injected to execute the checks. Although it brings a way to provide option contracts, this model modifies the environment rather than the contract value, which violates how contracts should work.


== States (and Trace Contracts) <compiler-formal-states>

Local compiler cannot implement contract states, since it is a one-shot handler, the contract cannot reuse anything. However, when we use the outside wrapper of shallow and deep compiler versions, we observe that it can encode states natively. In @effects-example, we demonstrated that states are encoded seemlessly by providing the initial state and the handler form is $lambda x. lambda k. lambda s. e$ where $x,k,s$ are perform value, continuation, and state respectively. Applying the same idea, we extend the handler with two new effects, $effstateget,effstateset$, representing get state and set state respecively.

We demonstrate how state(s) can be encoded effortlessly in shallow compiler version. @shallow-state-handler shows the effect handler adapted to receive and handle a state variable. While executing the condition $apply(p,v)$, it can invoke effect $effstateget,effstateset$ to obtain the current state, or set the current state. Since the state is provided as an extra argument, to obtain the result of the execution the wrapper must be a function that accepts the state(s).

#figure(caption: "Shallow check handler with contract-controlled state")[
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


The current encoding of contract state is limited to a single value. It is easy to expand into multiple state variables. Since the handler always accepts three arguments (type, value, continuation), the rest can be functions. The body of the handler is changed into $lambda s_1. ... lambda s_i. e$ form, where $e$ is the main handler code. And for each state, we provide a pair of effects ($effstateget^i,effstateset^i$) that returns and updates the corresponding $s_i$. Wrapper must be updated to ignore states $s_i$ and return the result only. The wrapper must also provide all initial states to ensure execution.

#figure(caption: "Shallow check handler with contract-controlled multiple states")[
  $
  H &= mu H. handler(h_s, m: s) \
  h_s(effcheck) &= lambda tuple(l,tuple(p,v)). lambda k. lambda s_1. lambda s_2.
    apply(apply(apply(H,(lambda \_. ife(apply(p,v),apply(k,v),eblame(l)))), s_1), s_2) \
  h_s(effstateget^1) &= lambda u. lambda k. lambda s_1. lambda s_2.
    apply(apply(H,lambda \_. apply(k,s_1)),s_1) \
  h_s(effstateset^1) &= lambda s'_1. lambda k. lambda s_1. lambda s_2.
    apply(apply(H,lambda \_. apply(k,s'_1)),s'_1). \
  h_s(effstateget^2) &= lambda u. lambda k. lambda s_1. lambda s_2.
    apply(apply(H,lambda \_. apply(k,s_2)),s_2) \
  h_s(effstateset^2) &= lambda s'_2. lambda k. lambda s_1. lambda s_2.
    apply(apply(H,lambda \_. apply(k,s'_2)),s'_2). \

  kw("wrap")_s &= lambda f. apply(apply(apply(H,(lambda \_. apply((lambda r. lambda s_1. lambda s_2. r),f))),s_1),s_2)
  $
] <shallow-multi-state-handler>

A slightly different encoding is to use tuples $tuple(s_1,tuple(s_2,tuple(s_3,...)))$, which is only available for languages with tuples support. If we have multiple tuple spaces and index-able projection $pi_i$, the handler can be written easier without a series of nested left/right injections.

Users want to use this must define the state in their program. Assume an extension to contract to provide states in @contract-with-states, $kw("cstate")(e_1,lambda x. e_2)$ where $e_1$ is the initial value of the state, and $lambda s. e_2$ is the expression where the state will be bounded into $s$ and appears in $e'_2$. While typing $e_2$, we provide $s : kw("cstate")(tau)$ in the context so that it can only be used under contract. There are only two expressions that can use these contract state variables, $kw("cget"),kw("cset")$. Under the dynamic settings, there is a storage that watches the contract states (similarly to mutable boxes).

#figure(caption: [Extend #langc with contract states])[
#bnf(
  Prod($tau$, {
    Or[$...$][]
    Or[$kw("cstate")(tau)$][]
  }),
  Prod($e$, {
    Or[$...$][]
    Or[$kw("cstate")(e,lambda x. e)$][]
    Or[$kw("cget")(x)$][]
    Or[$kw("cset")(x,e)$][]
  }),
)
] <contract-with-states>

The compiler should for each $kw("cstate")(e_1,lambda s. e_2)$ define a new effect, use $e_1$ as the initial state value and for every occurance of $s$ in $e_2$, modifies $kw("cget"),kw("cset")$ accordingly to effect calling. This compiler is not yet complete, since there are cases where $kw("cstate")$ are enclosed inside a function, so each time that function is run, the state is initialized fresh.

The setup provides a possible compilation for Trace Contracts, introduced in @cameron2023trace. In trace contracts model, the collector (state) is defined as a list and it is being updated automatically. If we rewrite the handler to ${effcheck -> Lambda alpha. lambda x. lambda k. lambda s. apply((lambda \_. e), (apply(perform(effstateset),x)))}$, we obtain a closer ressemblance to trace contracts semantics.

== Connection to Effectful Contracts

Our compiler model shows that basic contract monitors can be compiled into an effect, and maintain the semantics with a crafted handler. Effectful contracts, @cameron2024effectful, explicitly defines contracts for effects, for which we have not defined compilation rules. Inspecting their reduction rules, effects are marked and converted into a sequence of monitors. If we can adapt this reduction to compose a way to convert effect contracts into monitors, our compiler can compile normally. The expected behavior during executing the effect is performing the check effect #effcheck on [effect's] input and [continuation's] output values.
