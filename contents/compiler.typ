#import "/setup.typ": setupdoc
#show: setupdoc

#import "/models/language.typ": *
#import "/proofs/setup.typ": appendix-theorem, appendix-lemma, appendix-number, proof
#import "@preview/great-theorems:0.1.2": great-theorems-init
#import "/utils.typ": load-bib, no-ref

#show: no-ref

#show: great-theorems-init

#let theorem = appendix-theorem
#let lemma = appendix-lemma

= Compiler

Following the compiler of @robert2013icfp, we can compile all contracts recursively by padding a new lambda for functional contracts, unfolding until flat contract. Through observation, instead of compiling flat contracts into $ife(apply(p,v),v,"blame")$, this phrase is pushed into the handler and an effect is performed. Immediately, we can see an easy compilation strategy.

$apply(handler({effcheck^1 -> lambda \_. lambda k. ife(apply(p,v),apply(k,v),"blame")}, m:s), (lambda \_. (apply(perform(effcheck^1), unit))))$

There are two main questions to this approach that when answered, it shows why this is undesired. First, do we need a different effect for each different contract?. Second, where should we put the handler? The first question is relatively yes, if we push the whole if/else clause into the handler. Which we can simplify by using tuples, or similar techniques for encoding the predicate, value, and even blame label into the first argument of handler. Using tuple, we can rewrite into:

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

== Local Compiler


== Shallow Compiler


== Deep Compiler


== States without compromises

Local compiler cannot implement contract states, since it is a one-shot handler, the contract cannot reuse anything. However, when we use the outside wrapper of shallow and deep compiler versions, we observe that it can encode states natively. In @effects-example, we demonstrated that states are encoded seemlessly by providing the initial state and the handler form is $lambda x. lambda k. lambda s. e$ where $x,k,s$ are perform value, continuation, and state respectively. Applying the same idea, we extend the handler with two new effects, $effstateget,effstateset$, representing get state and set state respecively.

=== Shallow State Handler

@shallow-state-handler shows the effect handler adapted to receive and handle a state variable. While executing the condition $apply(p,v)$, it can invoke effect $effstateget,effstateset$ to obtain the current state, or set the current state. However, this state is shared across all contracts. Ideally, we want each set of contracts to have access to a single state, or some states. A simple solution is to introduce hash map into the language and make the state a hash map between an identifier and its [polymorphic] value. Fortunately, it is possible to segment the states without relying on hash map. For each state that is needed, $effstateget^i,effstateset^i$ is created, and the states are provided sequencially. The compiler now must collect and name all possible contract states, then provide correct effects for them.

#figure(caption: "Shallow check handler with contract-controlled state")[
  $
  H &= mu H. handler(h_s, m: s) \
  h_s(effcheck) &= lambda tuple(l,tuple(p,v)). lambda k. lambda s.
    apply(apply(H,(lambda \_. ife(apply(p,v),apply(k,v),eblame(l)))),s) \
  h_s(effstateget) &= lambda u. lambda k. lambda s.
    apply(apply(H,lambda \_. apply(k,s)),s) \
  h_s(effstateset) &= lambda s'. lambda k. lambda s.
    apply(apply(H,lambda \_. apply(k,s')),s').
  $
] <shallow-state-handler>

When wrapping the program with this handler, the end of the execution must be a function that accepts the state(s). Therefore, the wrapper must now be:

$kw("wrap")_s = lambda f. apply(apply(H,(lambda \_. apply((lambda r. lambda s. r),f))),s)$
