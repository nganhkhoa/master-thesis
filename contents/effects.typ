#import "/setup.typ": setupdoc
#show: setupdoc

#import "/models/language.typ": *
#import "/utils.typ": load-bib, no-ref

#import "/proofs/setup.typ": rn

#show: no-ref

#let effdup = $scr("D")$
#let effget = $scr("G")$
#let effset = $scr("S")$

== #lange Language <chapter-effects>

Effect handlers provide programmers a universal way to define side-effects, including exceptions, states, input/output systems. Effects was first defined algebraically by @gordon2003algebraic, few years later, @gordon2013handling defines a universal way to handle algebraic effects. Since then, effect handlers is adapted closer to programming language with languages Frank#footnote(link("https://github.com/frank-lang/frank")) @lukas2020doo and Koka#footnote(link("https://koka-lang.github.io/koka/doc/index.html")) @leijen2017type. The idea behind effects and handlers is simple, an effect is considered as a function with its body provided by a handler in-scope/pre-installed.

Modeling languages with effects is complex. The Frank language relies on Call-By-Push-Value (CBPV) @levy2013call semantics to separate between values, always effect-free, and computations, which may carry effects. In CBPV, a computation $M$ is a _suspended thunk_, which by itself has no effects until it is _forced_ $!M$. Most programmers are not used to this computational model of CBPV, fortunately, the notion of a thunk can be simulated by a function waiting to be applied, $lambda \_. e$, and forced means to apply the function $apply((lambda \_. e),unit)$. With this notion, the Koka language was built under System $F_omega$, ultilizing kind for effects. For the rest of the dissertation, we use the semantics closer to the Koka language.

A program is given definitions of possible effects, for example $"Console"$ denotes read/write capability over the console, or $"Network"$ denotes read/write capability over sockets. The the program can invoke these pre-defined effects. An effect is a set of _operations_, e.g., $"Console"$ effect has operations $"Read","Write"$. Users write invocations to operations, not effects, and the code produces the corresponding effect. Calling an operation is undefined without handler pre-installed. Therefore, users must manually install a handler to the program, or part of code, to interpret the effect. A handler for an effect is a mapping between all operations to its handler functions, $"Read" -> f_"read"; "Write" -> f_"write"$. With a handler in-scope, operations can be defined, and executes accordingly.

Writing programs using effects and effect handlers streamlines the coding process. A module dealing with inputs/outputs can specify an effect $"Process"$ with two operations $"Input","Output"$ and be ignorant to the actual implementation. A different model then defines a handler providing $"Input","Output"$ as file-backed or network-backed or database-backed read/write. Moreover, handlers can encode states, without using mutable boxes.

In the subsequent sections, we give some examples for effect handler usage under the #lange language introduced in @effects-model.

=== Example <effects-example>

In @handler-example-1, we present a simple example: a program wants to compute $(effdup 2) + 1$ is registered with a handler $h$ for effect #effdup, basically _duplicating_ its input. When an effect is perform, the main program pauses the execution, and push everything later into a continuation $k = lambda y. handle(h, (y + 1), m: d)$, at (i). Here, the continuation registers the handler $h$ again, in case the rest of the program uses $effdup$. When the program is a value, the handler removes itself (ii).

#figure(
  stack(
    grid(
      columns: (auto,auto,auto),
      gutter: 1.5em,
      [$h$], [$=$], [${effdup -> lambda v. lambda k. apply(k,(v + v))}$],
    ),
    v(1em),
    grid(
      columns: (2em, auto, 4em),
      align: (left, left, right),
      gutter: 0.5em,

      [],
      [$handle(h, ((apply(perform(effdup, tau: numt), 2)) + 1), m: d)$],
      [],

      [$estep$],
      [$handle(h, apply(perform(effdup, tau: numt), 2), m: d)$],
      [],

      [$estep$],
      [$apply(apply((lambda#underline(rgb("2D8DDD"), $v$). lambda#underline(rgb("#7D8DDD"), $k$).
        apply(k,(v + v))),#underline(rgb("2D8DDD"),2)), #underline(rgb("#7D8DDD"),$(lambda y. handle(h, (y + 1), m: d))$))$],
      [(i)],

      [$estep1$],
      [$apply((lambda y. handle(h, (y + 1), m: d)),(2 + 2))$],
      [],

      [$estep1$],
      [$handle(h, 5, m: d)$],
      [(ii)],

      [$estep$],
      [$5$],
      [],
    ),
    v(1em),
  ),
  caption: [Handler in action]
) <handler-example-1>

Handlers can encode states. This is a nice feature to provide a common state across the code. We illustrate the example in @handler-example-2, where a simple state can be managed by two effects _get_ #effget, and _set_ #effset. As can be seen, the continuation now returns a function expecting a state. During handler execution, this state is applied automatically if the handler is installed with initial state. The continuation resumes the program with the new state, made possible because handler is installed with new state.

Without careful setup, the program might enter the stuck state because the handler removes itself when the execution completes, making the result applies with the state. For example, this program $apply(handle(h,v, m: d) ,s) estep1 apply(v,s)$ stucks if $v$ is not callable. There are many ways to resolve this problem. The first approach requires the program awareness of the state. The programmer explicitly returns a function taking the result and the state but only returns the result.

$
apply(handle(h, (apply((lambda x. lambda s. x),e)), m: d), s) estep1 apply(handle(h, (apply((lambda x. lambda s. x),v)), m: d), s) estep1 apply((lambda s. v), s) estep v
$

The second approach is to use _parameterized handlers_ @leijen2017type, which puts the state into the handler expression. The third approach is to augment the handler with a special effect $ekw("return")$, which modifies the value before removing the handler. The example @handler-example-1 chooses the first approach, as it keeps the handler semantics simple, although a programmer needs to pay more attention when dealing with handlers receiving arguments.

#figure(
  stack(
    grid(
      columns: (auto,auto,auto),
      gutter: 1.5em,
      [$h$], [$=$], [${effget -> lambda v. lambda k. lambda s. apply(apply(k,s),s); effset -> lambda v. lambda k. lambda s. apply(apply(k,s),v)}$],
    ),
    v(1em),
    grid(
      columns: (2em, auto, 4em),
      align: (left, left, right),
      gutter: 0.5em,

      [],
      [$e = ((apply(perform(effset,tau: numt), 42)) + (apply(perform(effget, tau: numt), unit)) + 100)$],
      [],

      [],
      [$apply((handle(h, (apply((lambda x. lambda s. x),e)), m: d)), 0)$],
      [],

      [$estep1$],
      [$apply(apply(apply((lambda#underline(rgb("2D8DDD"), $v$). lambda#underline(rgb("#7D8DDD"), $k$). lambda#underline(rgb("#987112"), $s$).
        apply(apply(k,s),v)), #underline(rgb("2D8DDD"), 42)), #underline(rgb("#7D8DDD"), $lambda y. handle(h, (apply((lambda x. lambda s. x),(y + (apply(perform(effget, tau: numt), unit)) + 100))), m: d)$)), #underline(rgb("#987112"), 0))$],
      [],

      [$estep1$],
      [$apply(apply((lambda y. handle(h, (apply((lambda x. lambda s. x),(y + (apply(perform(effget, tau: numt), unit)) + 100))), m: d)),0), 42)$],
      [],

      [$estep1$],
      [$apply(handle(h, (apply((lambda x.lambda s. x), ((0 + (apply(perform(effget, tau: numt), unit)) + 100)))), m: d), 42)$],
      [],

      [$estep1$],
      [$apply(handle(h, (apply((lambda x.lambda s. x), 142)), m: d), 42)$],
      [],

      [$estep1$],
      [$apply((lambda s. 142), 42)$],
      [],

      [$estep1$],
      [$142$],
      [],
    ),
    v(1em),
  ),
  caption: [Handler with state]
) <handler-example-2>

=== Language Model <effect-model>

We introduce #lange by extending #langb into System $F^epsilon$ by @ningning2020effect. Because System $F^epsilon$ is based on System $F_omega$, the type system is evolved into kinded system, with type constructors and effect kinds. By System $F_omega$, the language is equipped with type abstractions $Lambda alpha. v$ and type applications $e[tau]$. Function types are annotated with effect $epsilon$ showing possible effects during the invocation of function, $teff(tau_1,epsilon,tau_2)$. We also add recursive functions $mu x. v$ to the language as a value, instead of an expression. We give the full syntax extension in @effects-syntax.

Before discussing about handlers, #lange triggers an effect $op$ by invoking $perform(op)$ with an argument, similarly to function application. System $F^epsilon$ only has deep handlers. To deliver a full picture for our translation, we also extend System $F^epsilon$ with shallow handlers. A handler $handler(h, m:m)$ value, has a mode $m in {d,s}$ to annotate deep or shallow. This handler value is typed as a function, and acts as a function waiting for an argument. If $e$ has a $perform(op)$ application, that is $e$ invokes an effect, users write

$apply(handler(h,m:m), (lambda \_ : unit. e))$ to install the handler $h$ when executing $e$.

At runtime, handler expressions turn into a handle expressions $handle(h,e,m:m)$ which are responsible for handling effects invocation during execution of $e$. With handler and handle expressions defined, the next step is to define the concrete handler $h$. A handler is a groupped mapping of operations to functions $op -> f$, for example ${"Get" -> f_1; "Set" -> f_2}$ denotes a handler of two operations $"Get"$ and $"Set"$, with their respective handler functions $f_1,f_2$. Each handler should belong to a single effect, for example the $"Get","Set"$ handler belongs to the $"State"$ effect. The list of effects is given by the users through $Sigma$, a mapping between effect name to handler operation signature set. For $"State"$ effect, $"Get" : tau_"get" in Sigma("State")$ and $"Set" : tau_"set" in Sigma("State")$.

#lange must define the semantics for recursive functions, which was not included in System $F^epsilon$, and handlers. For recursive functions, because $mu x. v$ is a value, it is dormant and reduces on term or type applications. Ignoring types, the rules are as below,

$apply((mu x. v_1),v_2) estepx apply(v_1[x:=mu x. v_1],v_2)$, and

$(mu x. v)[tau] estepx v[x:=mu x. v][tau]$,

Consider this program $handle(h_1, handle(h_2, handle(..., apply(perform(op),v),m:m),m:m),m:m)$, effect perform should be caught by some handler in $h_1,h_2,...$. Assumes that $op : tau in Sigma(l)$. If handler $h = {op -> f; ...}$ implements effect $l$, it should catch it. Rewriting the program into,

$E_1[handle(h,E_2[apply(perform(op),v,)], m:m)]$, where $h$ does not appear in $E_2$.

Then if the handler is shallow, it captures the continuation $E_2$, and applies $f$ with $v$ and continuation $k = lambda x. E_2[x]$,

$E_1[handle(h,E_2[apply(perform(op),v,)], m:s)] estep E_1[apply(apply(f,v),(lambda x. E_2[x]))]$.

If the handler is deep, it captures the continuation $E_2$, and applies $f$ with $v$ and continuation $k = lambda x. handle(h,E_2[x],m:d)$. By re-installing the handler into the continuation, it satisfies the deep handler semantics,

$E_1[handle(h,E_2[apply(perform(op),v,)], m:d)] estep E_1[apply(apply(f,v),(lambda x. handle(h,E_2[x],m:d)))]$.

To find $h$, we provide a metafunction $bop(E)$ that collects possible operations in the context $E$, and validate it with the operation in request.

In typed version, an effect invocation is can be polymorphic. An operation $op$ can be invoked with values of different types. Therefore, the syntax is adjusted to allow type specification on perform and during handler reduction, $apply(apply(perform(op), tau), v)$ and $apply(apply(f[tau],v),k)$. Readers can find the full reduction rules in @effects-reduction-rules.

Before we discuss the typing judgement for #lange, we define how to annotate effect list. A function may invoke multiple effects, for example writing to the console (first effect, $"Console"$) and accessing the internet (second effect, $"Network"$). For that reason, $effs("Console","Network")$ denotes the use of two effects. The syntax can be nested, however they should be considered equivalent to its flatten representation. Moreover, effect's order is not important.

$effs(l_1,l_2,...,l_n) eq.triple effs(l_1,effs(l_2,effs(...,l_n)))$ and $effs(l_1,l_2) eq.triple effs(l_2,l_1)$.

We use $epsilon$ to denote effect lists, and $mteff$ to denote an empty effect list.

Typing judgement for #lange is defined using $type(Gamma,e,tau,eff:epsilon)$, read as "under context $Gamma$, expression $e$ has type $tau$ and might produce effects in $epsilon$". While type is derived, effects is provided as part of context. Typing a program in #lange starts with $mteff$, $type(dot,e,tau,eff:mteff)$. To validate the effects that may occur during the program, the following expressions are augmented with effects, $lambda^epsilon x : tau. e$, $handler(h,m:m,eff:epsilon)$, $handle(h,e,m:m,eff:epsilon)$, and $perform(op,tau:tau,eff:epsilon)$. Effects annotation are mostly kept, except during handle expression, where it can add new effect because a new effect handler is in scope. Handler $h$ has a separated typing judgement, $type(Gamma, m : h, tau, eff:l \| epsilon, type:"ops")$ read as "under context $Gamma$, handler type $m$, the hander $h$ has type $tau$, handles effects $l$ and left out effects $epsilon$". This judgement can rule out effect $l$ that is handled by handler $h$. Another typing judgement is used for values, $type(Gamma,e,tau,type:"val")$, this includes normal values as well as $perform(op,tau:tau,eff:epsilon)$ and $handler(h,m:m)$. Because a value cannot invoke effects, this judgement is defined to separate typing of expressions and values.

Most typing rules are trivial, we select the two typing rules for handlers, #rn("T-E-Ops-Deep") and #rn("T-E-Ops-Shallow"), which require some explanations. A handler

$type(Gamma, m : {op_1 -> f_1, ..., op_n -> f_n},tau, eff: l \| epsilon,type:"ops")$

must first have all the $op_i$ defined in $Sigma(l)$. Type of $op_i : forall alpha. tau_1 -> tau_2$ is a polymorphic function between the effect to be invoked value type $tau_1$ and effect output type $tau_2$. Then handler functions $f_i : forall beta. tau_v -> tau_k -> tau_r$ is also a polymorphic function, as previously shown it receives three arguments, the type $beta$, the value of type $tau_v$, the continuation of type $tau_k$ and returns value of type $tau_r$. Unifying them one by one: first, the operation's signature $tau_1 = tau_v$ because it describes the input type to perform; second, $tau_k = tau_2 -> ?$ because the continuation receives the effect output type; third, $tau_k = tau_2 -> tau_r$ because $f$ must invokes $k$ at the last step therefore, what $k$ returns is what $f$ returns; forth, continuation preserve at least the effects $epsilon$. If the handler is typed for deep handler, the effect of continuation is $tau_k = teff(tau_1,epsilon,tau_r)$ because the handler is re-installed inside the continuation therefore all effects $l$ invocation are resolved. However, when the handler is typed as shallow, the continuation type is $tau_k = teff(tau_1,effs(l, epsilon),tau_r)$ because the continuation (the rest of the program) can execute the effect $l$. Finally, because $f$ runs code, it must align its effect with the environment, $f : tau_v -> teff(tau_k, epsilon, tau_r)$.

#pad(left: 2em)[
  Readers can argue that the signature for shallow handler function $f : tau_v -> teff(tau_k,effs(l,epsilon),tau_r)$ when continuation type $tau_k = teff(tau_1,effs(l,epsilon),tau_r)$. This breaks the Preservation proof. Because expression $handle(h,e,m:s)$ preserves the effect, the expression $e$ must effectively resolve effect of handler $h$. Therefore, the type system limits $f$ to *always* re-install a handler for the effect again. This can be the same handler or a different handler. For example, the handler function that does nothing must be written as:

  $f = Lambda alpha. lambda x. lambda k. handle(h', apply(k,x), m:m)$, where $h'$ a handler for effect $l$.
]

The rest of the typing rules are in @effects-type-rules.

#include "/models/effects.typ"
#include "/models/effects-type-rules.typ"
#include "/models/effects-reduction-rules.typ"
