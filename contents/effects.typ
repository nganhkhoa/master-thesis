#import "/models/language.typ": *
#import "/utils.typ": load-bib, no-ref

#show: no-ref

#let effdup = $scr("D")$
#let effget = $scr("G")$
#let effset = $scr("S")$

== #lange Language

=== Example

In @handler-example-1, we present a simple example: a program wants to compute $(effdup 2) + 1$ is registered with a handler $h$ for effect #effdup, basically _duplicating_ its input. When an effect is perform, the main program pauses the execution, and push everything later into a continuation $k = lambda y. handle(h, (y + 1))$, at (i). Here, the continuation register the handler $h$ again, in case the rest of the program uses $effdup$. When the program is a value, the handler removes itself (ii).

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
      [$handle(h, ((apply(perform(effdup, numt), 2)) + 1))$],
      [],

      [$estep$],
      [$handle(h, apply(perform(effdup, numt), 2))$],
      [],

      [$estep$],
      [$apply(apply((lambda#underline(rgb("2D8DDD"), $v$). lambda#underline(rgb("#7D8DDD"), $k$).
        apply(k,(v + v))),#underline(rgb("2D8DDD"),2)), #underline(rgb("#7D8DDD"),$(lambda y. handle(h, (y + 1)))$))$],
      [(i)],

      [$estep1$],
      [$apply((lambda y. handle(h, (y + 1))),(2 + 2))$],
      [],

      [$estep1$],
      [$handle(h, 5)$],
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

Without careful setup, the program might enter the stuck state because the handler removes itself when the execution completes, making the result applies with the state. For example, this program $apply(handle(h,v) ,s) estep1 apply(v,s)$ stucks if $v$ is not callable. There are many ways to resolve this problem. The first approach requires the program awareness of the state. The programmer explicitly returns a function taking the result and the state but only returns the result.

$
apply(handle(h, (apply((lambda x. lambda s. x),e))), s) estep1 apply(handle(h, (apply((lambda x. lambda s. x),v))), s) estep1 apply((lambda s. v), s) estep v
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
      [$apply((handle(h, (apply((lambda x. lambda s. x),((apply(perform(effset,numt), 42)) + (apply(perform(effget, numt), unit)) + 100))))), 0)$],
      [],

      [$estep1$],
      [$apply(apply(apply((lambda#underline(rgb("2D8DDD"), $v$). lambda#underline(rgb("#7D8DDD"), $k$). lambda#underline(rgb("#987112"), $s$).
        apply(apply(k,s),v)), #underline(rgb("2D8DDD"), 42)), #underline(rgb("#7D8DDD"), $lambda y. handle(h, (apply((lambda x. lambda s. x),(y + (apply(perform(effget, numt), unit)) + 100))))$)), #underline(rgb("#987112"), 0))$],
      [],

      [$estep1$],
      [$apply(apply((lambda y. handle(h, (apply((lambda x. lambda s. x),(y + (apply(perform(effget, numt), unit)) + 100))))),0), 42)$],
      [],

      [$estep1$],
      [$apply(handle(h, (apply((lambda x.lambda s. x), ((0 + (apply(perform(effget, numt), unit)) + 100))))), 42)$],
      [],

      [$estep1$],
      [$apply(handle(h, (apply((lambda x.lambda s. x), 142))), 42)$],
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

=== Formalism

#lange, inspired by @ningning2020effect, equips #langb with effects and effect handlers. We extend the type system into a kinded type system based on System F, mainly to separate between effect types and normal types. System F also provides polymorphism. The type system adapts its syntax of functions into $teff(tau_1,epsilon,tau_2)$ denotes an effect $epsilon$ (may) occurs during the execution of the function.

Following @ningning2020effect, effects are group of "operations", distinct by its label. An operation $scr("O")$ of effect $epsilon$ is invoked by applying $perform(scr("O"), tau)$ with an argument, and produces an effect $epsilon$. Given an expression $e$ that would perform some effect $epsilon$, a handler $h$ providing all definitions for operations of $epsilon$ must be installed. The calculus provides two ways to install a handler, $handle(h,e)$ and $apply(handler(h),(lambda \_. e))$. The former is the base syntax, during evaluation of $e$, the handler $h$ is used. The other syntax is useful for suspending a computation, and run it only when a handler is applied, providing flexibility such as different handlers.

A handler is a mapping between operation names and their definitions. An operation is a function with the template $Lambda alpha. lambda x : tau_1. lambda k : tau_2. e$. The polymorphic type variable $alpha$ is used to make operations polymorphic. The argument $x$ is the operation argument. The argument $k$ is the _continuation_ or _resumption_, enclosing the rest of the program after the operation invocation. When $k$ is called, the program resumes with the argument provided to $k$.

Because $k$ is a function, a handler can return $k$ and let the program use continuation anyhow the programer wants. This is described in @ningning2020effect as "undesirable in practice" and define a restriction named _scoped resumption_. Our language also follows the same principle and does not allow returning the continuation $k$ (directly or indirectly through closure). However, we do not enforce this and left out for the language implementators.


#v(1em)
#include "/models/effects.typ"
#v(1em)

A function can use multiple effects, and are represented as rows with equivalence up to reordering. An empty effect is represented as $mteff$. Effects can be concatenated by $effs(l,epsilon)$ where effect row $epsilon$ is extended with effect $l$. For ease of writing, we allow writing $effs(l_1,l_2,...,l_n)$ as shorthand instead of $effs(l_1,effs(l_2,...effs(l_n)))$.

The language is explicit about the effects. Lambdas are annotated with effects, as well as perform (operation invocation), and handler installation. These effect annotations are used only during type checking, they do not affect the execution.

Typing for an effect language requires some consideration. Following the works in @ningning2020effect, we define the type judgement relationship $type(Delta,e,tau,eff: epsilon)$ between a type context $Delta$, an expression $e$ and assert it against type $tau$ with some possible effects $epsilon$. Variables and base values do not have effects, they can take any effects. For this reason, we define $type(Delta,v,tau,type: "val")$. Handlers are typed using $type(Delta,h,tau,eff: l | epsilon,type: "ops")$, that it handles a _single_ effect $l$, other effects in $epsilon$ remains unhandled, and all operations returns $tau$. All effects signatures are defined in a global set $Sigma$ for fast accessing the type of the operations. This set can be built by going through all handlers, and its existence is assumed during the start of type checking. All type rules unique to #lange is presented in @effects-type-rules.

#v(1em)
#include "/models/effects-type-rules.typ"
#v(1em)

Lastly the semantic model of #lange is presented in @effects-reduction-rules. A handler can be installed to a function as a shorthand, where it applies the function with a unit argument, which to be ignored. The reduction for handling an effect calling is encoded as _deep handler_. Supporting the shallow should be straightforward by not installing the handler again in the continuation $k$. There is little advantage to support shallow handlers, therefore, only deep handlers are used. While looking for the handler, we make sure we get the innermost handler that can handle the operation.

#v(1em)
#include "/models/effects-reduction-rules.typ"
#v(1em)
