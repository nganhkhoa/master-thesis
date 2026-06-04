#import "/models/language.typ": *
#import "/utils.typ": load-bib, no-ref

#show: no-ref

== #lange Language

=== Example

#let effdup = $scr("D")$
#let effget = $scr("G")$
#let effset = $scr("S")$

Effect handler is a new construct similar to how try/catch was designed. In fact, the idea is similar to resumable exception. An effect is invoked (throw), and a handler (try) for the effect installed prior catches. A continuation is pushed into the catch context, and can be invoked to continue the execution, or abort. Yapping...

In @handler-example-1, we lay out a simple example. A program wants to compute $(effdup 2) + 1$ is registered with a handler $h$ for effect #effdup, basically _duplicating_ its input. When an effect is perform, the main program pauses the execution, and push everything later into a continuation $k = lambda y. handle(h, (y + 1))$, at (i). Here, the continuation register the handler $h$ again, in case the rest of the program uses $effdup$. When the program is a value, the handler removes itself (ii).

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

We continue to extend the #langb language with effects and effect handlers in @effects-syntax. This is done by typing the effects separately from the base types. This practice has been introduced to formalize the Koka#footnote(link("https://koka-lang.github.io/")) language. The approach we take here resembles the System $F^epsilon$ language introduced in @ningning2020effect. We added polymorphism through type application, and kinds to #langb language. Two special kinds are added to represent effects (#eff) and effect labels (#lab). A label $l in #lab$ is a group of operations. And an effect $epsilon in #eff$ is composed by chaining #lab together with other effects. An empty effect $mteff$ defines no labels, therefore no effects can be performed. In otherwords, #eff defines the set of effects that can be performed. A function can now produce some effects $epsilon in #eff$, and is represented in its type $teff(tau_1,epsilon,tau_2)$. Original type for function $tau_1->tau_2$ is understood as pure, without effects, $teff(tau_1,mteff,tau_2)$.


The language is then extended with handlers, handler installation ($handle(h,e)$), and calling/performing an effect ($perform(op, tau)$). Handlers are a set of operations distinguishable by the operation's name. A handler denotes a single effect usually by its label $l in #lab$. Performing an effect is analogous function application, therefore $perform(op,tau)$ is treated as a value, where application for it has a distinct reduction rule. The evaluation context is thus extended to support handler installation.

#v(1em)
#include "/models/effects.typ"
#v(1em)

Typing for an effect language requires some consideration. Following the works in @ningning2020effect, we define the type judgement relationship $type(Delta,e,tau,eff: epsilon)$ between a type context $Delta$, an expression $e$ and assert it against type $tau$ with some possible effects $epsilon$. Variables and base values do not have effects, they can take any effects. For this reason, we define $type(Delta,v,tau,eff:[],type: "val")$. Handlers are typed using $type(Delta,h,tau,eff: l | epsilon,type: "ops")$, that it handles a _single_ effect $l$, other effects in $epsilon$ remains unhandled, and all operations returns $tau$. All type rules unique to #lange is presented in @effects-type-rules.

#v(1em)
#include "/models/effects-type-rules.typ"
#v(1em)

Lastly the semantic model of #lange is presented in @effects-reduction-rules. A handler can be installed to a function as a shorthand, where it applies the function with a unit argument, which to be ignored. The reduction for handling an effect calling is encoded as _deep handler_. Supporting the shallow should be straightforward by not installing the handler again in the continuation $k$. There is little advantage to support shallow handlers, therefore, only deep handlers are used. While looking for the handler, we make sure we get the innermost handler that can handle the operation.

#v(1em)
#include "/models/effects-reduction-rules.typ"
#v(1em)
