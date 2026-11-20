#import "/setup.typ": setupdoc
#show: setupdoc

#import "/models/language.typ": *
#import "/utils.typ": load-bib, no-ref

#show: no-ref

== Software Contracts and #langc <chapter-contracts>

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

=== #langc language

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

=== Language Model

We define #langc language extended from #langb with monitors. The surface syntax has only one new expression, $mon(k,l,j,kappa,e)$ where $kappa$ is a contract, $e$ is the protected expression, and $k,l,j$ are labels for blame reporting. There are three main types of contracts, flat $flat(e)$, functional $kappa_1 -> kappa_2$, and dependent $dep(kappa_1,lambda y. kappa_2)$. #langc provides tuple contracts as syntactic sugar applied recursively,

$mon(k,l,j,tuple(kappa_1,kappa_2),e) = apply((lambda v. tuple(mon(k,l,j,kappa_1,injl(v)),mon(k,l,j,kappa_2,injr(v)))),e)$

During evaluation, two new expressions might arise, $check(k,j,e,v)$ and $blame(k,j)$, along with a new value type $guard(v,kappa,k,l,j)$. During evaluation if a contract is violated it reduces into $blame(k,j)$ with two labels $k$ the party responsible (to blamed), and $j$ the contract-providing party. A monitor of a flat contract reduces to a $check(k,j,e,v)$, indicating that a contract checking is happening, with checking code $e$ and value $v$. Checking code evaluates to true or false. If true, check is removed off value, else blame is returned using the labels of check. For other contract types, a monitor turns into a dormant $guard(v,kappa,k,l,j)$, treated as a function value. When it is applied to a value, it breaks down the contract to monitor the argument, and the function's result.

To type #langc, we need a new type $con(tau)$ to type contracts. The type of flat contract depends on the predicate input type, $flat(e) : con(tau)$ where $e : tau -> boolt$. Functional and dependent contracts are typed $con(tau_1 -> tau_2)$ each corresponse to domain contract type, and codomain contract type. A monitor $mon(k,l,j,kappa,v)$ is then typed easily by making sure the contract $kappa$ is typed $con(dot)$ of protected value $v$ type. To ensure type safety is hold, $check(k,j,e,v)$, $guard(v,kappa,k,l,j)$ and $blame(k,j)$ expressions must be typed as well. $blame(k,j)$ accepts any type; $check(k,j,e,v)$ checking code $e$ is typed bool, and the expression type resonates with value $v$; $guard(v,kappa,k,l,j)$ shares the same type with protected value $v$, with contract $kappa$ has contract type of type of $v$ as well.

#include "/models/contracts.typ"
#include "/models/contracts-type-rules.typ"
#include "/models/contracts-reduction-rules.typ"
