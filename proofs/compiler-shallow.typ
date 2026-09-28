#import "/proofs/setup.typ": *
#import "/utils.typ": *
#import "/models/language.typ": *

#show: no-ref
#show: great-theorems-init

#let C(e) = $"C"(#e)$
#let V(e) = $"V"(#e)$
#let T(s) = $"T"(#s)$
#let M(e, s) = $chevron.l #e; #s chevron.r$
#let H = $"H"$
#let nil = $epsilon$

= Correctness of the shallow-handler compiler

We prove forward simulation for the pure fragment with flat and nondependent
function contracts. The base constructs are constants, variables, abstraction,
application, recursion, conditionals, pairs, projections, and the pure primitive
operations. Contracts have grammar $kappa ::= flat(p) | kappa -> kappa$,
where $p$ is a lambda abstraction of predicate type (its body may be open
before substitution). This syntactic value restriction is preserved by both
value substitution and recursive unfolding. Predicate bodies may contain arbitrary terms of this fragment,
including further monitors. Runtime terms additionally contain checks, guards,
and blame. We use left-to-right call-by-value evaluation and capture-avoiding
substitution, identifying terms up to renaming of bound variables.

This restriction on predicates is necessary for the Compile-Flat rule in
`models/compiler.typ`: its argument $tuple(k,tuple(C(p),C(e)))$ evaluates
$p$ before $e$, whereas the source first evaluates $e$. For example, let
$p = (lambda z. lambda x. trueb) blame(a,j)$ and let $e = blame(b,j)$,
with $a != b$. A flat monitor of $e$ reports $b$ in the source and $a$ in
the compiled program. Both expressions can be assigned the required types.
Thus the unrestricted theorem for that rule is false. Value predicates avoid
this discrepancy. Dependent, reference, and pair contracts, and mutable state,
are outside the theorem below; ordinary pairs remain in the base fragment.

== Target semantics and compilation

All target terms in the proof are untyped. Unlike the deep rule in
`models/effects-reduction-rules.typ`, the shallow operation rule captures
$lambda x. D[x]$, without reinstalling the handler. Here $D$ is a target
evaluation context containing no handler for $effcheck$:

$ handle(h,D[apply(perform(effcheck),a)])
  estep apply(apply(h(effcheck),a),(lambda x. D[x])). $

Handler application to a thunk and handler return have the usual rules:
$apply(handler(h),f) estep handle(h,apply(f,()))$ and
$handle(h,w) estep w$. Target errors escape every evaluation context,
including handlers. Labels are values. Define the recursive handler value
$H$ by the following unfolding equation; recursion can equivalently be
implemented by the $mu$-bound handler wrapper:

$ H = handler({effcheck -> lambda tuple(l,tuple(p,v)). lambda q.
  apply(H,(lambda u. ife(apply(p,v),apply(q,v),eblame(l))))) }). $

The variables $u$ and all continuation parameters are fresh. Write
$handle(H,t)$ for handling $t$ with the clauses of $H$, and put
$"Run"(e) = apply(H,(lambda u. C(e)))$.
The essential derived reduction is

$ handle(H,D[apply(perform(effcheck),tuple(k,tuple(p,w)))])
  estep1 handle(H,ife(apply(p,w),apply((lambda x. D[x]),w),eblame(k))). $

It follows by shallow capture, the two clause applications, recursive handler
unfolding, thunk application, and handler installation. In particular the
reinstalled handler surrounds both the predicate and the resumed continuation.

Compilation $C$ is homomorphic on base syntax, erasing type annotations, and
$V$ is its restriction to source values, extended to runtime guards below.
Define the function wrapper

$ "W"(k,l,j,kappa_1,kappa_2) = lambda f. lambda x.
  C(mon(k,l,j,kappa_2,apply(f,mon(l,k,j,kappa_1,x)))). $

Then

$ C(mon(k,l,j,flat(p),e)) =
  apply(perform(effcheck),tuple(k,tuple(V(p),C(e)))), $
$ C(mon(k,l,j,kappa_1 -> kappa_2,e)) =
  apply(("W"(k,l,j,kappa_1,kappa_2)),C(e)), $
$ V(guard(v,kappa_1 -> kappa_2,k,l,j)) = lambda x.
  C(mon(k,l,j,kappa_2,apply(v,mon(l,k,j,kappa_1,x)))), $
$ C(blame(k,j)) = eblame(k). $

For ordinary values, $V(b)=b$, $V(n)=n$, $V(())=()$, $V(x)=x$,
$V(tuple(v_1,v_2))=tuple(V(v_1),V(v_2))$, and
$V(lambda x. e)=lambda x. C(e)$.
These clauses recursively compile contracts of smaller structure when defining
$"W"$. They are exactly the erased Compile-Flat and Compile-Func rules,
together with the homomorphic base rules. The guard clause defines a runtime
relation, not an additional source compilation rule. The target preserves the
blamed party $k$; the source's second label $j$ is not observable in this target.

== Evaluation stacks and the simulation relation

A stack lists frames from innermost to outermost. An ordinary frame $F$ is
one immediate call-by-value evaluation frame, excluding a check frame. Its
translation $F^C$ is homomorphic on base frames, with

$ (mon(k,l,j,flat(p),square.stroked))^C =
  apply(perform(effcheck),tuple(k,tuple(V(p),square.stroked))), $
$ (mon(k,l,j,kappa_1 -> kappa_2,square.stroked))^C =
  apply(("W"(k,l,j,kappa_1,kappa_2)),square.stroked). $

These are target evaluation contexts: $V(p)$ and $"W"$ are values.
A check frame is $"Q"(k,j,v)=check(k,j,square.stroked,v)$.
Define a target evaluation context for every stack:

$ T(nil)[t] = t, $
$ T(F :: S)[t] = T(S)[F^C[t]], $
$ T("Q"(k,j,v) :: S)[t] =
  ife(t,apply((lambda x. T(S)[x]),V(v)),eblame(k)). $

Thus a check saves the entire remaining computation in its success branch.
This definition handles any number of nested checks without assuming that
translation commutes with plugging a check into an ordinary context. None
of these contexts contains a handler for $effcheck$.

We use the standard source evaluation machine $M(e,S)$. It decomposes a
base expression into its next operand and an ordinary frame, returns values
through those frames in evaluation order, and contracts a base redex once its
operands are values. Its additional transitions are:

$ M(mon(k,l,j,kappa,e),S) -> M(e,mon(k,l,j,kappa,square.stroked) :: S), $
$ M(v,mon(k,l,j,flat(p),square.stroked) :: S)
  -> M(apply(p,v),"Q"(k,j,v) :: S), $
$ M(v,mon(k,l,j,kappa_1 -> kappa_2,square.stroked) :: S)
  -> M(guard(v,kappa_1 -> kappa_2,k,l,j),S), $
$ M(trueb,"Q"(k,j,v) :: S) -> M(v,S), $
$ M(falseb,"Q"(k,j,v) :: S) -> M(blame(k,j),S). $

Applying a guarded function contracts Guard-Func from the source semantics.
Blame discards the stack. If a runtime check is written explicitly, its
administrative decomposition is
$M(check(k,j,e,v),S) -> M(e,"Q"(k,j,v) :: S)$.
It is enough to consider machines starting from source programs without
runtime checks or guards: checks introduced by reduction are immediately
represented by check frames, and guards by the value clause above.

For a focused term without a runtime check constructor, put

$ "A"(e,S) = handle(H,T(S)[C(e)]). $

For blame we instead use the canonical clause
$"A"(blame(k,j),S) = handle(H,eblame(k))$ for every $S$:
source blame discards its pending computation, and target errors can
propagate through $T(S)$ before leaving the outer handler.

The simulation relation pairs the source configuration $M(e,S)$ with
$"A"(e,S)$. In particular $C(v)=V(v)$ for every runtime value. Explicit
checks are represented by their decomposed configurations. This is a
relation between configurations, not an equivalence relation between the
two languages.

#lemma(title: "Substitution and evaluation contexts")[
  For a source term $e$ and value $v$ in this fragment,
  $C(e[x:=v]) = C(e)[x:=V(v)]$.
  The corresponding equality holds for values, contracts, and ordinary
  frames. For every stack $S$, $T(S)$ is a target evaluation context.
]

#proof[
  Prove the substitution equalities simultaneously by structural induction.
  Constants and variables are immediate. Every base constructor follows
  by applying the induction hypothesis to its constituents, renaming bound
  variables first. The flat clause follows from the hypotheses for its
  predicate value and monitored expression. In the function clause, choose
  $f$ and the wrapper parameter fresh; apply the hypotheses to the two
  smaller contracts and to the monitored expression. The guard clause uses
  the same argument with the hypothesis for the guarded value. Labels do
  not change under term substitution. This exhausts the constructors.

  For the context property, induct on the stack. The empty stack is the
  hole. An ordinary frame composes two evaluation contexts; the flat frame
  is valid because its predicate has already translated to a value. A check
  frame puts the hole in the condition of an if-expression. Its success
  branch is suspended, so it need not be a value. Fresh continuation
  parameters prevent capture in all three clauses.
]

#lemma(title: "Source refocusing")[
  If a closed source program $e$ reduces to a result $r$, where $r$ is a
  value or blame, the machine starting at $M(e,nil)$ reaches $M(r,nil)$
  in finitely many transitions.
]

#proof[
  Plugging a focused term into its stack reconstructs the source term.
  The unique left-to-right evaluation position determines the next frame.
  Pushing frames and returning an operand value to seek the next operand
  leave the reconstructed term unchanged. Each such traversal to the next
  redex is finite, since it traverses a finite term and stack. Contracting
  that redex is precisely one source reduction: the two monitor rules,
  the two check rules, guarded application, or a base reduction. Introducing
  a check and pushing its frame reconstructs the source's Check term.
  Blame discards all frames, matching contextual blame propagation (or
  leaves terminal blame unchanged when the stack is empty). Induct on
  the given finite source reduction sequence, inserting these finite
  traversals between contractions. Finally return the result through
  any remaining administrative frames. This gives the claimed machine run.
]

#lemma(title: "Shallow simulation")[
  For every reachable machine transition
  $M(e,S) -> M(e',S')$, there is a finite target reduction
  $"A"(e,S) estep1 "A"(e',S')$.
]

#proof[
  Case analysis on the machine transition:

  - *Administrative base transitions and monitor decomposition.*
    The two translations are identical by the ordinary-frame clause of
    $T$. This includes moving from a completed operand to the next operand
    and reconstructing a pair value. Use zero target steps.

  - *Base contraction.* Beta reduction is simulated by one target beta
    step and the substitution lemma. Recursion unfolds on both sides;
    the structural substitution proof also applies to substitution of the
    recursive term (predicate positions remain values in this fragment).
    Conditionals select the same branch, projections select the same pair
    component, and pure primitives compute the same constant. Each step
    occurs inside the evaluation context $handle(H,T(S))$.

  - *Flat monitor.* Let $D=T(S)$ and $w=V(v)$. The initial target is
    $handle(H,D[apply(perform(effcheck),tuple(k,tuple(V(p),w)))])$.
    By the derived shallow-capture reduction it reduces to
    $handle(H,ife(apply(V(p),w),apply((lambda x. D[x]),w),eblame(k)))$.
    This is exactly $"A"(apply(p,v),"Q"(k,j,v) :: S)$.
    Capture includes every pending check in $S$. The installed handler
    therefore also handles checks raised while evaluating $apply(p,v)$.

  - *Function monitor.* In $T(S)$, apply $"W"$ to $V(v)$.
    One beta step and substitution yield
    $V(guard(v,kappa_1 -> kappa_2,k,l,j))$, as required.

  - *Guarded application.* Applying the translated guard to $V(w)$ takes
    one beta step to
    $C(mon(k,l,j,kappa_2,apply(v,mon(l,k,j,kappa_1,w))))$.
    This is the translation of Guard-Func's reduct by substitution. The
    reversed domain labels and unchanged range labels match exactly.

  - *Successful check.* The target is
    $handle(H,ife(trueb,apply((lambda x. T(S)[x]),V(v)),eblame(k)))$.
    Selecting the true branch and beta-reducing gives
    $handle(H,T(S)[V(v)]) = "A"(v,S)$.

  - *Failed check.* Selecting the false branch gives
    $handle(H,eblame(k))$.
    The continuation containing $S$ has been discarded. By the canonical
    blame clause this is $"A"(blame(k,j),S)$, as required.

  - *Blame produced by a base contraction or an operand.* If a selected
    branch or substituted body is blame, its target error propagates through
    $T(S)$ to reach the canonical blame translation. Stop before propagating
    through the outer handler. Discarding a source blame stack then requires
    zero target steps.

  These cases cover all machine transitions. The canonical blame extension
  also makes administrative decomposition with a blamed operand valid:
  after the syntactic decomposition, propagate its error through the
  remaining evaluation context. No step reinstalls a discarded continuation.
]

#theorem(title: "Preservation of terminating results")[
  Let $e$ be a closed, well-typed program in the fragment above. If
  $e cstep1 r$, then
  $"Run"(e) estep1 "Result"(r)$, where
  $"Result"(v)=V(v)$ and $"Result"(blame(k,j))=eblame(k)$.
  In particular the compiler preserves terminating base values and the
  blamed party.
]

#proof[
  Unfold the wrapper and apply its thunk to obtain
  $"Run"(e) estep1 "A"(e,nil)$.
  Source refocusing supplies a finite machine run to $M(r,nil)$.
  Induction on its length, applying shallow simulation at each transition
  and concatenating the finite target reductions, gives
  $"A"(e,nil) estep1 "A"(r,nil)$.
  If $r=v$, handler return yields $V(v)$. If $r=blame(k,j)$,
  target error propagation through the handler yields $eblame(k)$.
]

The theorem is a forward simulation of the erased shallow compiler. It does
not assert reflection of termination or correctness of type erasure for the
polymorphic target. A typed version additionally needs a well-typed shallow
wrapper and an erasure lemma for that target's operational semantics; neither
follows merely from the untyped simulation.
