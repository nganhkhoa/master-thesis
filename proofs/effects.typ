#import "/setup.typ": setupdoc
#show: setupdoc

#import "@preview/curryst:0.6.0": rule, prooftree, rule-set
#import "@preview/great-theorems:0.1.2": *

#import "/models/language.typ": *
#import "/utils.typ": *

#set heading(numbering: "A.1")

#show: no-ref
#show: great-theorems-init
#show link: text.with(fill: blue)

#import "/proofs/setup.typ": appendix-theorem, appendix-lemma, derivation, rn
#let theorem = appendix-theorem
#let lemma = appendix-lemma

#let remark = mathblock(
  blocktitle: "Remark",
  prefix: [_Remark._],
  inset: 5pt,
  fill: lime,
  radius: 5pt,
  numbering: "A.1"
)

#let proof = proofblock()



#let lam = [lambda]
#let hdl = [handler]
#let hnd = [handle]
#let prf = [perform]

// Effect annotations are syntax, not inferred decorations.  These helpers
// distinguish the row stored in a term from a row used as a meta-variable.
#let eabs(eps, x, tau, e) = $lambda^eps x : tau . e$
// Build the effect forms through the notation exported by language.typ.  The
// calculus stores the row annotation in the syntax, so handler and handle need
// an outer attachment while perform can use its `eff` parameter directly.
#let ehandler(eps, h, m: d) = $attach(handler(h, m: m), tr: #eps)$
#let ehandle(eps, h, e, m: d) = $attach(handle(h, e, m: m), tr: #eps)$
#let eperform(eps, op, tau) = $perform(op, tau: tau, eff: eps)$

// labels of the handlers in a context, innermost first
#let lbls(E) = $ceil.l #E ceil.r$
// a row extended with a list of labels
#let row(ls, eps) = $chevron.l #ls | #eps chevron.r$
// context typing and handler typing
#let tec(ctx, E, t1, t2, eps) = $#ctx attach(tack.r.short, br: "ec") #E : #t1 -> #t2 | #eps$
#let tops(ctx, h, t, l, eps) = $#ctx attach(tack.r.short, br: "ops") #h : #t | #l | #eps$

= #lange Safety Theorem

Follow the proofs of System $F^epsilon$ in @ningning2020effect, our language extends a new type $blab$, and $eblame(p)$ for migrating labels of #langc to #lange. We also extend with shallow handler which is very similar to deep handler. We also add recursive function $mu$. These are the extra details that we must extend the proofs.

First we redefine some "operations" and rules that change when when adding the above.

- $ceil.l E ceil.r^l$ extracts all labels $l$ from a context in reverse order:

  $ceil.l F_0 dot handle(h_1, dot,m:m) dot F_1 dot ... dot handle(h_n, dot,m:m) dot F_n ceil.r^l eq.delta chevron.l l_n, ..., l_1 chevron.r "iff" h_i : Sigma(l_i)$

  Adapted to include both shallow and deep handle.

// - Well-formedness of types

//   Add #blab as a well-formedness type.

//   #rule-set(
//     prooftree(rule(
//       name: [Kind-Blame-Label],
//       $attach(tack.r.short, br: "wf") blab : k$,
//     )),
//   )

- Evaluation context typing

  Adapted to include both shallow and deep handle.


    #rule-set(
      prooftree(rule(
        name: [CHANDLE],
        $type(Gamma,m : h,sigma, eff:l | epsilon,type:"ops")$,
        $type(Gamma,E,sigma_1 -> sigma, eff:effs(l,epsilon),type:"ec")$,
        $type(Gamma, handle(h, E, eff:epsilon, m:m), sigma_1 -> sigma, eff:epsilon, type: "ec")$,
      )),
    )

== Evaluation Context Typing Lemmas

#lemma(title: "Evaluation Context Typing")[

If $type(Gamma, E, tau_1 -> tau, eff:epsilon,type:"ec")$ and $type(Gamma,e,tau_1,eff:effs(effextr(E),epsilon))$ then $type(Gamma,E[e],tau,eff:epsilon)$
] <lange-evaluation-context-typing>

#proof[

Induction on the evaluation context typing $type(Gamma, E, tau_1 -> tau, eff:epsilon, type:"ec")$.

- Case $E = square.stroked$ trivial

- Case $E = apply(E_0,e_0)$

  #derivation((
    ($type(Gamma, apply(E_0,e_0), tau_1 -> tau, eff:epsilon, type:"ec")$, [Given]),
    ($type(Gamma, E_0, tau_1 -> teff(tau_3, epsilon, tau), eff:epsilon, type:"ec")$, [#rn("CAPP1")]),
    ($type(Gamma, e_0, tau_3, eff:epsilon)$, [#rn("CAPP1")]),
    ($effextr(E) eq.delta effextr(apply(E_0,e_0)) eq.delta effextr(E_0)$, []),
    ($type(Gamma,e,tau_1,eff:effs(effextr(E_0),epsilon))$, [Given]),
    ($type(Gamma, E_0[e], teff(tau_3, epsilon, tau), eff:epsilon)$, [I.H.]),
    ($type(Gamma, apply(E_0[e], e_0), tau, eff:epsilon)$, [#rn("T-E-App")]),
  ))

- Case $E = handle(h, E_0, eff:epsilon,m:m)$

  #derivation((
    ($type(Gamma, handle(h, E_0, eff:epsilon,m:m), tau_1 -> tau, eff:epsilon, type:"ec")$, [Given]),
    ($type(Gamma, m : h, tau, eff:l | epsilon, type:"ops")$, [#rn("CHANDLE")]),
    ($type(Gamma, E_0, tau_1 -> tau, eff:effs(l,epsilon), type:"ec")$, [#rn("CHANDLE")]),
    ($effextr(E) eq.delta effextr(handle(h, E_0, eff:epsilon,m:m)) eq.delta effs(l,effextr(E_0)) = effs(effextr(E_0), l)$, []),
    ($type(Gamma,e,tau_1,eff:effs(effextr(E_0),l,epsilon))$, [Given]),
    ($type(Gamma, E_0[e], tau_1 -> tau, eff:effs(l,epsilon))$, [I.H.]),
    ($type(Gamma, handle(h, E_0[e], eff:epsilon, m:m), tau, eff:epsilon)$, [#rn("T-E-Handle")]),
  ))

- Other cases follow similarly.
]

#lemma(title: "Effect corresponds to the evaluation context")[

If $type(dot,E[e],tau,eff:epsilon)$ then there exists $tau_1$ such that $type(dot,E,tau_1->tau,eff:epsilon,type:"ec")$ and $type(dot,e,tau_1,eff:effs(effextr(E),epsilon))$
] <lange-effect-correspondence>

#proof[

By induction on $E$.

- Case $E = square.stroked$ trivial. $tau_1 = tau$

- Case $E = apply(E_0,e_0)$

  #derivation((
    ($type(dot, (apply(E_0,e_0))[e],tau,eff:epsilon)$, [Given]),
    ($type(dot, apply(E_0[e],e_0),tau,eff:epsilon)$, []),
    ($type(dot, E_0[e],tau_2 -> tau,eff:epsilon)$, [#rn("T-E-App")]),
    ($type(dot, e_0,tau_2,eff:epsilon)$, [#rn("T-E-App")]),
    ($type(dot, E_0,tau_3 -> (tau_2 -> tau),eff:epsilon,type:"ec")$, [I.H.]),
    ($type(dot, e, tau_3, eff:effs(effextr(E_0),epsilon))$, [I.H.]),
    ($effextr(E) eq.delta effextr(apply(E_0,e_0)) eq.delta effextr(E_0)$, []),
    ($type(dot, e, tau_3, eff:effs(effextr(E),epsilon))$, [I.H.]),
    ($type(dot, E,tau_3 -> tau,eff:epsilon,type:"ec")$, [#rn("CAPP1")]),
    ($tau_1 = tau_3$, [Choose]),
  ))

- Case $E = handle(h, E_0, eff:epsilon,m:m)$

  #derivation((
    ($type(dot, handle(h, E_0, eff:epsilon,m:m)[e],tau,eff:epsilon)$, [Given]),
    ($type(dot, handle(h, E_0[e], eff:epsilon,m:m),tau,eff:epsilon)$, []),
    ($type(dot, m : h, tau, eff:l | epsilon, type:"ops")$, [#rn("T-E-Handle")]),
    ($type(dot, E_0[e],tau,eff:effs(l,epsilon))$, [#rn("T-E-Handle")]),
    ($type(dot, E_0,tau_2 -> tau,eff:effs(l,epsilon),type:"ec")$, [I.H.]),
    ($type(dot, e,tau_2,eff:effs(effextr(E_0),l,epsilon))$, [I.H.]),
    ($effextr(E) eq.delta effextr(handle(h, E_0, eff:epsilon,m:m)) eq.delta effs(l,effextr(E_0)) = effs(effextr(E_0), l)$, []),
    ($type(dot, e,tau_2,eff:effs(effextr(E),epsilon))$, [I.H.]),
    ($type(dot, handle(h, E_0,eff:epsilon,m:m),tau_2 -> tau,eff:epsilon,type:"ec")$, [#rn("CHANDLE")]),
    ($tau_1 = tau_2$, [Choose]),
  ))

- Other cases follow similarly.
]

#lemma(title: "Well typed operations are handled")[

If $type(dot,E[apply(perform(op,tau:overline(tau)),v)],tau,eff:mteff)$ then $E$ has the form $E_1 dot handle(h,dot,m:m,eff:epsilon) dot E_2$ with $op in.not bop(E_2)$ and $op -> f in h$.
] <lange-well-typed-handled>

#proof[
  #derivation((
    ($type(dot,E[apply(perform(op,tau:overline(tau)),v)],tau,eff:mteff)$, [Given]),
    ($type(dot,apply(perform(op,tau:overline(tau)),v),tau_1,eff:effextr(E))$, [@lange-effect-correspondence]),
    ($type(dot,perform(op,tau:overline(tau)),teff(tau_2,effextr(E),tau_1),eff:effextr(E))$, [#rn("T-E-App")]),
    ($type(dot,perform(op,tau:overline(tau)),teff(tau_2,effextr(E),tau_1),type:"val")$, [#rn("T-E-Val")]),
    ($l in effextr(E)$, [$effextr(E) = effs(l,epsilon')$]),
    ($E = E_1 dot handle(h,dot,eff:epsilon) dot E_2$, [Definition of $effextr(E)$]),
    ($op -> f in h$, []),
    ($op in.not bop(E_2)$, [Let $handle(h,dot,eff:epsilon)$ be the inner most one]),
  ))
]

#lemma(title: "Effects types are meaningful")[

If $type(dot,E[apply(perform(op,tau:overline(tau)),v)],tau,eff:epsilon)$ with $op in.not bop(E)$, then $op in Sigma(l)$ and $l in epsilon$, i.e. effect types cannot be discarded without a handler.
] <lange-meaningful-effect-type>

#proof[
  #derivation((
    ($type(dot,E[apply(perform(op,tau:overline(tau)),v)],tau,eff:epsilon)$, [Given]),
    ($type(dot,apply(perform(op,tau:overline(tau)),v),tau_1,eff:effs(effextr(E),epsilon))$, [@lange-effect-correspondence]),
    ($type(dot,perform(op,tau:overline(tau)),teff(tau_2,effs(effextr(E),epsilon),tau_1),eff:effs(effextr(E),epsilon))$, [#rn("T-E-App")]),
    ($type(dot,perform(op,tau:overline(tau)),teff(tau_2,effs(effextr(E),epsilon),tau_1),type:"val")$, [#rn("T-E-Val")]),
    ($l in effs(effextr(E),epsilon)$, [$effs(effextr(E),epsilon) = effs(l,epsilon')$]),
    ($op in.not bop(E)$, [Given]),
    ($l in epsilon$, []),
  ))
]

== Type Safety Theorem

#theorem(title: [#lange Progress])[

If $type(dot, e_1, tau, eff: mteff)$ then $e_1$ is a value or $e_1 = eblame(p)$ or $e_1 estep e_2$.
] <lange-effects-progress>

#proof[
  By @lange-progress-with-effect, $e_1$ is a value, or $e_1 = eblame(p)$, or $e_1 estep e_2$, or $e_1 = E[apply(perform(op, tau:overline(tau)), v)]$ with $op in.not bop(E)$ and $op in Sigma(l)$. The last case is impossible:
  #derivation((
    ($type(dot, E[apply(perform(op, tau:overline(tau)), v)], tau, eff: mteff)$, "Given"),
    ($l in mteff$, [@lange-meaningful-effect-type]),
    ("Contradiction", [$mteff$ is empty]),
  ))
]

#lemma(title: [#lange Progress with effects])[

If $type(dot, e_1, tau, eff: epsilon)$ then either
  - $e_1$ is a value or
  - $e_1 = eblame(p)$ or
  - $e_1 estep e_2$ or
  - $e_1 = E[apply(perform(op,tau:overline(tau)),v)]$ where $op : forall overline(alpha). tau_1 -> tau_2 in Sigma(l)$, and $op in.not bop(E)$.
] <lange-progress-with-effect>

#proof[
By induction on $type(dot,e_1,tau,eff:epsilon)$

- Case $e_1 = v$, trivially true
- Case $e_1 = eblame(p)$, trivially true
- Case $e_1 = apply(e_3,e_4)$

  #derivation((
    ($type(dot,apply(e_3,e_4),tau,eff:epsilon)$, [Given]),
    ($type(dot,e_3,teff(tau_1,epsilon,tau),eff:epsilon)$, [Given]),
    ($type(dot,e_4,tau_1,eff:epsilon)$, [Given]),
  ))

  By I.H. on $e_3$:

  - Case $e_3 estep e_5$

    $e_1 = apply(e_3,e_4) estep apply(e_5,e_4) = e_2$

  - Case $e_3 = eblame(p)$

    $e_1 = apply(eblame(p),e_4) estep eblame(p) = e_2$

  - Case $e_3 = E_0[apply(perform(op,tau:overline(tau)),v)]$ where $op : forall overline(alpha). tau_1 -> tau_2 in Sigma(l)$, and $op in.not bop(E)$

    $e_1 = apply(E_0[apply(perform(op,tau:overline(tau)),v)],e_4) = E_1[apply(perform(op,tau:overline(tau)),v)]$.

  - Case $e_3$ is a value

    By I.H. on $e_4$.

    - Cases $e_4 estep e_5$, $e_4 = eblame(p)$ makes $e_1$ steps.

    - Case $e_4$ is a value, by canonical forms of $e_3$, only some cases are valid:

      - Case $e_3 = lambda x. e_6$. Then $e_1 = apply((lambda x. e_6),e_4) estep e_6[x:=e_4] = e_2$
      - Case $e_3 = perform(op, tau:overline(tau))$. Then $e_1 = square.stroked[apply(perform(op, tau:overline(tau)),e_4)]$
      - Case $e_3 = handler(h,eff:epsilon,m:m)$. Then $e_1 = apply(handler(h,eff:epsilon,m:m),e_4) estep handle(h,apply(e_4, ()),eff:epsilon,m:m) = e_2$

- Case $e_1 = apply(e_3, [tau_1])$

  #derivation((
    ($type(dot,apply(e_3,[tau_1]),tau_2[alpha:=tau_1],eff:epsilon)$, [Given]),
    ($type(dot,e_3,forall alpha. tau_2,eff:epsilon)$, []),
  ))

  By I.H. on $e_3$:

  - Case $e_3 estep e_5$

    $e_1 = apply(e_3,[tau_1]) estep apply(e_5,[tau_1]) = e_2$

  - Case $e_3 = eblame(p)$

    $e_1 = apply(eblame(p),[tau_1]) estep eblame(p) = e_2$

  - Case $e_3 = E_0[apply(perform(op,tau:overline(tau)),v)]$ where $op : forall overline(alpha). tau_1 -> tau_2 in Sigma(l)$, and $op in.not bop(E)$

    $e_1 = apply(E_0[apply(perform(op,tau:overline(tau)),v)],[tau_1]) = E_1[apply(perform(op,tau:overline(tau)),v)]$.

  - Case $e_3$ is a value

    By canonical form of value, $e_3 = Lambda alpha. e_4$

    $e_1 = apply((Lambda alpha. e_4), [tau_1]) estep e_4[alpha:=tau_1] = e_2$

- Case $e_1 = handle(h,e_3,eff:epsilon,m:m)$

  #derivation((
    ($type(dot,handle(h,e_3,eff:epsilon,m:m),tau,eff:epsilon)$, [Given]),
    ($type(dot,e_3,tau,eff:effs(l,epsilon))$, [Given]),
  ))

  By I.H. on $e_3$:

  - Case $e_3 estep e_4$

    $e_1 = handle(h,e_3,eff:epsilon,m:m) estep handle(h,e_4,eff:epsilon,m:m) = e_2$

  - Case $e_3 = eblame(p)$

    $e_1 = handle(h,eblame(p),eff:epsilon,m:m) estep eblame(p) = e_2$

  - Case $e_3 = E_0[apply(perform(op,tau:overline(tau)),v)]$ where $op : forall overline(alpha). tau_1 -> tau_2 in Sigma(l)$, and $op in.not bop(E)$

    $e_1 = handle(h,E_0[apply(perform(op,tau:overline(tau)),v)],eff:epsilon,m:m)$.

    - Case $op -> f in h$

      - Case $m=s$ shallow handler

        $e_1 estep apply(apply(apply(f,overline(tau)),v),(lambda x. E_0[x])) = e_2$

      - Case $m=d$ deep handler

        $e_1 estep apply(apply(apply(f,overline(tau)),v),(lambda x. handle(h,E_0[x],eff:epsilon,m:d))) = e_2$

    - Case $op -> f in.not h$

      $e_1 = E_1[apply(perform(op,tau:overline(tau)),v)]$.

  - Case $e_3$ is a value

    $e_1 = handle(h,e_3,eff:epsilon,m:m) estep e_3 = e_2$

- Other cases follow similarly.
]

#theorem(title: [#lange Preservation])[

If $type(dot, e_1, tau, eff: mteff)$ and $e_1 estep e_2$ then $type(dot, e_2, tau, eff: mteff)$.
] <lange-effects-preservation>

#proof[
  By cases on the step.

  - Case $e_1 = E[e_3] estep E[e_4] = e_2$ and $e_3 estepx e_4$.
    #derivation((
      ($type(dot, E[e_3], tau, eff:mteff)$, [Given]),
      ($tec(dot, E, tau_1, tau, mteff)$, [@lange-effect-correspondence]),
      ($type(dot, e_3, tau_1, eff: effs(effextr(E), epsilon))$, [@lange-effect-correspondence]),
      ($type(dot, e_4, tau_1, eff: effs(effextr(E), epsilon))$, [@lange-small-step-preservation]),
      ($type(dot, E[e_4], tau, eff:mteff)$, [@lange-evaluation-context-typing]),
    ))

  - Case Step-E-Error, $E[eblame(p)] estep eblame(p)$.
    #derivation((
      ($type(dot, eblame(p), tau, type: "val")$, rn("T-E-Error")),
      ($type(dot, eblame(p), tau, eff: epsilon)$, rn("T-E-Val")),
    ))
]

#lemma(title: [Redex preservation])[

If $type(dot, e_1, tau, eff: epsilon)$ and $e_1 estepx e_2$ then $type(dot, e_2, tau, eff: epsilon)$.
] <lange-small-step-preservation>

#proof[
  By cases on $e_1 estepx e_2$.

  - Case $apply((lambda^epsilon x : tau_1. e), v) estepx e[x:=v]$.
    #derivation((
      ($type(dot, lambda^epsilon x : tau_1. e, teff(tau_1, epsilon, tau), eff: epsilon)$, rn("T-E-App")),
      // ([The $lambda$ annotation is the body effect $epsilon$.], rn("T-E-Abs")),
      ($type(dot, v, tau_1, eff: epsilon)$, rn("T-E-App")),
      ($type(x : tau_1, e, tau, eff: epsilon)$, [#rn("T-E-Val"), #rn("T-E-Abs")]),
      ($type(dot, v, tau_1, type: "val")$, [#rn("T-E-Val")]),
      ($type(dot, e[x:=v], tau, eff: epsilon)$, [@lange-var-substitution]),
    ))

  - Case $(Lambda alpha^k. v)[tau_0] estepx v[alpha:=tau_0]$
    #derivation((
      ($type(dot, (Lambda alpha^k. v)[tau_0], tau_1[alpha:=tau_0], eff:epsilon)$, [Given]),
      ($type(dot, Lambda alpha^k. v, forall alpha^k. tau_1, eff: epsilon)$, rn("T-E-Tapp")),
      ($attach(tack.r.short, br: "wf") tau_0 : k$, rn("T-E-Tapp")),
      ($type(dot, v, tau_1, type: "val")$, [#rn("T-E-Val"), #rn("T-E-TAbs")]),
      ($type(dot, v[alpha:=tau_0], tau_1[alpha:=tau_0], type: "val")$, [@lange-type-var-substitution]),
      ($type(dot, v[alpha:=tau_0], tau, eff: epsilon)$, rn("T-E-Val")),
    ))

  - Case $apply((mu x : tau_1. v_1),v_2) estepx apply(v_1[x:=mu x : tau_1. v_1],v_2)$, where $tau_1 = teff(tau_2,epsilon,tau)$.

    #derivation((
      ($type(dot, apply((mu x : tau_1. v_1),v_2), tau, eff:epsilon)$, [Given]),
      ($type(dot, mu x : tau_1. v_1, tau_1, eff:epsilon)$, [#rn("T-E-App")]),
      ($type(dot, v_2, tau_2, eff:epsilon)$, [#rn("T-E-App")]),
      ($type(dot, mu x : tau_1. v_1, tau_1, type:"val")$, [#rn("T-E-Val")]),
      ($type(x : tau_1, v_1, tau_1, type:"val")$, [#rn("T-E-Fix")]),
      ($type(dot, v_1[x:=mu x : tau_1 . v_1], tau_1, type:"val")$, [@lange-var-substitution]),
      ($type(dot, v_1[x:=mu x : tau_1 . v_1], tau_1, eff:epsilon)$, rn("T-E-Val")),
      ($type(dot, apply(v_1[x:=mu x : tau_1 . v_1],v_2), tau, eff:epsilon)$, rn("T-E-App")),
    ))

  - Case $(mu x : tau_1. v)[tau_2] estepx (v[x:=mu x : tau_1. v])[tau_2]$, where $tau_1 = forall alpha^k. tau_3$.

    #derivation((
      ($type(dot, (mu x : tau_1. v)[tau_2], tau_3[alpha:=tau_2], eff:epsilon)$, [Given]),
      ($attach(tack.r.short, br: "wf") tau_2 : k$, [#rn("T-E-Tapp")]),
      ($type(dot, mu x : tau_1. v, tau_1, eff:epsilon)$, [#rn("T-E-Tapp")]),
      ($type(dot, mu x : tau_1. v, tau_1, type:"val")$, [#rn("T-E-Val")]),
      ($type(x : tau_1, v, tau_1, type:"val")$, [#rn("T-E-Fix")]),
      ($type(dot, v[x:=mu x : tau_1. v], tau_1, type:"val")$, [@lange-var-substitution]),
      ($type(dot, v[x:=mu x : tau_1. v], tau_1, eff:epsilon)$, rn("T-E-Val")),
      ($type(dot, (v[x:=mu x : tau_1. v])[tau_2], tau_3[alpha:=tau_2], eff:epsilon)$, rn("T-E-Tapp")),
    ))

  - Case $apply(handler(h,eff:epsilon,m:m),v) estepx handle(h, apply(v, unit), eff:epsilon,m:m)$.
    #derivation((
      ($type(dot, apply(handler(h,eff:epsilon,m:m),v), tau, eff:epsilon)$, [Given]),
      ($type(dot, handler(h,eff:epsilon,m:m), teff(tau_1, epsilon, tau), eff: epsilon)$, rn("T-E-App")),
      ($type(dot, v, tau_1, eff: epsilon)$, rn("T-E-App")),
      ($type(dot, handler(h,eff:epsilon,m:m), teff(tau_1, epsilon, tau), type: "val")$, rn("T-E-Val")),
      ($tops(dot, h, tau, l, epsilon)$, rn("T-E-Handler")),
      ($tau_1 = teff(unit, row(l, epsilon), tau)$, rn("T-E-Handler")),
      ($type(dot, v, teff(unit, row(l, epsilon), tau), eff: row(l, epsilon))$, [@lange-values-any-effect]),
      ($type(dot, apply(v, unit), tau, eff: row(l, epsilon))$, [#rn("T-Unit"), #rn("T-E-App")]),
      ($type(dot, handle(h, apply(v, unit),eff:epsilon,m:m), tau, eff: epsilon)$, rn("T-E-Handle")),
    ))

  - Case $handle(h, v, eff:epsilon,m:m) estepx v$.
    #derivation((
      ($type(dot, v, tau, eff: row(l, epsilon))$, rn("T-E-Handle")),
      ($type(dot, v, tau, type: "val")$, rn("T-E-Val")),
      ($type(dot, v, tau, eff: epsilon)$, [@lange-values-any-effect]),
    ))

  - Case $handle(h, E[apply(perform(op, tau:tau_0), v)], eff:epsilon,m:d) estepx apply(apply(f[tau_0], v), k)$, where $op in.not bop(E)$, $(op -> f) in h$, $op : forall alpha. tau_1 -> tau_2 in Sigma(l)$ and $k = lambda^epsilon x : tau_2[alpha:=tau_0]. handle(h, E[x], eff:epsilon, m:d)$.
    #derivation((
      ($type(dot,handle(h, E[apply(perform(op, tau:tau_0), v)], eff:epsilon,m:d),tau,eff:epsilon)$, [Given]),
      ($tops(dot, h, tau, l, epsilon)$, rn("T-E-Handle")),
      ($type(dot, f, forall alpha. teff(tau_1, epsilon, (teff((teff(tau_2, epsilon, tau)), epsilon, tau))), eff:epsilon)$, rn("T-E-Ops")),
      ($type(dot, f, forall alpha. teff(tau_1, epsilon, (teff((teff(tau_2, epsilon, tau)), epsilon, tau))), type: "val")$, rn("T-E-Val")),
      ($type(dot, f[tau_0], teff(tau_1[alpha:=tau_0], epsilon, (teff((teff(tau_2[alpha:=tau_0], epsilon, tau)), epsilon, tau))), eff: epsilon)$, [#rn("T-E-Val"), #rn("T-E-Tapp")]),
      ($type(dot, apply(perform(op, tau:tau_0), v), tau_2[alpha:=tau_0], eff: effs(effextr(handle(h,E,eff:epsilon,m:d)),epsilon))$, [@lange-effect-correspondence]),
      ($tec(dot, handle(h, E,eff:epsilon,m:d), tau_2[alpha:=tau_0], tau, epsilon)$, [@lange-effect-correspondence]),
      ($type(dot, v, tau_1[alpha:=tau_0], eff: epsilon)$, [#rn("T-E-App"), @lange-values-any-effect]),
      ($type(dot, apply(f[tau_0],v), teff((teff(tau_2[alpha:=tau_0], epsilon, tau)), epsilon, tau), eff: epsilon)$, [#rn("T-E-Val"), #rn("T-E-Tapp")]),
      ($$, [build up $k$ $arrow.b$]),
      ($type(x : tau_2[alpha:=tau_0], x, tau_2[alpha:=tau_0], type:"val")$, [#rn("T-E-Var")]),
      ($type(x : tau_2[alpha:=tau_0], x, tau_2[alpha:=tau_0], eff: epsilon)$, [#rn("T-E-Val")]),
      ($tec(x : tau_2[alpha:=tau_0], handle(h, E,eff:epsilon,m:d), tau_2[alpha:=tau_0], tau, epsilon)$, [weakening]),

      ($type(x : tau_2[alpha:=tau_0], handle(h, E[x], eff:epsilon,m:d), tau, eff: epsilon)$, [@lange-evaluation-context-typing]),
      ($type(dot, lambda^epsilon x : tau_2[alpha:=tau_0]. handle(h, E[x], eff:epsilon,m:d), teff(tau_2[alpha:=tau_0],epsilon,tau), type:"val")$, [#rn("T-E-Abs")]),
      ($type(dot, lambda^epsilon x : tau_2[alpha:=tau_0]. handle(h, E[x], eff:epsilon,m:d), teff(tau_2[alpha:=tau_0],epsilon,tau), eff:epsilon)$, [#rn("T-E-Val")]),
      ($type(dot, k, teff(tau_2[alpha:=tau_0], epsilon, tau), eff: epsilon)$, [#rn("T-E-Abs"), #rn("T-E-Val")]),
      ($type(dot, apply(apply(f[tau_0], v), k), tau, eff: epsilon)$, rn("T-E-App")),
    ))

  - Case $handle(h, E[apply(perform(op, tau:tau_0), v)], eff:epsilon,m:s) estepx apply(apply(f[tau_0], v), k)$, where $op in.not bop(E)$, $(op -> f) in h$, $op : forall alpha. tau_1 -> tau_2 in Sigma(l)$ and $k = lambda^effs(l,epsilon) x : tau_2[alpha:=tau_0]. E[x]$, with $x$ fresh.
    #derivation((
      ($type(dot,handle(h, E[apply(perform(op, tau:tau_0), v)], eff:epsilon,m:s),tau,eff:epsilon)$, [Given]),
      ($type(dot, s : h, tau, type:"ops", eff:l | epsilon)$, rn("T-E-Handle")),
      ($type(dot, E[apply(perform(op, tau:tau_0), v)], tau, eff:effs(l,epsilon))$, rn("T-E-Handle")),
      ($type(dot, f, forall alpha. teff(tau_1, epsilon, teff((teff(tau_2, effs(l,epsilon), tau)), epsilon, tau)), type:"val")$, rn("T-E-Ops-Shallow")),
      ($type(dot, f[tau_0], teff(tau_1[alpha:=tau_0], epsilon, teff((teff(tau_2[alpha:=tau_0], effs(l,epsilon), tau)), epsilon, tau)), eff:epsilon)$, [#rn("T-E-Val"), #rn("T-E-Tapp")]),
      ($type(dot, apply(perform(op, tau:tau_0), v), tau_2[alpha:=tau_0], eff:effs(effextr(E),effs(l,epsilon)))$, [@lange-effect-correspondence]),
      ($tec(dot, E, tau_2[alpha:=tau_0], tau, effs(l,epsilon))$, [@lange-effect-correspondence]),
      ($type(dot, v, tau_1[alpha:=tau_0], eff:epsilon)$, [#rn("T-E-App"), @lange-values-any-effect]),
      ($type(dot, apply(f[tau_0],v), teff((teff(tau_2[alpha:=tau_0], effs(l,epsilon), tau)), epsilon, tau), eff:epsilon)$, rn("T-E-App")),
      ($type(x : tau_2[alpha:=tau_0], x, tau_2[alpha:=tau_0], type:"val")$, rn("T-E-Var")),
      ($type(x : tau_2[alpha:=tau_0], x, tau_2[alpha:=tau_0], eff:effs(effextr(E),effs(l,epsilon)))$, rn("T-E-Val")),
      ($tec(x : tau_2[alpha:=tau_0], E, tau_2[alpha:=tau_0], tau, effs(l,epsilon))$, [Weakening]),
      ($type(x : tau_2[alpha:=tau_0], E[x], tau, eff:effs(l,epsilon))$, [@lange-evaluation-context-typing]),
      ($type(dot, k, teff(tau_2[alpha:=tau_0], effs(l,epsilon), tau), type:"val")$, rn("T-E-Abs")),
      ($type(dot, k, teff(tau_2[alpha:=tau_0], effs(l,epsilon), tau), eff:epsilon)$, rn("T-E-Val")),
      ($type(dot, apply(apply(f[tau_0], v), k), tau, eff:epsilon)$, rn("T-E-App")),
    ))

  - Other cases follows similarly to the above and @langb-redex-preservation, with every judgment under effect $epsilon$.
]


#lemma(title: "Variable Substitution")[

If $type(Gamma_1\,x:tau_1\,Gamma_2, e, tau, eff:epsilon)$ and $type(Gamma_1\,Gamma_2,v,tau_1,type:"val")$ then $type(Gamma_1\,Gamma_2, e[x:=v], tau, eff:epsilon)$
] <lange-var-substitution>

#proof[
]

#lemma(title: "Type Variable Substitution")[

If $type(Gamma,e,tau,eff:epsilon)$ and $attach(tack.r.short, br: "wf") tau_1 : k$ then $type(Gamma[alpha^k := tau_1], e[alpha^k := tau_1], tau[alpha^k := tau_1], eff:epsilon)$
] <lange-type-var-substitution>

#proof[
]

#lemma(title: "Values take any effect")[

If $type(Gamma,v,tau,type:"val")$ then $type(Gamma,v,tau,eff:epsilon)$
] <lange-values-any-effect>
