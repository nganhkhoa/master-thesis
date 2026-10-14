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

#import "/proofs/setup.typ": appendix-theorem, appendix-lemma
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


// Proof derivations use the same full-width two-column layout as
// compiler-typesoundness.typ.
#let mp(rows) = block(width: 100%, grid(
  columns: (1fr, auto),
  column-gutter: 2em,
  row-gutter: 0.8em,
  align: (left, right),
  ..rows.map(((judgment, reason)) => (judgment, reason)).flatten(),
))

#let lam = [lambda]
#let hdl = [handler]
#let hnd = [handle]
#let prf = [perform]

// Effect annotations are syntax, not inferred decorations.  These helpers
// distinguish the row stored in a term from a row used as a meta-variable.
#let eabs(eps, x, tau, e) = $#kw("lambda")^eps x : tau . e$
// Build the effect forms through the notation exported by language.typ.  The
// calculus stores the row annotation in the syntax, so handler and handle need
// an outer attachment while perform can use its `eff` parameter directly.
#let ehandler(eps, h) = $attach(handler(h), tr: #eps)$
#let ehandle(eps, h, e) = $attach(handle(h, e), tr: #eps)$
#let eperform(eps, op, tau) = $perform(op, tau: tau, eff: eps)$

// labels of the handlers in a context, innermost first
#let lbls(E) = $ceil.l #E ceil.r$
// a row extended with a list of labels
#let row(ls, eps) = $chevron.l #ls | #eps chevron.r$
// context typing and handler typing
#let tec(ctx, E, t1, t2, eps) = $#ctx attach(tack.r.short, br: "ec") #E : #t1 -> #t2 | #eps$
#let tops(ctx, h, t, l, eps) = $#ctx attach(tack.r.short, br: "ops") #h : #t | #l | #eps$

The proofs for #lange follow the proofs of System $F^epsilon$ in Effect Handlers, Evidently @ningning2020effect. #lange is $F^epsilon$ with the expressions of #langb, errors, and fixpoints. Its type rules are those of $F^epsilon$, with the evidence translation left out. This part has four sections: evaluation contexts, substitution, progress, and preservation.

== Conventions

*Typing.* There is no type variable context. As in $F^epsilon$, type variables are kept apart by the side conditions $alpha in.not "ftv"(Gamma)$ of T-E-Perform and $alpha in.not "ftv"(epsilon, tau)$ of T-E-Ops, and every type is assumed well-formed. The rules of #langb are lifted to #lange by giving every premise and the conclusion the same effect row $epsilon$. The value forms $n$, $b$, $unit$ and $x$ are typed by value rules (T-Num, T-Bool, T-Unit, T-E-Var). The effect row is also recorded in effect-bearing syntax: $#kw("lambda")^epsilon x : tau. e$ records the latent effect of its body, $eperform(epsilon, op, tau_s)$ records the tail of its operation row, and $ehandler(epsilon, h)$ and $ehandle(epsilon, h, e)$ record the handler residual row. Thus $ehandle(epsilon, h, e)$ checks $e$ at $row(l, epsilon)$ and produces effect $epsilon$. A tuple of values also has a value rule, T-E-VTuple: from $type(Gamma, v_1, tau_1, type: "val")$ and $type(Gamma, v_2, tau_2, type: "val")$ conclude $type(Gamma, tuple(v_1, v_2), tuple(tau_1, tau_2), type: "val")$. Without it, a tuple could not be substituted for a variable in a value position, such as the body of $Lambda alpha. v$. In the figure, the rule for $lambda$ is named T-E-Abs.

*Errors.* $eblame(p)$ is a value, typed by T-E-Error: $type(Gamma, eblame(p), tau, type: "val")$ for any $tau$. Step-E-Error aborts the program, $E[eblame(p)] estep eblame(p)$ for $E != square.stroked$. We drop the context $eblame(E)$ of the figure, since the argument of an error is a party, not an expression.

*Effect rows and signatures.* Rows are lists of labels and may contain duplicates. For a list of labels $L = l_n, ..., l_1$, the row $row(L, epsilon)$ is $chevron.l l_n | ... chevron.l l_1 | epsilon chevron.r ... chevron.r$. Unlike $F^epsilon$, we do not quotient rows by permutation: the rows below are built by the same ordered concatenation. As in @ningning2020effect, operation names are globally unique, so $op in Sigma(l)$ determines $l$, and T-E-Ops gives a handler for $l$ exactly one clause for every operation in $Sigma(l)$.

*Fixpoints.* In #lange, a fixpoint is a recursive value of function or polymorphic type:

#align(center, grid(
  columns: 2,
  column-gutter: 3em,
  row-gutter: 1em,
  [T-E-Fix: from $type(Gamma\, x : tau, v, tau, type: "val")$ conclude $type(Gamma, mu x : tau. v, tau, type: "val")$, where $tau$ is $teff(tau_1, epsilon, tau_2)$ or $forall alpha^k. tau_1$],
  [],
  [Step-E-Fix-App: $apply((mu x : tau. v), v_0) estepx apply(v[x:=mu x : tau. v], v_0)$],
  [Step-E-Fix-TApp: $(mu x : tau. v)[tau_s] estepx v[x:=mu x : tau. v][tau_s]$],
))

#remark[
  The lifted fixpoint of #langb, which unfolds $mu x : tau. e$ to $e[x:=mu x : tau. e]$ for any $e$, does not preserve types once effects are tracked. Let $tau = teff(unit, mteff, numt)$ and

  $e = apply((#kw("lambda")^effs(l) y. #kw("lambda")^mteff \_ : unit. apply(x, unit)), apply(eperform(mteff, op, tau_s), v))$.

  Then $type(x : tau, e, tau, eff: effs(l))$, so $mu x : tau. e$ has type $tau$ with effect $effs(l)$. After one step, $mu x : tau. e$ sits in the body of $lambda \_ : unit. dots$, which has effect $mteff$. But $mu x : tau. e$ can only be typed with the effect of the $prf$ in $e$, so the result is not well typed. Restricting the body to a value avoids this. A value can be given any effect, and so can a recursive value. The $kw("wrap")$ handler of the compiler is such a recursive value.
]

== Evaluation Contexts

$lbls(E)$ collects the labels of the handlers in $E$, innermost first. $bop(E)$ collects the operations they handle.

$
lbls(F_0 dot.c hnd h_1 dot.c F_1 dot.c ... dot.c hnd h_n dot.c F_n) = l_n, ..., l_1 quad "where" h_i : Sigma(l_i)
$

$
bop(square.stroked) = emptyset quad quad bop(F[E]) = bop(E) quad quad bop(ehandle(epsilon, h, E)) = bop(E) union {op | (op -> f) in h}
$

where $F$ is a single frame without a handler. A handler $h : Sigma(l)$ has a clause for every operation of $l$ (T-E-Ops). So a context $E$ handles $op in Sigma(l)$, i.e. $op in bop(E)$, exactly when $l$ occurs in $lbls(E)$.

The judgment $tec(Gamma, E, tau_1, tau_2, epsilon)$ types a context as a function from the type of its hole to the type of the whole expression, where the whole expression has effect $epsilon$.

#figure(
  rule-set(
    prooftree(rule(name: "CE-Empty", $tec(Gamma, square.stroked, tau, tau, epsilon)$)),
    prooftree(rule(
      name: "CE-App1",
      $type(Gamma, e, tau_2, eff: epsilon)$,
      $tec(Gamma, E, tau_1, (teff(tau_2, epsilon, tau_3)), epsilon)$,
      $tec(Gamma, apply(E, e), tau_1, tau_3, epsilon)$,
    )),
    prooftree(rule(
      name: "CE-App2",
      $type(Gamma, v, teff(tau_2, epsilon, tau_3), type: "val")$,
      $tec(Gamma, E, tau_1, tau_2, epsilon)$,
      $tec(Gamma, apply(v, E), tau_1, tau_3, epsilon)$,
    )),
    prooftree(rule(
      name: "CE-TApp",
      $tec(Gamma, E, tau_1, forall alpha. tau_2, epsilon)$,
      $tec(Gamma, E[tau], tau_1, tau_2[alpha:=tau], epsilon)$,
    )),
    prooftree(rule(
      name: "CE-Handle",
      $tops(Gamma, h, tau, l, epsilon)$,
      $tec(Gamma, E, tau_1, tau, row(l, epsilon))$,
      $tec(Gamma, ehandle(epsilon, h, E), tau_1, tau, epsilon)$,
    )),
    prooftree(rule(
      name: "CE-If",
      $tec(Gamma, E, tau_1, boolt, epsilon)$,
      $type(Gamma, e_2, tau, eff: epsilon)$,
      $type(Gamma, e_3, tau, eff: epsilon)$,
      $tec(Gamma, ife(E, e_2, e_3), tau_1, tau, epsilon)$,
    )),
    prooftree(rule(
      name: "CE-Op1",
      $tec(Gamma, E, tau_1, tau_a, epsilon)$,
      $type(Gamma, e, tau_b, eff: epsilon)$,
      $tec(Gamma, E o e, tau_1, tau_o, epsilon)$,
    )),
    prooftree(rule(
      name: "CE-Op2",
      $type(Gamma, v, tau_a, eff: epsilon)$,
      $tec(Gamma, E, tau_1, tau_b, epsilon)$,
      $tec(Gamma, v o E, tau_1, tau_o, epsilon)$,
    )),
  ),
  caption: [Typing of evaluation contexts. The frames $iszero(E)$, $tuple(E, e)$, $tuple(v, E)$, $injl(E)$, $injr(E)$ have rules CE-Zero, CE-Tuple1, CE-Tuple2, CE-Inj-Left, CE-Inj-Right of the same form, following the type rule of the frame.]
) <effects-context-rules>

Only CE-Handle changes the effect: the hole of $ehandle(epsilon, h, E)$ is typed under $row(l, epsilon)$. Following the definitions, for every context

$
row(lbls(apply(E, e)), epsilon) = row(lbls(E), epsilon) quad quad row(lbls(ehandle(epsilon, h, E)), epsilon) = row(lbls(E), row(l, epsilon))
$

and likewise for every frame without a handler.



== Statements and proofs

#lemma(title: [Evaluation context typing])[
  If $tec(dot, E, tau_1, tau, epsilon)$ and $type(dot, e, tau_1, eff: row(lbls(E), epsilon))$ then $type(dot, E[e], tau, eff: epsilon)$.
] <evaluation-context-typing>

#proof[
  By induction on the derivation of $tec(dot, E, tau_1, tau, epsilon)$.

  - Case CE-Empty. $E[e] = e$ and $row(lbls(square.stroked), epsilon) = epsilon$.

  - Case CE-App1, $E = apply(E_0, e_0)$.
    #mp((
      ($tec(dot, E_0, tau_1, (teff(tau_2, epsilon, tau)), epsilon)$, rn("CE-App1")),
      ($type(dot, e_0, tau_2, eff: epsilon)$, rn("CE-App1")),
      ($type(dot, e, tau_1, eff: row(lbls(E_0), epsilon))$, [given, $lbls(E) = lbls(E_0)$]),
      ($type(dot, E_0[e], teff(tau_2, epsilon, tau), eff: epsilon)$, "I.H."),
      ($type(dot, apply(E_0[e], e_0), tau, eff: epsilon)$, rn("T-E-App")),
    ))

  - Case CE-App2, $E = apply(v, E_0)$.
    #mp((
      ($type(dot, v, teff(tau_2, epsilon, tau), type: "val")$, rn("CE-App2")),
      ($tec(dot, E_0, tau_1, tau_2, epsilon)$, rn("CE-App2")),
      ($type(dot, E_0[e], tau_2, eff: epsilon)$, "I.H."),
      ($type(dot, v, teff(tau_2, epsilon, tau), eff: epsilon)$, rn("T-E-Val")),
      ($type(dot, apply(v, E_0[e]), tau, eff: epsilon)$, rn("T-E-App")),
    ))

  - Case CE-TApp, $E = E_0[tau_0]$ and $tau = tau_2[alpha:=tau_0]$.
    #mp((
      ($tec(dot, E_0, tau_1, forall alpha. tau_2, epsilon)$, rn("CE-TApp")),
      ($type(dot, E_0[e], forall alpha. tau_2, eff: epsilon)$, "I.H."),
      ($type(dot, E_0[e][tau_0], tau_2[alpha:=tau_0], eff: epsilon)$, rn("T-E-Tapp")),
    ))

  - Case CE-Handle, $E = ehandle(epsilon, h, E_0)$.
    #mp((
      ($tops(dot, h, tau, l, epsilon)$, rn("CE-Handle")),
      ($tec(dot, E_0, tau_1, tau, row(l, epsilon))$, rn("CE-Handle")),
      ($type(dot, e, tau_1, eff: row(lbls(E_0), row(l, epsilon)))$, [given, def. of $lbls(dot.op)$]),
      ($type(dot, E_0[e], tau, eff: row(l, epsilon))$, "I.H."),
      ($type(dot, ehandle(epsilon, h, E_0[e]), tau, eff: epsilon)$, rn("T-E-Handle")),
    ))

  - Case CE-If, $E = ife(E_0, e_2, e_3)$.
    #mp((
      ($tec(dot, E_0, tau_1, boolt, epsilon)$, rn("CE-If")),
      ($type(dot, e_2, tau, eff: epsilon), type(dot, e_3, tau, eff: epsilon)$, rn("CE-If")),
      ($type(dot, E_0[e], boolt, eff: epsilon)$, "I.H."),
      ($type(dot, ife(E_0[e], e_2, e_3), tau, eff: epsilon)$, rn("T-If")),
    ))

  - Cases CE-Op1, CE-Op2, CE-Zero, CE-Tuple1, CE-Tuple2, CE-Inj-Left, CE-Inj-Right. As CE-If: the I.H. on $E_0$, then the lifted rule of #langb for the frame.
]

#lemma(title: [Effect corresponds to the evaluation context])[
  If $type(dot, E[e], tau, eff: epsilon)$ then there is $tau_1$ such that $tec(dot, E, tau_1, tau, epsilon)$ and $type(dot, e, tau_1, eff: row(lbls(E), epsilon))$.
] <effect-correspondence>

#proof[
  By induction on $E$.

  - Case $E = square.stroked$. Take $tau_1 = tau$, and use CE-Empty.

  - Case $E = apply(E_0, e_0)$.
    #mp((
      ($type(dot, E_0[e], teff(tau_2, epsilon, tau), eff: epsilon)$, rn("T-E-App")),
      ($type(dot, e_0, tau_2, eff: epsilon)$, rn("T-E-App")),
      ($tec(dot, E_0, tau_1, (teff(tau_2, epsilon, tau)), epsilon)$, "I.H."),
      ($type(dot, e, tau_1, eff: row(lbls(E_0), epsilon))$, "I.H."),
      ($tec(dot, apply(E_0, e_0), tau_1, tau, epsilon)$, rn("CE-App1")),
      ($type(dot, e, tau_1, eff: row(lbls(E), epsilon))$, [$lbls(E) = lbls(E_0)$]),
    ))

  - Case $E = apply(v, E_0)$.
    #mp((
      ($type(dot, v, teff(tau_2, epsilon, tau), eff: epsilon)$, rn("T-E-App")),
      ($type(dot, v, teff(tau_2, epsilon, tau), type: "val")$, [inversion of #rn("T-E-Val")]),
      ($type(dot, E_0[e], tau_2, eff: epsilon)$, rn("T-E-App")),
      ($tec(dot, E_0, tau_1, tau_2, epsilon)$, "I.H."),
      ($type(dot, e, tau_1, eff: row(lbls(E_0), epsilon))$, "I.H."),
      ($tec(dot, apply(v, E_0), tau_1, tau, epsilon)$, rn("CE-App2")),
    ))

    The value $v$ has a function type, so it is not a tuple, and its derivation ends in T-E-Val.

  - Case $E = E_0[tau_0]$.
    #mp((
      ($type(dot, E_0[e], forall alpha. tau_2, eff: epsilon)$, [#rn("T-E-Tapp"), $tau = tau_2[alpha:=tau_0]$]),
      ($tec(dot, E_0, tau_1, forall alpha. tau_2, epsilon)$, "I.H."),
      ($type(dot, e, tau_1, eff: row(lbls(E_0), epsilon))$, "I.H."),
      ($tec(dot, E_0[tau_0], tau_1, tau, epsilon)$, rn("CE-TApp")),
    ))

  - Case $E = ehandle(epsilon, h, E_0)$ with $h : Sigma(l)$.
    #mp((
      ($tops(dot, h, tau, l, epsilon)$, rn("T-E-Handle")),
      ($type(dot, E_0[e], tau, eff: row(l, epsilon))$, rn("T-E-Handle")),
      ($tec(dot, E_0, tau_1, tau, row(l, epsilon))$, "I.H."),
      ($type(dot, e, tau_1, eff: row(lbls(E_0), row(l, epsilon)))$, "I.H."),
      ($tec(dot, ehandle(epsilon, h, E_0), tau_1, tau, epsilon)$, rn("CE-Handle")),
      ($type(dot, e, tau_1, eff: row(lbls(E), epsilon))$, [def. of $lbls(dot.op)$]),
    ))

  - Case $E = ife(E_0, e_2, e_3)$.
    #mp((
      ($type(dot, E_0[e], boolt, eff: epsilon)$, rn("T-If")),
      ($type(dot, e_2, tau, eff: epsilon), type(dot, e_3, tau, eff: epsilon)$, rn("T-If")),
      ($tec(dot, E_0, tau_1, boolt, epsilon)$, "I.H."),
      ($type(dot, e, tau_1, eff: row(lbls(E_0), epsilon))$, "I.H."),
      ($tec(dot, ife(E_0, e_2, e_3), tau_1, tau, epsilon)$, rn("CE-If")),
    ))

  - Cases of the other frames of #langb. As $ife(E_0, e_2, e_3)$: invert the lifted rule of the frame, apply the I.H., and close with the context rule of the frame.
]

#lemma(title: [Well typed operations are handled])[
  If $type(dot, E[apply(eperform(epsilon_p, op, tau_s), v)], tau, eff: mteff)$ then $E = E_1[ehandle(epsilon, h, E_2)]$ with $op in.not bop(E_2)$ and $(op -> f) in h$.
] <operations-handled>

#proof[
  Let $op : forall alpha. tau_1 -> tau_2 in Sigma(l)$.
  #mp((
    ($type(dot, apply(eperform(epsilon_p, op, tau_s), v), tau_3, eff: row(lbls(E), mteff))$, [@effect-correspondence]),
    ($type(dot, eperform(epsilon_p, op, tau_s), teff(tau_4, row(lbls(E), mteff), tau_3), eff: row(lbls(E), mteff))$, rn("T-E-App")),
    ($type(dot, eperform(epsilon_p, op, tau_s), teff(tau_4, row(lbls(E), mteff), tau_3), type: "val")$, rn("T-E-Val")),
    ($row(l, epsilon_0) = row(lbls(E), mteff)$, [#rn("T-E-Perform"), where $epsilon_0$ is the explicit annotation of $eperform(epsilon_p, op, tau_s)$]),
    ($l in lbls(E)$, [the row is not empty]),
  ))

  So some handler in $E$ is for $l$, and it has a clause for $op$. Take $ehandle(epsilon, h, E_2)$ to be the innermost handler of $E$ with a clause for $op$. Then $(op -> f) in h$, and no handler in $E_2$ handles $op$, so $op in.not bop(E_2)$.
]

#lemma(title: [Effect types are meaningful])[
  If $type(dot, E[apply(eperform(epsilon_p, op, tau_s), v)], tau, eff: epsilon)$ with $op in.not bop(E)$ and $op in Sigma(l)$, then $l in epsilon$.
] <meaningful-effect-type>

#proof[
  #mp((
    ($type(dot, apply(eperform(epsilon_p, op, tau_s), v), tau_3, eff: row(lbls(E), epsilon))$, [@effect-correspondence]),
    ($type(dot, eperform(epsilon_p, op, tau_s), teff(tau_4, row(lbls(E), epsilon), tau_3), type: "val")$, [#rn("T-E-App"), #rn("T-E-Val")]),
    ($row(l, epsilon_0) = row(lbls(E), epsilon)$, rn("T-E-Perform")),
    ($l in.not lbls(E)$, [$op in.not bop(E)$]),
  ))

  The row on the left starts with $l$. If $lbls(E)$ were not empty, the row on the right would start with a label of $lbls(E)$, which is not $l$. So $lbls(E)$ is empty and $row(l, epsilon_0) = epsilon$, hence $l in epsilon$.
]

#lemma(title: [Value typing])[
  If $type(Gamma, v, tau, eff: epsilon)$ then $type(Gamma, v, tau, type: "val")$. Hence $type(Gamma, v, tau, eff: epsilon_0)$ for every $epsilon_0$.
] <values-any-effect>

#proof[
  By induction on $v$. The second part follows from the first by T-E-Val.

  - Case $v = tuple(v_1, v_2)$. The derivation ends in T-E-Val or in the lifted T-Tuple. In the first case we are done. In the second:
    #mp((
      ($type(Gamma, v_1, tau_1, eff: epsilon), type(Gamma, v_2, tau_2, eff: epsilon)$, rn("T-Tuple")),
      ($type(Gamma, v_1, tau_1, type: "val"), type(Gamma, v_2, tau_2, type: "val")$, "I.H."),
      ($type(Gamma, tuple(v_1, v_2), tuple(tau_1, tau_2), type: "val")$, rn("T-E-VTuple")),
    ))

  - Any other value. The only rule that types it with an effect is T-E-Val, and its premise is the goal.
]

#lemma(title: [Weakening])[
  If $type(Gamma, e, tau, eff: epsilon)$ and $x in.not "dom"(Gamma)$ then $type(Gamma\, x : tau_s, e, tau, eff: epsilon)$, and likewise for $attach(tack.r.short, br: "val")$, $attach(tack.r.short, br: "ops")$ and $attach(tack.r.short, br: "ec")$.
] <weakening>

#proof[
  By induction on the derivation. Only T-E-Abs and T-E-Fix extend $Gamma$, with a bound variable that we choose different from $x$. The side condition $alpha in.not "ftv"(Gamma\, x : tau_s)$ of T-E-Perform holds by choosing the quantified $alpha$ of the signature fresh.
]

#lemma(title: [Variable substitution])[
  Let $type(Gamma_1\, Gamma_2, v, tau_1, type: "val")$.
  1. If $type(Gamma_1\, x : tau_1\, Gamma_2, e, tau, eff: epsilon)$ then $type(Gamma_1\, Gamma_2, e[x:=v], tau, eff: epsilon)$.
  2. If $type(Gamma_1\, x : tau_1\, Gamma_2, v_0, tau, type: "val")$ then $type(Gamma_1\, Gamma_2, v_0[x:=v], tau, type: "val")$.
  3. If $tops(Gamma_1\, x : tau_1\, Gamma_2, h, tau, l, epsilon)$ then $tops(Gamma_1\, Gamma_2, h[x:=v], tau, l, epsilon)$.
] <var-substitution>

#proof[
  By mutual induction on the derivations. Let $Gamma = Gamma_1, x : tau_1, Gamma_2$ and $Gamma_0 = Gamma_1, Gamma_2$. Since $v$ is a value, $v_0[x:=v]$ is again a value, so the value rules still apply after substitution.

  Part 2.

  - Case T-E-Var with $v_0 = x$. Then $tau = tau_1$ and $x[x:=v] = v$, which has type $tau_1$ by assumption.

  - Case T-E-Var with $v_0 = y != x$.
    #mp((
      ($y : tau in Gamma_0$, [#rn("T-E-Var"), $y != x$]),
      ($type(Gamma_0, y[x:=v], tau, type: "val")$, [#rn("T-E-Var"), $y[x:=v] = y$]),
    ))

  - Case T-E-Abs with $v_0 = #kw("lambda")^epsilon_0 y : tau_2. e$, $y in.not {x} union "fv"(v)$.
    #mp((
      ($type(Gamma\, y : tau_2, e, tau_3, eff: epsilon_0)$, rn("T-E-Abs")),
      ($type(Gamma_0\, y : tau_2, v, tau_1, type: "val")$, [@weakening]),
      ($type(Gamma_0\, y : tau_2, e[x:=v], tau_3, eff: epsilon_0)$, "I.H. 1"),
      ($type(Gamma_0, #kw("lambda")^epsilon_0 y : tau_2. e[x:=v], teff(tau_2, epsilon_0, tau_3), type: "val")$, rn("T-E-Abs")),
    ))

  - Case T-E-Fix with $v_0 = mu y : tau. v_1$. As T-E-Abs, with the I.H. 2 on $v_1$.

  - Case T-E-TAbs with $v_0 = Lambda alpha^k. v_1$.
    #mp((
      ($type(Gamma, v_1, tau_2, type: "val"), k != lab$, rn("T-E-TAbs")),
      ($type(Gamma_0, v_1[x:=v], tau_2, type: "val")$, "I.H. 2"),
      ($type(Gamma_0, Lambda alpha^k. v_1[x:=v], forall alpha^k. tau_2, type: "val")$, rn("T-E-TAbs")),
    ))

  - Case T-E-Handler with $v_0 = ehandler(epsilon_0, h)$.
    #mp((
      ($tops(Gamma, h, tau_2, l, epsilon_0)$, rn("T-E-Handler")),
      ($tops(Gamma_0, h[x:=v], tau_2, l, epsilon_0)$, "I.H. 3"),
      ($type(Gamma_0, ehandler(epsilon_0, h[x:=v]), teff((teff(unit, row(l, epsilon_0), tau_2)), epsilon_0, tau_2), type: "val")$, rn("T-E-Handler")),
    ))

  - Case T-E-VTuple with $v_0 = tuple(v_1, v_2)$. The I.H. 2 on both components, then T-E-VTuple.

  - Case T-E-Perform with $v_0$ an effect operation form. It has no *term* variables, so term substitution leaves its type instantiation and explicit tail annotation unchanged. The side condition $alpha in.not "ftv"(Gamma_0)$ follows from $alpha in.not "ftv"(Gamma)$.

  - Cases T-Num, T-Bool, T-Unit, T-E-Error. No variables.

  Part 1.

  - Case T-E-Val.
    #mp((
      ($type(Gamma, v_0, tau, type: "val")$, rn("T-E-Val")),
      ($type(Gamma_0, v_0[x:=v], tau, type: "val")$, "I.H. 2"),
      ($type(Gamma_0, v_0[x:=v], tau, eff: epsilon)$, rn("T-E-Val")),
    ))

  - Case T-E-App with $e = apply(e_1, e_2)$.
    #mp((
      ($type(Gamma, e_1, teff(tau_2, epsilon, tau), eff: epsilon), type(Gamma, e_2, tau_2, eff: epsilon)$, rn("T-E-App")),
      ($type(Gamma_0, e_1[x:=v], teff(tau_2, epsilon, tau), eff: epsilon)$, "I.H. 1"),
      ($type(Gamma_0, e_2[x:=v], tau_2, eff: epsilon)$, "I.H. 1"),
      ($type(Gamma_0, apply(e_1, e_2)[x:=v], tau, eff: epsilon)$, rn("T-E-App")),
    ))

  - Case T-E-Tapp with $e = e_1[tau_0]$. The I.H. 1 on $e_1$, then T-E-Tapp.

  - Case T-E-Handle with $e = ehandle(epsilon, h, e_1)$. The explicit residual annotation $epsilon$ is unchanged by term substitution.
    #mp((
      ($tops(Gamma, h, tau, l, epsilon)$, rn("T-E-Handle")),
      ($type(Gamma, e_1, tau, eff: row(l, epsilon))$, rn("T-E-Handle")),
      ($tops(Gamma_0, h[x:=v], tau, l, epsilon)$, "I.H. 3"),
      ($type(Gamma_0, e_1[x:=v], tau, eff: row(l, epsilon))$, "I.H. 1"),
      ($type(Gamma_0, (ehandle(epsilon, h, e_1))[x:=v], tau, eff: epsilon)$, rn("T-E-Handle")),
    ))

  - Cases of the lifted rules of #langb (T-Tuple, T-If, T-Op, T-Zero, T-Inj-Left, T-Inj-Right). The I.H. 1 on every premise, then the same rule.

  Part 3.

  - Case T-E-Ops. Each operation clause has the type prescribed by T-E-Ops, with the residual row $epsilon$ on all three arrows. Apply I.H. 2 to every clause body. The result has the same clause type under $Gamma_0$, and T-E-Ops applies because its side conditions mention only $epsilon$ and $tau$.
]

#lemma(title: [Type variable substitution])[
  If $type(Gamma, e, tau, eff: epsilon)$ and $attach(tack.r.short, br: "wf") tau_0 : k$ then $type(Gamma[alpha^k:=tau_0], e[alpha^k:=tau_0], tau[alpha^k:=tau_0], eff: epsilon[alpha^k:=tau_0])$, and likewise for $attach(tack.r.short, br: "val")$ and $attach(tack.r.short, br: "ops")$.
] <type-var-substitution>

#proof[
  By induction on the derivation, as Lemma 20 of @ningning2020effect without the evidence translation. Bound type variables are renamed away from $alpha$ and from $"ftv"(tau_0)$, so substitution commutes with them:

  $tau_2[beta:=tau_s][alpha:=tau_0] = tau_2[alpha:=tau_0][beta:=tau_s[alpha:=tau_0]]$ when $beta in.not {alpha} union "ftv"(tau_0)$.

  The interesting cases are the following.

  - Case T-E-Tapp with $e = e_1[tau_s]$.
    #mp((
      ($type(Gamma, e_1, forall beta. tau_2, eff: epsilon)$, rn("T-E-Tapp")),
      ($type(Gamma[alpha:=tau_0], e_1[alpha:=tau_0], forall beta. tau_2[alpha:=tau_0], eff: epsilon[alpha:=tau_0])$, "I.H."),
      ($type(Gamma[alpha:=tau_0], e_1[alpha:=tau_0][tau_s[alpha:=tau_0]], tau_2[alpha:=tau_0][beta:=tau_s[alpha:=tau_0]], eff: epsilon[alpha:=tau_0])$, rn("T-E-Tapp")),
      ($tau_2[alpha:=tau_0][beta:=tau_s[alpha:=tau_0]] = tau_2[beta:=tau_s][alpha:=tau_0]$, "commuting"),
    ))

  - Case T-E-Perform. The type of the operation in $Sigma(l)$ is closed, so only the instantiation $tau_s$ changes, and the conclusion follows by commuting. The quantified variable of the signature is chosen fresh, so it is still not free in $Gamma[alpha:=tau_0]$.

  - Case T-E-Ops. The clause variable is chosen fresh for $tau_0$, so the side condition $beta in.not "ftv"(epsilon[alpha:=tau_0], tau[alpha:=tau_0])$ still holds.

  - Case T-E-TAbs. The bound variable is renamed, and $k != lab$ is unchanged.

  All other cases follow from the I.H. and the same rule.
]

#lemma(title: [Canonical forms])[
  Let $type(dot, v, tau, eff: epsilon)$. Then $v$ is $eblame(p)$, or
  - if $tau = teff(tau_1, epsilon_0, tau_2)$, $v$ is $eabs(epsilon_0, x, tau_1, e)$, an operation form $eperform(epsilon_p, op, tau_s)$ whose operation row is $epsilon_0$, a handler form $ehandler(epsilon_0, h)$, or $mu x : tau. v_0$;
  - if $tau = forall alpha. tau_s$, $v$ is $Lambda alpha. v_0$ or $mu x : tau. v_0$;
  - if $tau$ is $numt$, $boolt$, $unit$ or $tuple(tau_1, tau_2)$, $v$ is $n$, $b$, $unit$ or $tuple(v_1, v_2)$ respectively.
] <effects-canonical>

#proof[
  A variable is not typed in the empty context. By @values-any-effect, $type(dot, v, tau, type: "val")$. Every other value form has exactly one value rule, and the conclusion of that rule fixes the shape of the type. T-E-Error types $eblame(p)$ at any type, and T-E-Fix only gives a function or polymorphic type.
]

#lemma(title: [Steps under contexts])[
  If $e estep e_0$ then $E[e] estep e_0$ for some $e_0$.
] <effects-step-context>

#proof[
  If the step is Step-E, $e = E_1[e_1]$ with $e_1 estepx e_2$, and $E[e] = (E[E_1])[e_1] estep (E[E_1])[e_2]$ by Step-E. If it is Step-E-Error, $e = E_1[eblame(p)]$ with $E_1 != square.stroked$, so $E[E_1] != square.stroked$ and $E[e] estep eblame(p)$ by Step-E-Error.
]

#lemma(title: [Progress with effects])[
  If $type(dot, e_1, tau, eff: epsilon)$ then $e_1$ is a value, or $e_1 estep e_2$, or $e_1 = E[apply(eperform(epsilon_p, op, tau_s), v)]$ with $op in.not bop(E)$.
] <progress-with-effect>

#proof[
  By induction on the typing derivation. Call the last form _stuck on op_.

  - Case T-E-Val. $e_1$ is a value.

  - Case T-E-App, $e_1 = apply(e_3, e_4)$.
    #mp((
      ($type(dot, e_3, teff(tau_1, epsilon, tau), eff: epsilon)$, rn("T-E-App")),
      ($type(dot, e_4, tau_1, eff: epsilon)$, rn("T-E-App")),
    ))

    By the I.H. on $e_3$:
    - $e_3 estep e_5$. Then $e_1$ steps by @effects-step-context.
    - $e_3 = E_0[apply(eperform(epsilon_p, op, tau_s), v)]$. Take $E = apply(E_0, e_4)$. Then $bop(E) = bop(E_0)$, so $e_1$ is stuck on $op$.
    - $e_3$ is a value. By the I.H. on $e_4$:
      - $e_4 estep e_6$. Then $e_1$ steps by @effects-step-context.
      - $e_4 = E_0[apply(eperform(epsilon_p, op, tau_s), v)]$. Take $E = apply(e_3, E_0)$.
      - $e_4$ is a value. By @effects-canonical on $e_3$:
        - $e_3 = #kw("lambda")^epsilon x : tau_1. e$. Then $e_1 estep e[x:=e_4]$ (S-App).
        - $e_3 = ehandler(epsilon, h)$. Then $e_1 estep ehandle(epsilon, h, apply(e_4, unit))$ (Step-E-Handler).
        - $e_3 = eperform(epsilon_p, op, tau_s)$. Take $E = square.stroked$; $e_1$ is stuck on $op$.
        - $e_3 = mu x : tau_f. v_0$. Then $e_1 estep apply(v_0[x:=e_3], e_4)$ (Step-E-Fix-App).
        - $e_3 = eblame(p)$. Error subcase, with the context $apply(square.stroked, e_4)$.

  - Case T-E-Tapp, $e_1 = e_3[tau_1]$ and $type(dot, e_3, forall alpha. tau_2, eff: epsilon)$. By the I.H. on $e_3$:
    - $e_3$ steps, or is stuck on $op$ with context $E_0$. Then $e_1$ steps, or is stuck on $op$ with context $E_0[tau_1]$.
    - $e_3$ is a value. By @effects-canonical:
      - $e_3 = Lambda alpha. v_0$. Then $e_1 estep v_0[alpha:=tau_1]$ (Step-E-TApp).
      - $e_3 = mu x : tau_f. v_0$. Then $e_1 estep v_0[x:=e_3][tau_1]$ (Step-E-Fix-TApp).
      - $e_3 = eblame(p)$. Error subcase.

  - Case T-E-Handle, $e_1 = ehandle(epsilon, h, e_3)$ with $h : Sigma(l)$ and $type(dot, e_3, tau, eff: row(l, epsilon))$. By the I.H. on $e_3$:
    - $e_3$ steps. Then $e_1$ steps by @effects-step-context.
    - $e_3$ is a value. Then $e_1 estep e_3$ (Step-E-Return).
    - $e_3 = E_0[apply(eperform(epsilon_p, op, tau_s), v)]$ with $op in.not bop(E_0)$.
      - If $(op -> f) in h$, then $e_1 estep apply(apply(f[tau_s], v), k)$ with $k = #kw("lambda")^epsilon x : tau_2[alpha:=tau_s]. ehandle(epsilon, h, E_0[x])$ (Step-E-Perform).
      - Otherwise take $E = ehandle(epsilon, h, E_0)$. Then $op in.not bop(E) = bop(E_0) union {op_0 | (op_0 -> f) in h}$, so $e_1$ is stuck on $op$.

  - Case T-If, $e_1 = ife(e_3, e_4, e_5)$. If $e_3$ steps or is stuck, so is $e_1$, with the context $ife(E_0, e_4, e_5)$. If $e_3$ is a value of type $boolt$, it is $trueb$ or $falseb$ and S-If-True or S-If-False applies, or it is $eblame(p)$ (error subcase).

  - Cases T-Op and T-Zero. As T-E-App: evaluate the operands from left to right; if all are values they are numbers or booleans by @effects-canonical and S-Op or S-Zero applies, or one of them is $eblame(p)$ (error subcase).

  - Cases T-Tuple, T-Inj-Left and T-Inj-Right. If the operands are values, a tuple is a value; $injl(tuple(v_1, v_2))$ and $injr(tuple(v_1, v_2))$ step by S-Inj-Left and S-Inj-Right; an operand $eblame(p)$ is the error subcase.
]

#theorem(title: [#lange Progress])[
  If $type(dot, e_1, tau, eff: mteff)$ then $e_1$ is a value or $e_1 estep e_2$.
] <effects-progress>

#proof[
  By @progress-with-effect, $e_1$ is a value, or steps, or $e_1 = E[apply(eperform(epsilon_p, op, tau_s), v)]$ with $op in.not bop(E)$ and $op in Sigma(l)$. The last case is impossible:
  #mp((
    ($type(dot, E[apply(eperform(epsilon_p, op, tau_s), v)], tau, eff: mteff)$, "Given"),
    ($l in mteff$, [@meaningful-effect-type]),
    ("Contradiction", [$mteff$ is empty]),
  ))
]

#lemma(title: [Redex preservation])[
  If $type(dot, e_1, tau, eff: epsilon)$ and $e_1 estepx e_2$ then $type(dot, e_2, tau, eff: epsilon)$.
] <small-step-preservation>

#proof[
  By cases on $e_1 estepx e_2$.

  - Case S-App, $apply((#kw("lambda")^epsilon x : tau_1. e), v) estepx e[x:=v]$.
    #mp((
      ($type(dot, #kw("lambda")^epsilon x : tau_1. e, teff(tau_1, epsilon, tau), eff: epsilon)$, rn("T-E-App")),
      ([The $lambda$ annotation is the body effect $epsilon$.], rn("T-E-Abs")),
      ($type(dot, v, tau_1, eff: epsilon)$, rn("T-E-App")),
      ($type(x : tau_1, e, tau, eff: epsilon)$, [#rn("T-E-Val"), #rn("T-E-Abs")]),
      ($type(dot, v, tau_1, type: "val")$, [@values-any-effect]),
      ($type(dot, e[x:=v], tau, eff: epsilon)$, [@var-substitution]),
    ))

  - Case Step-E-TApp, $(Lambda alpha^k. v)[tau_0] estepx v[alpha:=tau_0]$, with $tau = tau_1[alpha:=tau_0]$.
    #mp((
      ($type(dot, Lambda alpha^k. v, forall alpha^k. tau_1, eff: epsilon), attach(tack.r.short, br: "wf") tau_0 : k$, rn("T-E-Tapp")),
      ($type(dot, v, tau_1, type: "val")$, [#rn("T-E-Val"), #rn("T-E-TAbs")]),
      ($type(dot, v[alpha:=tau_0], tau_1[alpha:=tau_0], type: "val")$, [@type-var-substitution]),
      ($type(dot, v[alpha:=tau_0], tau, eff: epsilon)$, rn("T-E-Val")),
    ))

    The context is empty, and $alpha$ is bound in $Lambda alpha. v$, so $alpha in.not "ftv"(epsilon)$ and $epsilon[alpha:=tau_0] = epsilon$.

  - Case Step-E-Fix-App, $apply((mu x : tau_f. v), v_0) estepx apply(v[x:=mu x : tau_f. v], v_0)$, with $tau_f = teff(tau_1, epsilon, tau)$.
    #mp((
      ($type(dot, mu x : tau_f. v, tau_f, type: "val")$, [#rn("T-E-App"), #rn("T-E-Val")]),
      ($type(dot, v_0, tau_1, eff: epsilon)$, rn("T-E-App")),
      ($type(x : tau_f, v, tau_f, type: "val")$, rn("T-E-Fix")),
      ($type(dot, v[x:=mu x : tau_f. v], tau_f, type: "val")$, [@var-substitution]),
      ($type(dot, apply(v[x:=mu x : tau_f. v], v_0), tau, eff: epsilon)$, [#rn("T-E-Val"), #rn("T-E-App")]),
    ))

  - Case Step-E-Fix-TApp. As Step-E-Fix-App, closing with T-E-Tapp.

  - Case Step-E-Handler, $apply(ehandler(epsilon, h), v) estepx ehandle(epsilon, h, apply(v, unit))$.
    #mp((
      ($type(dot, ehandler(epsilon, h), teff(tau_1, epsilon, tau), eff: epsilon)$, rn("T-E-App")),
      ($type(dot, v, tau_1, eff: epsilon)$, rn("T-E-App")),
      ($type(dot, ehandler(epsilon, h), teff((teff(unit, row(l, epsilon), tau)), epsilon, tau), type: "val")$, rn("T-E-Val")),
      ($tops(dot, h, tau, l, epsilon), tau_1 = teff(unit, row(l, epsilon), tau)$, rn("T-E-Handler")),
      ($type(dot, v, teff(unit, row(l, epsilon), tau), eff: row(l, epsilon))$, [@values-any-effect]),
      ($type(dot, apply(v, unit), tau, eff: row(l, epsilon))$, [#rn("T-Unit"), #rn("T-E-App")]),
      ($type(dot, ehandle(epsilon, h, apply(v, unit)), tau, eff: epsilon)$, rn("T-E-Handle")),
    ))

  - Case Step-E-Return, $ehandle(epsilon, h, v) estepx v$.
    #mp((
      ($type(dot, v, tau, eff: row(l, epsilon))$, rn("T-E-Handle")),
      ($type(dot, v, tau, eff: epsilon)$, [@values-any-effect]),
    ))

  - Case Step-E-Perform, $ehandle(epsilon, h, E[apply(eperform(epsilon_p, op, tau_0), v)]) estepx apply(apply(f[tau_0], v), k)$, where $op in.not bop(E)$, $(op -> f) in h$, $op : forall alpha. tau_1 -> tau_2 in Sigma(l)$ and $k = #kw("lambda")^epsilon x : tau_2[alpha:=tau_0]. ehandle(epsilon, h, E[x])$.
    #mp((
      ($tec(dot, ehandle(epsilon, h, E), tau_3, tau, epsilon)$, [@effect-correspondence]),
      ($type(dot, apply(eperform(epsilon_p, op, tau_0), v), tau_3, eff: row(lbls(E), row(l, epsilon)))$, [@effect-correspondence]),
      ($tops(dot, h, tau, l, epsilon), tec(dot, E, tau_3, tau, row(l, epsilon))$, rn("CE-Handle")),
      ($type(dot, f, forall alpha. teff(tau_1, epsilon, (teff((teff(tau_2, epsilon, tau)), epsilon, tau))), type: "val")$, rn("T-E-Ops")),
      ($alpha in.not "ftv"(epsilon, tau)$, rn("T-E-Ops")),
      ($type(dot, f[tau_0], teff(tau_1[alpha:=tau_0], epsilon, (teff((teff(tau_2[alpha:=tau_0], epsilon, tau)), epsilon, tau))), eff: epsilon)$, [#rn("T-E-Val"), #rn("T-E-Tapp")]),
      ($type(dot, eperform(epsilon_p, op, tau_0), teff(tau_4, row(lbls(E), row(l, epsilon)), tau_3), type: "val")$, [#rn("T-E-App"), #rn("T-E-Val")]),
      ($tau_4 = tau_1[alpha:=tau_0], tau_3 = tau_2[alpha:=tau_0]$, rn("T-E-Perform")),
      ($type(dot, v, tau_1[alpha:=tau_0], eff: epsilon)$, [#rn("T-E-App"), @values-any-effect]),
      ($type(dot, apply(f[tau_0], v), teff((teff(tau_2[alpha:=tau_0], epsilon, tau)), epsilon, tau), eff: epsilon)$, rn("T-E-App")),
      ($type(x : tau_2[alpha:=tau_0], x, tau_2[alpha:=tau_0], eff: row(lbls(E), row(l, epsilon)))$, [#rn("T-E-Var"), #rn("T-E-Val")]),
      ($tec(x : tau_2[alpha:=tau_0], ehandle(epsilon, h, E), tau_2[alpha:=tau_0], tau, epsilon)$, [@weakening]),
      ($type(x : tau_2[alpha:=tau_0], ehandle(epsilon, h, E[x]), tau, eff: epsilon)$, [@evaluation-context-typing]),
      ($type(dot, k, teff(tau_2[alpha:=tau_0], epsilon, tau), eff: epsilon)$, [#rn("T-E-Abs"), #rn("T-E-Val")]),
      ($type(dot, apply(apply(f[tau_0], v), k), tau, eff: epsilon)$, rn("T-E-App")),
    ))

    Substituting for $alpha$ leaves $epsilon$ and $tau$ unchanged, because $alpha in.not "ftv"(epsilon, tau)$.

  - Cases S-If-True, S-If-False, S-Inj-Left, S-Inj-Right, S-Op, S-Zero. As in @langb-redex-preservation, with every judgment at effect $epsilon$.
]

#theorem(title: [#lange Preservation])[
  If $type(dot, e_1, tau, eff: epsilon)$ and $e_1 estep e_2$ then $type(dot, e_2, tau, eff: epsilon)$.
] <effects-preservation>

#proof[
  By cases on the step.

  - Case Step-E, $e_1 = E[e_a]$, $e_2 = E[e_b]$ and $e_a estepx e_b$.
    #mp((
      ($tec(dot, E, tau_1, tau, epsilon)$, [@effect-correspondence]),
      ($type(dot, e_a, tau_1, eff: row(lbls(E), epsilon))$, [@effect-correspondence]),
      ($type(dot, e_b, tau_1, eff: row(lbls(E), epsilon))$, [@small-step-preservation]),
      ($type(dot, E[e_b], tau, eff: epsilon)$, [@evaluation-context-typing]),
    ))

  - Case Step-E-Error, $E[eblame(p)] estep eblame(p)$.
    #mp((
      ($type(dot, eblame(p), tau, type: "val")$, rn("T-E-Error")),
      ($type(dot, eblame(p), tau, eff: epsilon)$, rn("T-E-Val")),
    ))
]

#theorem(title: [#lange Type Safety])[
  If $type(dot, e, tau, eff: mteff)$ and $e estep1 e_0$ then $e_0$ is a value or $e_0 estep e_0$ for some $e_0$.
] <effects-type-safety>

#proof[
  By @effects-preservation on each step, $type(dot, e_0, tau, eff: mteff)$. Then by @effects-progress.
]
