#import "@preview/great-theorems:0.1.2": *
#import "@preview/rich-counters:0.2.1": *

#show: great-theorems-init

#let mathcounter = rich-counter(
  identifier: "mathblocks",
  inherited_levels: 1,
)

// Appendix theorem environments, numbered by their enclosing appendix heading.
#let appendix-theorem = mathblock(
  blocktitle: "Theorem",
  counter: mathcounter,
  numbering: "A.1",
)

#let appendix-lemma = mathblock(
  blocktitle: "Lemma",
  counter: mathcounter,
  numbering: "A.1",
)

#let proof = proofblock()

// A derivation is a two-column table: judgment on the left, justification on
// the right. The full-width block prevents the rule column from being clipped.
#let derivation(rows) = block(width: 100%, grid(
  columns: (1fr, auto),
  column-gutter: 2em,
  row-gutter: 0.8em,
  align: (left, right),
  ..rows.flatten(),
))

#let rn(r) = $mono(#r)$

// Number of an appendix theorem/lemma, for restating it elsewhere (e.g. in the body).
#let appendix-number(lbl) = context {
  let d = query(selector(label("great-theorems:numberfunc")).after(lbl)).first()
  (d.value)(d.location())
}
