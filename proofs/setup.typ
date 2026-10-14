#import "@preview/great-theorems:0.1.2": *
#import "@preview/rich-counters:0.2.1": *

#show: great-theorems-init

#let mathcounter = rich-counter(
  identifier: "mathblocks",
  inherited_levels: 1
)

#let theorem = mathblock(
  blocktitle: "Theorem",
  counter: mathcounter,
  // align: left,
)

#let lemma = mathblock(
  blocktitle: "Lemma",
  counter: mathcounter,
)

#let remark = mathblock(
  blocktitle: "Remark",
  prefix: [_Remark._],
  inset: 5pt,
  fill: lime,
  radius: 5pt,
)

#let proof = proofblock()


// Appendix variants: number with the appendix heading letters ("A.1")
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

// Number of an appendix theorem/lemma, for restating it elsewhere (e.g. in the body).
#let appendix-number(lbl) = context {
  let d = query(selector(label("great-theorems:numberfunc")).after(lbl)).first()
  (d.value)(d.location())
}
