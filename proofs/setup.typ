#import "@preview/great-theorems:0.1.2": *
#import "@preview/rich-counters:0.2.1": *

#show: great-theorems-init

// Inherit only the chapter component, even inside deeply nested sections.
// rich-counters 0.2.1 otherwise truncates the heading counter using a loop
// whose discarded pop values fail to join on newer Typst versions.
#let chapter-counter = (
  at: loc => {
    let value = if loc == none { counter(heading).final() } else { counter(heading).at(loc) }
    (value.first(),)
  },
  inherited_levels: 0,
  last_update_location: (level, loc) => {
    let headings = if loc == none { query(heading) } else { query(selector(heading).before(loc)) }
    for h in headings.rev() {
      if h.level == 1 and h.numbering != none { return h.location() }
    }
    none
  },
)

#let mathcounter = rich-counter(
  identifier: "mathblocks",
  inherited_levels: 1,
  inherited_from: chapter-counter,
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
  // A standalone chapter does not include the appendix theorem. Do not run
  // an unanchored metadata lookup: it can select this restatement's own
  // manual-number metadata and recursively evaluate appendix-number again.
  let targets = query(lbl)
  if targets.len() == 0 {
    [?]
  } else {
    let numbers = query(selector(label("great-theorems:numberfunc"))
      .after(targets.first().location()))
    if numbers.len() == 0 {
      [?]
    } else {
      let d = numbers.first()
      (d.value)(d.location())
    }
  }
}
