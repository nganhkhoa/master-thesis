#let no-ref(it) = {
  // Catch all @label references
  show ref: r => context {
    // 1. Check if the document has a bibliography
    let has-bib = query(bibliography).len() > 0

    if has-bib {
      // Compiling main.typ: let all references resolve natively
      r
    } else {
      let target-exists = query(r.target).len() > 0
      if target-exists {
        r      // The figure/table exists in this chapter, render it
      } else {
        [[?]]  // The label is missing (citation), fallback to dummy
      }
    }
  }

  // Optional: Catch explicit #cite(<...>) calls if you use them instead of @
  show cite: c => context {
    if query(bibliography).len() > 0 { c } else { [[?]] }
  }

  it
}

#let load-bib(main: false) = {
  counter("bib-count").step()
  context {
    if main {
      [#bibliography("refs.bib", style: "acm.csl", full: true) <main-bib>]
    }
    else if query(<main-bib>) == () and counter("bib-count").get().first() == 1 {
      bibliography("works.bib")
    }
  }
}

#let make-proof(gap: 3em, rows) = {
  show math.equation: set align(left)

  let cells = ()
  for (expr, justification) in rows {
    cells.push(expr)
    cells.push(justification)
  }

  align(center, block(
    grid(
      columns: 2,
      column-gutter: gap,
      row-gutter: 0.8em, // Mimics standard math line spacing
      align: (left, right), // Ensures both expressions and rules are left-aligned
      ..cells
    )
  ))
}

// A derivation as a two column table: the judgment on the left, the rule
// used on the right. The rule column always gets its full width.
#let derivation(rows) = block(width: 100%, grid(
  columns: (1fr, auto),
  column-gutter: 2em,
  row-gutter: 0.8em,
  align: (left, right),
  ..rows.flatten(),
))

// rule names inside derivations
#let rn(r) = $mono(#r)$
