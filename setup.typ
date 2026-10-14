// Shared document setup for every Typst source in this project.
// Keep page, typography, and paragraph defaults here so standalone files and
// the thesis entry point render consistently.
#let setupdoc(body) = {
  set page(
    paper: "us-letter",
    margin: 1in,
    numbering: "1",
    number-align: top + right,
  )

  set text(
    size: 12pt,
    font: "New Computer Modern",
  )

  // Northwestern's thesis guidelines require double-spaced body text.
  set par(
    leading: 1.5em,
    justify: true,
    first-line-indent: 1.5em,
  )

  // Keep compact material compact without changing the document-wide default.
  show quote: set par(leading: 0.65em)
  show figure.caption: set par(leading: 0.65em)
  show list: set par(leading: 0.65em)
  show enum: set par(leading: 0.65em)
  show table: set par(leading: 0.65em)

  body
}
