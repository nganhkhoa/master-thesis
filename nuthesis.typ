#import "setup.typ": setupdoc

#let nuthesis(
  title: "",
  author: "",
  degree: "DOCTOR OF PHILOSOPHY",
  field: "Mathematics",
  campus: "EVANSTON, ILLINOIS",
  graduation-month: "June",
  graduation-year: none,
  abstract: none,
  acknowledgements: none,
  preface: none,
  dedication: none,
  abbreviations: none,
  glossary: none,
  nomenclature: none,
  body
) = {
  // Default graduation year to current year if not provided
  let grad-year = if graduation-year == none {
    str(datetime.today().year())
  } else {
    str(graduation-year)
  }

  // --- Global Document Setup ---
  setupdoc[]

  // --- Title Page ---
  // The title page is counted (Page 1) but should not display a page number
  set page(numbering: none)

  align(center)[
    NORTHWESTERN UNIVERSITY\
    #v(1fr)
    #title\
    #v(1fr)
    A DISSERTATION\
    #v(0.5cm)
    SUBMITTED TO THE GRADUATE SCHOOL\
    IN PARTIAL FULFILLMENT OF THE REQUIREMENTS\
    #v(0.5cm)
    for the degree\
    #v(0.5cm)
    #degree\
    #v(1fr)
    Field of #field\
    #v(1fr)
    By\
    #v(0.5cm)
    #author\
    #v(1fr)
    #campus\
    #v(0.5cm)
    #graduation-month #grad-year
  ]

  pagebreak()

  // --- Copyright Page ---
  // Begin showing pretext page numbers
  set page(numbering: "1", number-align: top + right)
  counter(page).update(2)

  align(center + horizon)[
    Copyright by #author #grad-year \
    All Rights Reserved
  ]

  pagebreak()

  // --- Heading Configuration ---
  set heading(numbering: "1.1")

  show heading.where(level: 1): it => {
    pagebreak(weak: true)
    align(center)[
      #if it.numbering != none [
        CHAPTER #counter(heading).display() \
        #v(1em)
      ]
      #text(weight: "bold")[#it.body]
    ]
    v(2em)
  }

  show heading.where(level: 2): it => {
    v(1.5em)
    text(weight: "bold")[
      #if it.numbering != none {
        counter(heading).display()
        h(0.5em)
      }
      #it.body
    ]
    v(0.5em)
  }

  // --- Prefatory Pages ---
  if abstract != none {
    heading(numbering: none)[ABSTRACT]
    align(center)[
      #title \ \
      #author
    ]
    v(1em)
    abstract
  }

  if acknowledgements != none {
    heading(numbering: none)[Acknowledgements]
    acknowledgements
  }

  if preface != none {
    heading(numbering: none)[Preface]
    preface
  }

  if abbreviations != none {
    heading(numbering: none)[List of abbreviations]
    abbreviations
  }

  if glossary != none {
    heading(numbering: none)[Glossary]
    glossary
  }

  if nomenclature != none {
    heading(numbering: none)[Nomenclature]
    nomenclature
  }

  if dedication != none {
    heading(numbering: none)[Dedication]
    align(center + horizon)[
      #dedication
    ]
  }

  // --- Table of Contents & Lists ---
  show outline.entry.where(level: 1): it => {
    v(1em, weak: true)
    strong(it)
  }

  heading(numbering: none)[Table of Contents]
  outline(title: none, depth: 3, indent: auto)

  heading(numbering: none)[List of Tables]
  outline(title: none, target: figure.where(kind: table))

  heading(numbering: none)[List of Figures]
  outline(title: none, target: figure.where(kind: image))

  // --- Main Body ---
  // Reset heading counter for Chapter 1
  counter(heading).update(0)

  body
}
