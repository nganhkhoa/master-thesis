#import "/setup.typ": setupdoc
#show: setupdoc

#import "nuthesis.typ": nuthesis

#import "proofs/setup.typ": *
#import "models/language.typ": langc, lange
#import "utils.typ": load-bib

#show: nuthesis.with(
  title: "Contract Checking as Effects",
  author: "Anh Khoa Nguyen",
  degree: "Master of Science",
  field: "Computer Science",
  campus: "EVANSTON, ILLINOIS",
  graduation-month: "December",
  graduation-year: 2026,

  abstract: [
    Contracts checking can be turned into effects and handled with handlers.
  ],

  acknowledgements: [
    Text for acknowledgments goes here. You can thank your advisors,
    peers, and family.
  ],

  preface: [
    This is the preface (optional).
  ],

  dedication: [
    This is the dedication (optional).
  ]
)

// ==========================================
// THE BODY OF YOUR THESIS STARTS HERE
// ==========================================

#include "contents/intro.typ"
#include "contents/base.typ"
#include "contents/contracts.typ"
#include "contents/effects.typ"

#include "contents/compiler.typ"

#include "contents/implementation.typ"

// ==========================================
// REFERENCES & APPENDICES
// ==========================================

#load-bib(main: true)

#set heading(numbering: "A.1")
#counter(heading).update(0)

#include "proofs/base.typ"

#include "proofs/contracts.typ"
#include "proofs/contract-erasure.typ"

#include "proofs/effects.typ"

#include "proofs/compiler-typesoundness.typ"
#include "proofs/compiler.typ"
#include "proofs/compiler-shallow.typ"
#include "proofs/compiler-local.typ"
