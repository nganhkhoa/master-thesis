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

  // acknowledgements: [

  //   I came to Northwestern during the winter days of 2025 as a collaborator with Professor Xinyu Xing, then in fall, I became a Master student working under Professor Christos Dimoulas. My life here could not have been as fulfill without any of them.

  //   My first thank to Professor Christos Dimoulas, without whom this thesis could not be completed. Since our first meeting, he has been a major support during my studies in programming language theory. As an advisee, I am grateful to have been questioned questions that have changed how I perceive problems, to look at them in different angles. As a student, I have been taught to look at ideas in simpler ways, and build them up. Needlessly, these conversations that we had should carry forward to my future research, and I am fortunate to have been under his guidance.

  //   Honorably, I would like to gave my thank to Professor Robert Findler.

  //   My second thank goes to Professor Xinyu Xing, who trusted me as a collaborator when we had barely worked together before I came to Northwestern. His welcoming attitude introduces me to the B3y0nd team, where I made most of my friends at Northwestern. Even after our collaboration, the team still consider me as a part of the team, sheltering me at the lab during my non-course hours. To Wenxuan, whom I enjoyed having conversations about building computer systems, and arguing about them. I cannot count the number of times we drifted off topic, bridging the gaps between colleague and friend. The B3y0nd team hosts intelligent people that I am fortunate to have met and work alongside them. Thank you Xinqian, Ziyun (NetU), Ziyi, Zhengyu, and Moyang. My only regret is that I was not able to level my Chinese to talk with you all.

  //   Although I did my thesis on programming language theory, I rarely set foot in their lab. However, I managed to connect and discuss ideas with Paul Zhang, Nathaniel Hejduk, and Nick. I regret that we almost never discussed anything technical, or theoretical outside class settings.

  //   Đăng (Midas), 
  // ],

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
#include "contents/conclusion.typ"

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
