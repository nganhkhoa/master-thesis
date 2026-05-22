#import "@preview/great-theorems:0.1.1": *
#import "@preview/rich-counters:0.2.2": *

#set heading(numbering: "1.1")

#show: great-theorems-init

// 1. Setup the mathcounter as per great-theorems requirements
#let mathcounter = rich-counter(
  identifier: "mathblocks",
  inherited_levels: 1
)

#let theorem = mathblock(
  blocktitle: "Theorem",
  counter: mathcounter,
  numbering: "1.1"
)

#let proof = proofblock()

// 2. Global state for storing the theorem body
#let thm-store = state("thm-store", (:))

// 3. Main text: Places the theorem and increments the counter
#let place-theorem(lbl) = context {
  let store = thm-store.final()
  let body = store.at(str(lbl), default: str(lbl))

  // Render and attach the label so it can be queried
  [#theorem(body) #label(str(lbl))]
}

// 4. Appendix: Retrieves the number from the main text location
#let def-theorem(lbl, body) = {
  // Save body to state
  thm-store.update(s => { s.insert(str(lbl), body); s })


  // Return the content directly, don't just "calculate" it
  context {
    let elems = query(lbl)
    if elems.len() > 0 {
      let num = (mathcounter.at)(lbl)
      let num-list = num.map(int) // ensure they are integers
      let last-idx = num-list.len() - 1
      num-list.at(last-idx) = num-list.at(last-idx) + 1
      let formatted-num = numbering("1.1", ..num-list)
      mathblock(blocktitle: "Theorem " + formatted-num)(body)
    } else {
      theorem(body)
    }
  }
}


// = Main Text

// The type soundness relies on progress and preservation.

// #place-theorem(<thm:progress>)
// #place-theorem(<thm:preservation>)

// = Appendix: Proofs


// // The appendix renders the content and pulls the number from above
// #def-theorem(<thm:progress>)[
//   If $emptyset tack e : tau$, then either $e$ is a value, or there exists $e'$ such that $e arrow e'$.
// ]
// #proof(of: <thm:progress>)[
//   By induction on the typing derivation... bruh please render
// ]

// #def-theorem(<thm:preservation>)[
//   If $emptyset tack e : tau$, then either $e$ is a value, or there exists $e'$ such that $e arrow e'$.
// ]
// #proof(of: <thm:preservation>)[
//   By induction on the typing derivation... bruh please render
// ]
