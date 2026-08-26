#let scratch(doc) = {
  // formatting rules
  set heading(numbering: "1.")
  show heading.where(level: 2): set block(below: 1.5em)

  set page(
    header: context {
      if counter(page).get().first() == 1 {
        none
      } else {
        [
          Toby Ueno
          #h(1fr)
          #context document.title
        ]
      }
    },
    numbering: "1"
  )

  show raw.where(block: true): it => {
    show raw.line: line => {
      box(width: 2em)[#align(right)[#text(fill: gray)[#line.number]]]
      h(1em)
      line.body
    }
    it
  }

  // content
  align(center, {
    title()
    text(size: 14pt)[Toby Ueno]
  })

  outline()

  doc
}