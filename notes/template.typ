// ── Reading-notes template ─────────────────────────────────────────────
// Helpers for capturing paper reading: metadata headers, statement boxes
// mirroring the papers' own numbering, page-referenced quotes, and
// callouts for insights, questions, critiques, and RelOL connections.

// Document setup: wrap your main file with `#show: notes.with(...)`.
#let notes(title: "Reading Notes", author: "", body) = {
  set document(title: title, author: author)
  set page(
    margin: (x: 2.2cm, y: 2.4cm),
    numbering: "1",
    header: context {
      if counter(page).get().first() > 1 {
        set text(size: 8.5pt, fill: luma(120))
        title
        h(1fr)
        author
      }
    },
  )
  set text(size: 10.5pt)
  set par(justify: true, leading: 0.62em)
  set heading(numbering: none)
  show heading.where(level: 1): it => {
    pagebreak(weak: true)
    set text(size: 16pt)
    block(inset: (bottom: 6pt), stroke: (bottom: 1pt + luma(160)), width: 100%, it)
  }
  show link: set text(fill: rgb("#1a4a8a"))
  body
}

// ── Paper metadata header ──────────────────────────────────────────────
// status: one of "unread" / "skimmed" / "reading" / "read"
#let paper-header(
  title: "",
  authors: "",
  venue: "",
  year: "",
  pdf: "",
  status: "unread",
  tags: (),
) = {
  let status-color = (
    unread: luma(140),
    skimmed: rgb("#b58900"),
    reading: rgb("#1a6fb5"),
    read: rgb("#2a8a3a"),
  ).at(status, default: luma(140))
  block(
    fill: luma(248),
    stroke: 0.5pt + luma(200),
    radius: 4pt,
    inset: 10pt,
    width: 100%,
  )[
    #grid(
      columns: (1fr, auto),
      gutter: 8pt,
      [
        #text(size: 12pt, weight: "bold")[#title] \
        #text(size: 9.5pt)[#authors] \
        #text(size: 9.5pt, style: "italic")[#venue #year]
        #if pdf != "" [ #h(6pt) #text(size: 8.5pt)[· #link("../Papers/" + pdf)[#pdf]] ]
      ],
      align(top + right)[
        #box(fill: status-color.lighten(85%), stroke: 0.5pt + status-color,
          radius: 10pt, inset: (x: 8pt, y: 3pt))[
          #text(size: 8.5pt, fill: status-color.darken(20%), weight: "bold")[#status]
        ]
      ],
    )
    #if tags.len() > 0 {
      v(4pt)
      for t in tags {
        box(fill: luma(235), radius: 8pt, inset: (x: 6pt, y: 2pt),
          text(size: 8pt, fill: luma(80))[#t])
        h(4pt)
      }
    }
  ]
}

// ── Statement boxes (mirror the paper's own numbering in `label`) ──────
#let statement(kind, color, label, body) = block(
  stroke: (left: 2.5pt + color),
  fill: color.lighten(94%),
  inset: (x: 10pt, y: 8pt),
  radius: (right: 3pt),
  width: 100%,
)[
  #text(fill: color.darken(25%), weight: "bold", size: 9.5pt)[#kind #label]
  #h(4pt)
  #body
]

#let defn(label, body) = statement("Definition", rgb("#1a6fb5"), label, body)
#let thm(label, body) = statement("Theorem", rgb("#7a3aa0"), label, body)
#let lem(label, body) = statement("Lemma", rgb("#7a3aa0"), label, body)
#let rule(label, body) = statement("Rule", rgb("#2a8a3a"), label, body)

// ── Page-referenced verbatim quote ─────────────────────────────────────
#let pquote(page, body) = block(
  fill: luma(246),
  stroke: (left: 2.5pt + luma(170)),
  inset: (x: 10pt, y: 7pt),
  radius: (right: 3pt),
  width: 100%,
)[
  #emph(body)
  #h(1fr)
  #text(size: 8.5pt, fill: luma(120))[— p.~#page]
]

// Inline page marker: cite a page while writing, e.g. `... the PCM laws #pg[93:8]`.
#let pg(p) = text(size: 8.5pt, fill: luma(120))[\[p.~#p\]]

// ── Callouts ───────────────────────────────────────────────────────────
#let callout(icon, name, color, body) = block(
  fill: color.lighten(92%),
  stroke: 0.5pt + color.lighten(40%),
  radius: 4pt,
  inset: (x: 10pt, y: 8pt),
  width: 100%,
)[
  #text(fill: color.darken(20%), weight: "bold", size: 9.5pt)[#icon #name]
  #h(6pt)
  #body
]

// Key takeaway worth remembering.
#let insight(body) = callout(sym.star.filled, "Insight", rgb("#b58900"), body)
// Something unresolved to chase down.
#let question(body) = callout("?", "Question", rgb("#1a6fb5"), body)
// Disagreement / suspected error / weakness in the paper.
#let critique(body) = callout(sym.excl, "Critique", rgb("#c0392b"), body)
// How this bears on the RelOL project specifically.
#let relol(body) = callout(sym.arrow.r, "RelOL", rgb("#2a8a3a"), body)
// Reading task.
#let todo(body) = callout(sym.square, "TODO", luma(100), body)
