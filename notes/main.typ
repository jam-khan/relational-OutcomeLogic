#import "template.typ": *
#show: notes.with(
  title: "Relational Outcome Logic — Reading Notes",
  author: "Jam Kabeer Ali Khan",
)

#align(center)[
  #text(size: 20pt, weight: "bold")[Relational Outcome Logic] \
  #v(2pt)
  #text(size: 13pt)[Reading Notes] \
  #v(2pt)
  #text(size: 10pt, fill: luma(120))[#datetime.today().display("[month repr:long] [day], [year]")]
]

#v(10pt)

// ── Reading log: one row per sitting ───────────────────────────────────
= Reading log

#table(
  columns: (auto, 1fr, 2fr),
  stroke: 0.5pt + luma(200),
  inset: 6pt,
  table.header([*Date*], [*Paper / sections*], [*One-line takeaway*]),
  // Add a row each sitting, newest first, e.g.:
  // [2026-07-24], [OL OOPSLA23 §3–4], [⊕ is BI over the PCM; reachability lives in atoms],
)

= Contents

#outline(title: none, depth: 2)

// ── Per-paper notes ────────────────────────────────────────────────────
// Core papers
#include "papers/outcome-logic-oopsla23.typ"
#include "papers/hyper-hoare-pldi24.typ"
#include "papers/murray-2020.typ"

// OL follow-ups
#include "papers/outcome-logic-toplas25.typ"
#include "papers/outcome-separation-logic-oopsla24.typ"
#include "papers/demonic-outcome-logic-popl25.typ"
#include "papers/total-outcome-logic.typ"
#include "papers/quantitative-weakest-hyperpre-oopsla24.typ"

// Relational lineage
#include "papers/rhol-icfp17.typ"
#include "papers/erhl-2025.typ"

// ── Cross-cutting synthesis ────────────────────────────────────────────
= Synthesis across papers

#todo[As themes recur across papers, collect them here: the novelty map
(relational × under-approximate × heterogeneous), definitional deltas between
OL versions, and anything that should feed back into the RelOL mechanization
or the paper.]
