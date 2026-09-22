# Probabilistic Relational Outcome Logic (pRelOL): study checkpoint

Spend the next two to three weeks becoming able to explain and rederive the
development. Feature work can wait. The target is ownership of the definitions,
proof arguments, and limits—not memorizing every Lean lemma.

The mathematical checkpoint is commit `3542464` on `prototype-3`. These materials
were prepared on 2026-09-22 and their source paths have been refreshed for the
subsequent repository reorganization. The Lean sources remain the authority.

The research name is Probabilistic Relational Outcome Logic (pRelOL). The Lean
namespace remains `RelOL`, and the package and import prefix remain
`RelationalOutcomeLogic`. Directory names describe the module's role; they do not
rename Lean declarations.
For example, `Examples/Probability/Search/Case.lean` still defines results in
`RelOL.Prob.Search`, and `Bridges/Probability.lean` contains compatibility results
in `RelOL.Generic`. The theorem index gives both the declaration and its current
source location. Examples now live together under `Examples/`.

## Start here

- [Printable rule handbook](rules.pdf), with [LaTeX source](rules.tex).
- [Manual proof workbook](exercises.md), with hints separated from the questions.
- [Checked rule-to-source index](theorem-index.md), with 59 core declarations and
  their precise assumptions.
- [Public theorem guide](../theorem-guide.md), for exact imports and API names.
- [Weighted semantics](../weighted-semantics.md), [pRHL bridge](../prhl-subsumption.md),
  [loop alignment](../loop-alignment.md), [search case](../randomized-search.md), and
  [semiring models](../semiring-models.md), for explanations of individual layers.

Keep one notebook with four sections: definitions, proofs, counterexamples, and
questions. For each theorem you study, record its statement in ordinary mathematics,
its assumptions, the key proof idea, and one way it would fail without a premise.
Record file and theorem names next to that entry.

Rebuild the PDF from the repository root with `./scripts/build-study.sh` (requires
LaTeX and `latexmk`). The script keeps auxiliary files in a temporary directory and
copies only the finished PDF here. The exercises still study the same mathematical
results; the refreshed paths follow the reorganized production development.

## A sustainable daily session

Allow about three focused hours per core day. Begin with 15 minutes recalling the
previous day's definitions without opening the repository. Spend 45–60 minutes on
targeted reading, 60–75 minutes on one paper proof, and 30–45 minutes checking the
argument against Lean or reconstructing a short proof in your own namespace. End
with a paragraph explaining what you understand and what remains unclear.

Do not read an existing proof before making an attempt. Read theorem statements and
definitions first; stop after roughly an hour of being stuck and use a workbook
hint. The harder loop arguments are explanation exercises in the core schedule,
not a demand to reproduce hundreds of lines of Lean in one afternoon.

Use ten study days across two weeks, leaving weekends or equivalent days for rest
and catch-up. Use the optional third week for the pieces that need another pass.
If a core session takes two days, use the extra week rather than doubling the load.

## Ten core days

| Day | Read and inspect | Work to produce |
| --- | --- | --- |
| 1. Sets and assertions | OL 2023 §§2–4 selectively; `Set/Assertions.lean`, `Set/Coupling.lean`, `Set/Judgment.lean`. Distinguish product atoms, bitotal coupling, and nonempty coupling. | E1; one page defining the judgments and their quantifiers. |
| 2. Composition and splitting | `Set/Semantics.lean`, selected structural rules in `Set/Rules.lean`, then `Generic/Rules.lean`. Return to OL 2023 §4.3. | E2; a handwritten sequencing proof and a splitting proof with each algebraic law named. |
| 3. Weights and joints | `Algebra/ENNReal/Basic.lean`, `Prob/Coupling/Basic.lean`, and `Prob/Semantics/Commands.lean`. Read the coupling/product-program paper's introduction and coupling definitions. | E3; a small joint matrix with verified marginals; explain raw weights versus subprobabilities. |
| 4. The pRHL bridge | [pRHL guide](../prhl-subsumption.md); `Subsumption/PRHL/Embedding.lean`, then the analogous `Generic/Coupling.lean`. | E4; both directions of the bridge, including why arbitrary coupled input weights are allowed. |
| 5. Quantitative refutation and review | `Prob/Refutation/EventMass.lean`, `Prob/Refutation/Certificate.lean`, selected `Prob/Refutation/Observation.lean` statements. Read OL 2023 §5.2 for its falsification viewpoint. | E5; one certificate with its original precondition and postcondition implication. Use remaining time to repair days 1–4. |
| 6. What a loop denotes | `Prob/Semantics/Loop.lean`, `Prob/Coupling/SynchronousLoop.lean`, `Subsumption/PRHL/OneSided.lean`; read [loop alignment](../loop-alignment.md). | E6; finite-approximation calculations, a synchronous proof outline, and the divergent-loop counterexample. |
| 7. Asynchronous alignment | `Examples/Algebra/AsynchronousCountdown.lean` definitions before its proofs; `Generic/Loops/Asynchronous.lean` scheduler and projection theorem. Read the product-program paper's mixed loop rule. | E7; a mode/rank table and a verbal account of both projection inequalities. |
| 8. One complete application | [Search explanation](../randomized-search.md); `Examples/Probability/Search/Programs.lean`, `Examples/Probability/Search/Alignment.lean`, `Examples/Probability/Search/OutcomeContract.lean`, `Examples/Probability/Search/CachedRandomness.lean`, `Examples/Probability/Search/Case.lean`. | E8; the fair two-trial calculation, then a dependency diagram connecting correctness and refutation of the same contract. |
| 9. Shared algebra and five models | [Semiring guide](../semiring-models.md); `Algebra/Outcome/Basic.lean`, `Algebra/Scalar/Basic.lean`, `Algebra/Scalar/Order.lean`, selected instance definitions. Read TOPLAS §3 and selected rules in §4. | E9 and E10 parts 1–3; an assumptions table separating finite algebra, sums, and loops. Save the countdown reproof for day 13 if needed. |
| 10. Compare and teach back | QWHP §§3–5 and §7.4; reread the public theorem guide. Read definitions and main statements before proof appendices. | A two-page comparison and a 20-minute explanation of pRelOL without reading the source. Leave unresolved claims explicitly open. |

Source paths in this table are relative to
[`RelationalOutcomeLogic/`](../../RelationalOutcomeLogic/). E1–E10 are in the
[workbook](exercises.md).

## Optional third week

| Day | Focus | Concrete stopping point |
| --- | --- | --- |
| 11 | Revisit the Set outcome-family loop rule and its convergence premise. | E11: reconstruct the proof outline and identify the assertion families in a small example. |
| 12 | Revisit increasing limits and asynchronous projection. | E12: explain why independently chosen finite couplings are insufficient for the proof used here, and where the rank is consumed. |
| 13 | Reconstruct a generic client in Lean; study noncommutative traces. | Finish E10 or E13 under a fresh namespace. State exactly which scalar laws the proof used. |
| 14 | Read eRHL's coupling definitions, deductive rules, and pRHL comparison. | Add a comparison row for its judgment and termination assumptions; do not assume an embedding into pRelOL without proving one. |
| 15 | Consolidate and choose the next small research experiment. | Explain the search result, its bug certificate, one generic instance, and one unsupported feature. Write a one-page tactic specification based on proof steps you actually found repetitive. |

## Targeted paper reading

Read these for specific questions. There is no requirement to finish every
appendix or reproduce completeness arguments.

1. **Outcome Logic (OOPSLA 2023)** — Zilberstein, Dreyer, and Silva.
   Read §§2–4 and the probabilistic falsification discussion in §5.2. Ask how
   outcome assertions differ from predicates on a single state, and how a failed
   universal specification can have a concrete witness.
   [Local PDF](../../Papers/OutcomeLogicOOPSLA23.pdf);
   [author PDF](https://www.cs.cornell.edu/~noamz/files/pubs/outcome.pdf).
2. **Coupling proofs are probabilistic product programs** — Barthe, Grégoire,
   Hsu, and Strub. Read the product construction and mixed synchronous/asynchronous
   loop rule. Ask what proves the product's marginals and what progress premises
   the rule needs. This is a comparison target, not evidence that our ranked rule
   has the same scope. [Primary source](https://arxiv.org/abs/1607.03455).
3. **Outcome Logic: A Unified Approach to the Metatheory of Program Logics with
   Branching Effects (TOPLAS 2025)** — Zilberstein. Read §3, then §§4.1–4.3 and
   selected loop material in §4.5. Compare partial operations, support restrictions,
   and continuity assumptions with the actual typeclasses here. Skip completeness
   proofs on the first pass.
   [Local PDF](../../Papers/OutcomeLogicTOPLAS25.pdf);
   [author PDF](https://www.cs.cornell.edu/~noamz/files/pubs/toplas25.pdf).
4. **Quantitative Weakest Hyper Pre (OOPSLA 2024)** — Zhang, Zilberstein,
   Kaminski, and Silva. Read the weight/hyperquantity definitions in §3, the
   transformer relation in §4, correctness/refutation in §5, and automation in
   §7.4. Separate what a semantic assertion can express from what a proof rule
   or tactic helps establish.
   [Local final PDF](../../Papers/QuantitativeWeakestHyperPreOOPSLA24.pdf);
   [author final PDF](https://www.cs.cornell.edu/~noamz/files/pubs/whp.pdf);
   [preprint record](https://arxiv.org/abs/2404.05097).
5. **A quantitative probabilistic relational Hoare logic (eRHL)** — Avanzini,
   Barthe, Davoli, and Grégoire. For the optional week, read §§3–4 and §5.1 in the
   local January 2025 version. Compare expectation assertions, coupling semantics,
   and the hypotheses of its pRHL correspondence.
   [Local PDF](../../Papers/eRHL-2025.pdf);
   [primary source](https://arxiv.org/abs/2407.17127).

The local `Papers/` directory is ignored by Git. Online links let another checkout
follow the reading plan without redistributing those PDFs. Older personal notes
are prompts for checking the papers, not a substitute for their definitions.

For the comparison, use columns for judgment, observation domain, termination
meaning, coupling witness, loop premises, refutation method, and automation.
Distinguish a proved repository theorem, a theorem in the cited paper, and an
unproved encoding idea. In particular, do not dismiss QWHP because its surface
syntax describes one program: ask whether two outputs can be represented within
its state/outcome model, then separately assess the available proof interface.
No semantic separation from QWHP has been established by this repository.

## What this checkpoint contains

The development already includes Set rules and refutation, exact probabilistic
couplings, a semantic pRHL bridge with named rules, finite-event quantitative
certificates, full terminating loop semantics, ranked mixed asynchronous loops,
the correct/faulty search case, and a shared algebra with five scalar instances.
The source-to-theorem details are in the handbook and public theorem guide.

Keep the following boundaries visible in your notes:

- The Set outcome-family `While-Fam` rule exists. A weighted/generic counterpart
  for arbitrary outcome assertions is not implemented; the main weighted loop
  rules use coupling invariants.
- Ranked mixed scheduling requires strict natural-rank descent on supported
  unilateral steps. An almost-surely terminating but unbounded unilateral phase
  is not automatically covered. A separate one-sided rule uses whole-loop losslessness.
- The scalar construction uses total summation semirings and explicit increasing-limit
  laws. It does not implement every partial algebra in TOPLAS, continuous sampling,
  or infinite-word traces.
- The search cost statements concern consumed trials and probabilities of strict
  savings. They are not an operational adequacy or expected-running-time theorem.
- `Tactic/Symexec.lean` is basic simplification support. Guided coupling search,
  automatic certificate discovery, further case studies, and external LeanCrypt
  integration remain future work. Completeness is outside the current goal.

## Knowing when to resume development

You are ready when you can explain the following without relying on a theorem
name alone:

1. Why `atom Eq` and `couple Eq` are different assertions.
2. Why support equality cannot establish probabilistic equivalence.
3. Why the pRHL bridge works in both directions and what external integration
   would still have to supply.
4. Why a deficit certificate needs an upper bound on the right event, and how its
   concrete input satisfies the original specification.
5. Where loop divergence goes, why one-sided body losslessness is insufficient,
   and what ranked scheduling proves about full marginals.
6. Which proofs are shared across scalar models, which extra laws enable loops,
   and why tropical order points in the opposite numerical direction.
7. What is useful about this implementation without claiming an unproved novelty
   or expressiveness result.

Keep unresolved questions as a short backlog. At the end of the checkpoint, choose
one next milestone from evidence in your own proofs—such as automating a repeated
finite coupling obligation—rather than immediately expanding the language again.

## Checking your own Lean proofs

Put completed experiments in a separate directory such as `study-work/`, use a
fresh namespace, and run `lake env lean study-work/YourFile.lean` from the repository
root. Import the module being studied or the root `RelationalOutcomeLogic` module.
Do not edit production proofs merely to practice, and do not add unfinished exercise
files to the root imports. Once a practice proof is complete, compare its assumptions
and dependencies with the existing theorem.

The production validation command is `./scripts/check.sh`; it builds the library,
checks production proof placeholders, and audits axioms. The study documents do
not replace that check or add new logical claims to the library.
