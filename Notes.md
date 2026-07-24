# RelOL — Decision Ledger & Proof Log

This file records every design choice and every proof that fought back. It feeds
the extended abstract's technical section (per Context.MD §7).

## Design decisions

### D1: Concrete powerset base, no execution-model typeclass
- **Decision:** No monad/PCM typeclass; the PCM is always `(∪, ∅)`. A shared `kleisli`
  engine (`Kleisli.lean`) carries OL Def 3.3's two compatibility laws once
  (`kleisli_union`, `kleisli_empty`); every `semLift` inherits them.
- **Alternatives:** OOPSLA23 bundled monad+PCM structure; TOPLAS25 semiring model.
- **Rationale:** Prototype has no loops, so semiring/Iter machinery is unpaid cost. Both
  case studies live in powerset-shaped carriers. Cite TOPLAS25 as future-work lineage.

### D2: Assertion/quadruple layer polymorphic over carriers from day one
- **Decision:** `RAssn (α β : Type) := Set α → Set β → Prop`; atom/oplus/quad/rules generic.
- **Rationale:** Zero extra proof burden (free type variables, no typeclasses); Phase 4
  heterogeneity (`α := StC`, `β := Except Unit StR`) becomes instantiation, not refactor.

### D3: Two-level quadruple (quadSem over lift functions; quad instantiates)
- **Rationale:** Rules proved once at `quadSem` level with union/empty-preservation
  hypotheses; language-specific facts enter only via the Kleisli kit.

### D4: Prop guards, noncomputable sem
- **Decision:** `b : State → Prop` + classical `if`, `sem` noncomputable.
- **Rationale:** Example pre/post arrive as Prop hypotheses (`s "x" > 0`); Bool guards
  would force `decide`-bridging at every ite. Proofs close by rewriting, not computation.
- **Fallback:** Bool guards, localized to `Lang.lean`.

### D5: Heterogeneous carriers of *different shapes* (deviation from Context.MD §5)
- **Decision:** C-like side = plain `Set StC` (silent wrap via `% WORD`, has `choice`);
  Rust-like side = `Set (Except Unit StR)` (checked add → `.error ()`, deterministic).
  Context.MD had `Set (Except Unit σ)` on both sides.
- **Rationale:** Different carrier shapes + effect repertoires is a *stronger*
  heterogeneity demonstration and the C side proofs get cheaper. Consequence: the
  C-side outcome-existence content is carried by `atom`'s left-nonemptiness (joint
  reachability), not by an `∃ s, a = .ok s` clause.

### D6: Corrected Def 6.3 error-bind orientation
- OOPSLA23's printed Def 6.3 has the ok/error cases apparently swapped (monad laws and
  Example 6.4 force: errors propagate verbatim, ok-states get the continuation).
  Mechanized via `errK`; `errK_assoc` is the regression lemma. Paper footnote material.

### D7: Overlap-friendly ⊕ (no disjointness)
- `oplus` splits via `m = m₁ ∪ m₂` with overlap allowed. Pays off concretely in the
  one-sided Choice rule, where the passive side must self-split `X = X ∪ X` — a
  disjointness-constrained ⊕ would make that rule *false*. (Abstract material.)

### D8: Notation
- `⊕ₒ` for oplus (`⊕` is Sum-type notation); `⦃R⦄ c ~ c' ⦃S⦄` scoped in `RelOL`.

## Recorded traps
- **OL's ⟨true⟩ ≠ ⊤:** the `true` precondition is `atomU (fun _ => True)` (nonemptiness
  baked in), NOT `topU`. With `topU` the pre admits `m = ∅` and any nonemptiness-bearing
  post is unprovable (`semLift c ∅ = ∅`).
- **⊕⊤ vs exhaustive certificates:** the ⊕⊤ (dropping) quadruple refutes ∀∀-shaped specs
  (NI via reachable bad pair); only the exhaustive (no-⊤) quadruple refutes ∀∃-shaped
  specs (refinement). Same quadruple form, two certificate strengths. (Abstract material.)
- **Singleton-pre pattern:** `atom`'s cross-product (∀∀) semantics makes functional-
  equality posts false for non-singleton pres — the product-model-vs-coupling limitation
  surfacing concretely; couplings are future work.

## Proofs that fought back
(record: theorem, what broke, fix)

- **Split probe (Phase 2.2): did NOT fight.** `quadSem_split` closed in 4 lines
  (destructure the pre-split, rewrite with the two union-preservation laws,
  `oplus_intro`). Confirms the prediction: the soundness direction of Split never
  needs Lemma D.3's side conditions (implication-freeness, falsifiable instance) —
  those belong to the *inversion* direction (failure-mode enumeration, Phase 3.6).
  The relational research content is therefore concentrated in falsification
  completeness, not in the proof system.

## Failure-mode catalog (Phase 3.5/3.6 findings — ALL MECHANIZED)
**This is the main negative/structural finding of the project; all of it is
kernel-checked in `Metatheory.lean`.**

- **n = 1 is complete** (`not_atom_iff` / `not_atom_enum`): a relational atom fails in
  exactly one of: left divergence (m = ∅), right divergence (m' = ∅), or a reachable
  bad pair — and the bad pair is itself a positive RelOL certificate `(atom ¬r) ⊕ ⊤`
  via *overlapping* splits `m = {x} ∪ m` (`bad_pair_oplus`). Four primitives vs unary
  OL's three (Lemma 5.5): divergence doubles per side.
- **The unary "bad state reachable" mode is UNSOUND for n ≥ 2**
  (`bad_pair_does_not_refute`): a reachable pair satisfying neither relation does not
  refute `atom r₁ ⊕ atom r₂`, because the split can separate the two outcomes so they
  are never co-located. This has no unary analogue (unary elements must land in *some*
  piece and satisfy its predicate; relational pairs can be split apart).
- **The sound n ≥ 2 generalizations** are: per-side divergence; per-relation joint
  unreachability (`not_oplus_atoms_of_rel_empty_left/right` — "outcome i never jointly
  reached"); and the **orphan mode** (`not_oplus_atoms_of_left_orphan`): an element with
  no partner under *either* relation. The orphan mode has ∃∀ shape and is NOT expressible
  as an `⊕ ⊤` certificate (the ⊕⊤ form only asserts a sub-rectangle, i.e. ∃∃).
- **No unary-style enumeration is complete for n ≥ 2** (`enumeration_incomplete`):
  over `Bool` with `r₁ = (· = ·)`, `r₂ = (· ≠ ·)`, `m = m' = univ`, every mode above is
  absent yet the spec is unsatisfiable. Reason: satisfaction of `atom r₁ ⊕ atom r₂` is a
  **rectangle-cover** condition (∃ rectangles A×A' ⊆ r₁, B×B' ⊆ r₂ covering m, m'
  side-wise), and with r₁ = equality every r₁-rectangle is a diagonal singleton, forcing
  the complementary r₂-rectangle to contain a reflexive pair. The obstruction is
  irreducibly global — exactly the "split correlation" failure predicted in Context.MD §6.
- Abstract framing: *the relational falsifying-assertion problem is not a finite
  enumeration but a rectangle-cover problem; the unary enumeration (OL Lemma 5.5) is the
  degenerate 1-rectangle case.*

## Pinned Mathlib names (v4.32.1)
(record resolved names here at first use)

### D9: Case study 3 — exceptions-to-error-codes lowering (compiler pass)
- **Decision:** Source `CmdS` (core fragment + `throw`) with state-carrying exceptions,
  semantics into `Set (Except State State)`; target = the **ite-fragment of the
  already-mechanized core `Cmd`** (a genuine subset of core, no new target language).
  `errK` generalized over the error type `ε` (Unit for Rust-like, `State` here) — the
  generalization touched nothing downstream.
- Correct pass `lower`: `throw ↦ err := 1`, sequencing guarded by `err = 0`.
  Buggy pass `lowerBug`: guard dropped — target executes dead code after an exception.
- Correspondence `lowRel`: `ok t ~ t` (source can't touch `err`, init `err = 0`);
  `error te ~ update te "err" 1` (throw-point store + flag).
- Certificates (per-program translation validation, NOT compiler verification):
  `lower_ok_correct`, `lower_thr_correct` (correct pass validates on both paths);
  `miscompiled` (exhaustive quadruple: source raises at store with `y = 0`, buggy
  target ends with `y = 2` — Csmith-style observation as a theorem);
  `lowerBug_not_correct` via `denial` — the certificate IS the disproof, the same
  pattern as `not_NI_via_denial` and `not_refines`, now for a third property class.
- Scoping honesty: correctness is per program/pass pair at a concrete initial store;
  a `Wf` predicate (source avoids `"err"`) and a ∀-programs simulation are future work.

## Mechanization status (2026-07-24)
- **All phases complete, whole repo sorry-free** (`scripts/check.sh` green; CI gate active).
- Axiom check on every showcase theorem: only `propext`, `Classical.choice`, `Quot.sound`
  (and `denial`, `quadSem_split` depend on **no** axioms at all).
- ~1,200 LOC (845 nonblank) across 14 files; git tags `phase-0` … `phase-4`.
- Phase 4 acceptance test PASSED: heterogeneity required **zero changes** to
  Assertions/Quadruple/Rules — `quadH` is a 2-line instantiation of `quadSem`.
  The carrier-polymorphism design (D2/D3) fully paid off.
- Certificate-strength asymmetry realized as predicted: `translation_bug` (⊕⊤ form)
  is derived from `translation_bug_exhaustive` by `oplus_left_top`, and only the
  exhaustive form powers `not_refines` (∀∃-shaped spec).

## Abstract outline (2.5–3 pp, structure per Context.MD §8)
1. **Problem** — under-approximate logics are unary (OL) or IL-shaped (Murray);
   relational properties need execution pairs; translation validation needs pairs
   across *different semantics*.
2. **Quadruple** (half page) — `quadSem`/`atom`/`⊕ₒ` definitions; carrying sentence:
   *the same quadruple form states the property (no ⊤) and certifies its violation
   (⊕ ⊤)*; one line on heterogeneity-by-polymorphic-carriers.
3. **Example 1** — `insecure` + `not_NI_via_denial`; contrast with Murray (backward,
   violation-only) in one sentence.
4. **Example 2** — `translation_bug_exhaustive` + `not_refines` + `correct_translation`
   contrast row; certificate-strength asymmetry (⊕⊤ refutes ∀∀, exhaustive refutes ∀∃).
5. **Metatheory** — relational falsification (Thm 5.1 analogue); the failure-mode
   findings: n=1 complete (4 primitives), bad-pair unsound for n≥2, orphan modes,
   mechanized incompleteness (rectangle-cover obstruction) — the paper's main
   structural finding.
6. **Status & roadmap** — mechanized in Lean 4, ~1.2k LOC, sorry-free, standard axioms
   only; future: coupling model, probabilistic instance (→ DP violations), semiring
   base (TOPLAS25), syntactic falsification, proof-producing tactic.
7. **Related work** — OL/TOPLAS25, Murray, HHL (self-composition + explicit
   multiple-programs-future-work concession), Alive2, rF*/Fuzz; eRHL ⊕ symbol-clash
   footnote; "no OL mechanization exists" as a contribution claim.

## Abstract fodder
- "The same quadruple form states the property (no ⊤) and certifies its violation (⊕ ⊤)."
- HHL: "extending Hyper Hoare Logic to multiple programs is interesting future work"
  (PLDI24, pp. 20, 22); OL "does not relate states with each other" (p. 21).
- Murray's quadruple is backward/IL-shaped (∀ finals ∃ initials) and cannot state NI;
  RelOL's forward quadruple does both.
- No mechanization of any OL variant exists in any proof assistant (survey of all
  follow-up papers) — the Lean mechanization is itself a contribution.
