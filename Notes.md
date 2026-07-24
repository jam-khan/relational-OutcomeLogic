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

## Failure-mode catalog (Phase 3.5/3.6 findings)
- Unary OL (Lemma 5.5) has exactly 3 failure modes; relational n=1 already has 4
  primitives (left-divergence, right-divergence, bad-pair-reachable; coverage joins at n≥2).

## Pinned Mathlib names (v4.32.1)
(record resolved names here at first use)

## Abstract fodder
- "The same quadruple form states the property (no ⊤) and certifies its violation (⊕ ⊤)."
- HHL: "extending Hyper Hoare Logic to multiple programs is interesting future work"
  (PLDI24, pp. 20, 22); OL "does not relate states with each other" (p. 21).
- Murray's quadruple is backward/IL-shaped (∀ finals ∃ initials) and cannot state NI;
  RelOL's forward quadruple does both.
- No mechanization of any OL variant exists in any proof assistant (survey of all
  follow-up papers) — the Lean mechanization is itself a contribution.
