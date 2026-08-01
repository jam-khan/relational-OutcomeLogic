import RelationalOutcomeLogic.Examples.NI
import RelationalOutcomeLogic.Examples.GNI

/-!
# Product-NI vs coupling-NI: the model-choice contrast suite

The flagship micro-example for the coupling model. `secProg` publishes `0` or
`1` nondeterministically, **independently of the secret** — it is secure. Yet:

* `not_NI_secProg` — the product-model `NI` (∀∀ rectangle post) *rejects* it:
  the cross pair (`low = 0`, `low' = 1`) disagrees. The rectangle over-flags
  secret-independent nondeterminism.
* `CNI_secProg` — coupling-NI (the standard possibilistic noninterference)
  *accepts* it: pair the branches diagonally.
* `not_CNI_prog` — coupling-NI still catches the genuinely leaky `prog`: on
  per-state deterministic programs couplings and rectangles coincide.
* `GNI_secProg` — the first *positively proved* ∀∃ property in the library,
  via the `coupleL` reading of GNI (`GNI_iff_coupleL`).
-/

namespace RelOL

/-- Coupling-NI: possibilistic noninterference. Some resolution of the two
sides' nondeterminism aligns their public outputs — and every outcome on each
side participates in the alignment. -/
def CNI (c : Cmd) : Prop := ⦃couple L⦄ c ~ c ⦃couple L⦄

/-- Publish `0` or `1`, nondeterministically and secret-independently. -/
def secProg : Cmd :=
  .choice (.assign "low" fun _ => 0) (.assign "low" fun _ => 1)

/-- The product-model `NI` rejects the secure `secProg`: the ∀∀ rectangle
demands *all* cross pairs agree, so it confuses nondeterminism with leakage. -/
theorem not_NI_secProg : ¬ NI secProg := by
  intro h
  have hpost := h {st 0 0} {st 0 0} (atom_singleton_iff.mpr rfl)
  rw [semLift_singleton] at hpost
  have h0 : Function.update (st 0 0) "low" (0 : Int) ∈ sem secProg (st 0 0) := by
    simp [secProg]
  have h1 : Function.update (st 0 0) "low" (1 : Int) ∈ sem secProg (st 0 0) := by
    simp [secProg]
  have hbad := atom_pair_elim hpost h0 h1
  simp [L] at hbad

/-- Coupling-NI accepts `secProg`: align branch 1 with branch 1 and branch 2
with branch 2. -/
theorem CNI_secProg : CNI secProg :=
  quad_choice_couple
    (fun s s' _ => by
      rw [sem_assign, sem_assign]
      exact couple_singleton_iff.mpr (by simp [L]))
    (fun s s' _ => by
      rw [sem_assign, sem_assign]
      exact couple_singleton_iff.mpr (by simp [L]))

/-- Coupling-NI still rejects the genuinely leaky `prog`: from low-equal
stores on opposite sides of the branch, the unique outcomes publish `1`
vs. `0`, and no pairing can hide a disagreement between singletons. -/
theorem not_CNI_prog : ¬ CNI prog := by
  intro h
  have hpost := h {st 1 0} {st 0 0} (couple_singleton_iff.mpr rfl)
  rw [semLift_singleton, semLift_singleton, sem_prog_pos (by simp),
    sem_prog_neg (by simp)] at hpost
  have hbad := couple_singleton_iff.mp hpost
  simp [L] at hbad

/-- GNI is a family of left-total couplings — definitionally. -/
theorem GNI_iff_coupleL {c : Cmd} :
    GNI c ↔ ∀ s s' : State,
      coupleL (fun t t' => t "low" = t' "low") (sem c s) (sem c s') :=
  Iff.rfl

/-- `secProg` satisfies GNI: a positive proof of an ∀∃ hyperproperty, matching
each branch with its twin on the other side. -/
theorem GNI_secProg : GNI secProg := by
  intro s s' t ht
  rw [show sem secProg s = {Function.update s "low" (0 : Int)}
      ∪ {Function.update s "low" (1 : Int)} from rfl] at ht
  rcases ht with ht | ht <;> rw [Set.mem_singleton_iff] at ht <;> subst ht
  · exact ⟨Function.update s' "low" 0, by simp [secProg], by simp⟩
  · exact ⟨Function.update s' "low" 1, by simp [secProg], by simp⟩

end RelOL
