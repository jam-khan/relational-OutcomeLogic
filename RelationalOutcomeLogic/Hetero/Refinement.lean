import RelationalOutcomeLogic.Hetero.Lang

/-!
# Refinement across the semantic gap

`refines c c'` is the ∀∃-shaped correctness statement of translation
validation: from every in-range initial store (same store on both sides, the
Rust side entered via `.ok`), every C outcome is matched by an ok Rust outcome
with the same store.

Certificate-strength note (Notes.md): a `⊕ ⊤` (outcome-dropping) quadruple can
refute ∀∀-shaped specs but *not* this ∀∃ shape — only the exhaustive (no-`⊤`)
quadruple `translation_bug_exhaustive` yields `not_refines`.
-/

namespace RelOL

/-- Refinement: every C outcome from an in-range store is matched by an ok
Rust outcome with the same resulting store. -/
def refines (c : CmdC) (c' : CmdR) : Prop :=
  ∀ s : StC, InRange s → ∀ t ∈ semC c s, Except.ok t ∈ semR c' s

/-- Sanity: identical assignments refine each other. -/
theorem refines_assign (x : String) (v : Int) :
    refines (.assign x fun _ => v) (.assign x fun _ => v) := by
  rintro s - t ht
  simp only [semC, Set.mem_singleton_iff] at ht
  subst ht
  exact rfl

/-- Refinement **is** a family of left-total couplings: the ∀∃ property the
product model could only refute is positively expressible in the coupling
model. -/
theorem refines_iff_coupleL {c : CmdC} {c' : CmdR} :
    refines c c' ↔ ∀ s : StC, InRange s →
      coupleL (fun t b => b = .ok t) (semC c s) (semR c' s) := by
  constructor
  · intro h s hs t ht
    exact ⟨.ok t, h s hs t ht, rfl⟩
  · intro h s hs t ht
    obtain ⟨b, hb, rfl⟩ := h s hs t ht
    exact hb

end RelOL
