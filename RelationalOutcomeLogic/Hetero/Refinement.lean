import RelationalOutcomeLogic.Hetero.Lang

/-! # Refinement across the two execution models -/

namespace RelOL

/-- Every C outcome from an in-range store is matched by an `ok` Rust outcome. -/
def refines (c : CmdC) (c' : CmdR) : Prop :=
  ∀ s : StC, InRange s → ∀ t ∈ semC c s, Except.ok t ∈ semR c' s

/-- Refinement is a ∀∃ quadruple of the logic. -/
theorem refines_iff_quadH {c : CmdC} {c' : CmdR} :
    refines c c' ↔
      quadH (coupleL fun s a => a = .ok s ∧ InRange s) c c' (coupleL fun t b => b = .ok t) := by
  rw [quadH, semLiftC, semLiftR, quadSem_coupleL_lift_iff]
  constructor
  · rintro h s a ⟨rfl, hs⟩ t ht
    exact ⟨.ok t, h s hs t ht, rfl⟩
  · intro h s hs t ht
    obtain ⟨b, hb, rfl⟩ := h s (.ok s) ⟨rfl, hs⟩ t ht
    exact hb

theorem refines_assign (x : String) (v : Int) :
    refines (.assign x fun _ => v) (.assign x fun _ => v) := by
  rintro s - t ht
  simp only [semC_assign, Set.mem_singleton_iff] at ht
  subst ht
  rfl

end RelOL
