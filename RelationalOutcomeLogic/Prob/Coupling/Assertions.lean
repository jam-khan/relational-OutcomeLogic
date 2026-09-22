import RelationalOutcomeLogic.Prob.Logic.Assertions
import RelationalOutcomeLogic.Prob.Coupling.Basic

/-!
# Exact couplings as weighted assertions

Additive splitting combines joint witnesses by addition. A common scalar rescales
both marginals. These rules use actual weights, with no duplication or normalization.
-/

namespace RelOL.Prob

open scoped ENNReal

variable {α β : Type*}

/-- Exact relation-supported coupling, viewed as a relational outcome assertion. -/
def couple (R : α → β → Prop) : RAssn α β := Coupled R

theorem couple_mono {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    entail (couple R) (couple S) :=
  fun _ _ hμν => hμν.mono h

@[simp] theorem couple_eq_iff {μ ν : Weight α} : couple Eq μ ν ↔ μ = ν :=
  coupled_eq_iff

/-- Related pieces can be added, retaining either piece's relation. -/
theorem oplus_couple {R S : α → β → Prop} :
    entail (oplus (couple R) (couple S)) (couple (fun a b => R a b ∨ S a b)) := by
  rintro μ ν ⟨μ₁, μ₂, ν₁, ν₂, rfl, rfl, h₁, h₂⟩
  exact (h₁.mono (fun _ _ h => Or.inl h)).add (h₂.mono (fun _ _ h => Or.inr h))

theorem oplus_couple_same {R : α → β → Prop} :
    entail (oplus (couple R) (couple R)) (couple R) := by
  rintro μ ν ⟨μ₁, μ₂, ν₁, ν₂, rfl, rfl, h₁, h₂⟩
  exact h₁.add h₂

/-- Common scaling preserves an exact coupling, including zero and infinite scalars. -/
theorem scale_couple (r : ℝ≥0∞) (R : α → β → Prop) :
    entail (scale r (couple R)) (couple R) := by
  rintro μ ν ⟨μ₀, ν₀, rfl, rfl, h⟩
  exact h.smul r

/-- A coupling and either marginal's mass determine both total masses. -/
theorem couple_massEq {R : α → β → Prop} {μ : Weight α} {ν : Weight β}
    (h : couple R μ ν) : massEq (Weight.mass μ) (Weight.mass μ) μ ν :=
  ⟨rfl, h.mass_eq.symm⟩

end RelOL.Prob
