import RelationalOutcomeLogic.Prob.Assertions

/-!
# Semantic judgments over weighted outcomes

This language-independent judgment lets a quantitative certificate refute a
specification of two weight transformers. A probabilistic command language and its
mass-preservation proofs are separate developments.
-/

namespace RelOL.Prob

variable {α β γ δ : Type*}

/-- Every input pair satisfying `P` is transformed to an output pair satisfying `Q`. -/
def quadSem (F : Weight α → Weight γ) (G : Weight β → Weight δ)
    (P : RAssn α β) (Q : RAssn γ δ) : Prop :=
  ∀ μ ν, P μ ν → Q (F μ) (G ν)

/-- A judgment from exact inputs states precisely their output property. -/
@[simp] theorem quadSem_exactly_iff (F : Weight α → Weight γ) (G : Weight β → Weight δ)
    (μ : Weight α) (ν : Weight β) (Q : RAssn γ δ) :
    quadSem F G (exactly μ ν) Q ↔ Q (F μ) (G ν) := by
  constructor
  · intro h
    exact h μ ν ⟨rfl, rfl⟩
  · rintro h _ _ ⟨rfl, rfl⟩
    exact h

end RelOL.Prob
