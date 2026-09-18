import RelationalOutcomeLogic.Prob.Coupling
import RelationalOutcomeLogic.Coupling

/-!
# From exact weighted couplings to possibilistic couplings

Forgetting weights preserves relational matching of possible outcomes. The reverse
implication does not hold: support matching discards both relative probabilities and
total mass. The existing Set coupling retains its original meaning.
-/

namespace RelOL.Prob

variable {α β : Type*}

/-- A first-marginal outcome is supported exactly when its row contains a supported pair. -/
theorem mem_support_margL_iff (J : Weight (α × β)) (a : α) :
    a ∈ Weight.support (margL J) ↔ ∃ b, (a, b) ∈ Weight.support J := by
  classical
  simp [Weight.support, margL, ENNReal.tsum_eq_zero]

/-- A second-marginal outcome is supported exactly when its column contains a supported pair. -/
theorem mem_support_margR_iff (J : Weight (α × β)) (b : β) :
    b ∈ Weight.support (margR J) ↔ ∃ a, (a, b) ∈ Weight.support J := by
  classical
  simp [Weight.support, margR, ENNReal.tsum_eq_zero]

/-- An exact joint witness induces the existing bitotal Set coupling on supports. -/
theorem IsCoupling.support_couple {R : α → β → Prop} {μ : Weight α} {ν : Weight β}
    {J : Weight (α × β)} (h : IsCoupling R μ ν J) :
    RelOL.couple R (Weight.support μ) (Weight.support ν) := by
  constructor
  · intro a ha
    have ha' : a ∈ Weight.support (margL J) := by rwa [h.margL_eq]
    obtain ⟨b, hab⟩ := (mem_support_margL_iff J a).mp ha'
    refine ⟨b, ?_, h.supported a b hab⟩
    rw [← h.margR_eq]
    exact (mem_support_margR_iff J b).mpr ⟨a, hab⟩
  · intro b hb
    have hb' : b ∈ Weight.support (margR J) := by rwa [h.margR_eq]
    obtain ⟨a, hab⟩ := (mem_support_margR_iff J b).mp hb'
    refine ⟨a, ?_, h.supported a b hab⟩
    rw [← h.margL_eq]
    exact (mem_support_margL_iff J a).mpr ⟨b, hab⟩

/-- Forgetting probability weights gives a sound, one-way bridge to the Set logic. -/
theorem Coupled.support_couple {R : α → β → Prop} {μ : Weight α} {ν : Weight β}
    (h : Coupled R μ ν) : RelOL.couple R (Weight.support μ) (Weight.support ν) := by
  obtain ⟨J, hJ⟩ := h
  exact hJ.support_couple

end RelOL.Prob
