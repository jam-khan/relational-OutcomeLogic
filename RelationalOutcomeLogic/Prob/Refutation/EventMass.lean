import RelationalOutcomeLogic.Prob.Coupling.Basic

/-!
# Finite-event mass bounds for couplings

An exact coupling supported in `R` sends the mass of a finite left event into any
finite right event containing its relational image. This necessary condition gives
sound mass-deficit certificates. The carriers may be infinite, and the weights may
have infinite total mass; only the two events are required to be finite.
-/

open scoped ENNReal

namespace RelOL

namespace Weight

variable {α : Type*}

/-- The total weight of a finite event. -/
noncomputable def eventMass (μ : Weight α) (A : Finset α) : ℝ≥0∞ := ∑ a ∈ A, μ a

@[simp] theorem eventMass_empty (μ : Weight α) : eventMass μ ∅ = 0 := by
  simp [eventMass]

@[simp] theorem eventMass_singleton (μ : Weight α) (a : α) : eventMass μ {a} = μ a := by
  simp [eventMass]

@[simp] theorem eventMass_zero (A : Finset α) : eventMass (0 : Weight α) A = 0 := by
  simp [eventMass]

@[simp] theorem eventMass_univ [Fintype α] (μ : Weight α) :
    eventMass μ Finset.univ = mass μ := by
  simp [eventMass, mass]

open scoped Classical in
@[simp] theorem eventMass_pure (a : α) (A : Finset α) :
    eventMass (pure a) A = if a ∈ A then 1 else 0 := by
  simp [eventMass, pure]

theorem eventMass_mono {μ ν : Weight α} (h : μ ≤ ν) (A : Finset α) :
    eventMass μ A ≤ eventMass ν A :=
  Finset.sum_le_sum fun a _ => h a

theorem eventMass_mono_set (μ : Weight α) {A B : Finset α} (h : A ⊆ B) :
    eventMass μ A ≤ eventMass μ B :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun _ _ _ => zero_le

theorem eventMass_le_mass (μ : Weight α) (A : Finset α) : eventMass μ A ≤ mass μ :=
  ENNReal.sum_le_tsum A

theorem eventMass_add (μ ν : Weight α) (A : Finset α) :
    eventMass (μ + ν) A = eventMass μ A + eventMass ν A :=
  Finset.sum_add_distrib

theorem eventMass_smul (r : ℝ≥0∞) (μ : Weight α) (A : Finset α) :
    eventMass (r • μ) A = r * eventMass μ A := by
  simp only [eventMass, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

end Weight

namespace Prob

variable {α β : Type*}

/-- A coupling bounds each finite event's mass by the mass of a finite cover of its image. -/
theorem IsCoupling.eventMass_le {R : α → β → Prop} {μ : Weight α} {ν : Weight β}
    {J : Weight (α × β)} (h : IsCoupling R μ ν J) (A : Finset α) (B : Finset β)
    (himage : ∀ a ∈ A, ∀ b, R a b → b ∈ B) :
    Weight.eventMass μ A ≤ Weight.eventMass ν B := by
  classical
  change (∑ a ∈ A, μ a) ≤ ∑ b ∈ B, ν b
  calc
    ∑ a ∈ A, μ a = ∑ a ∈ A, ∑ b ∈ B, J (a, b) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [← h.margL_eq]
      exact tsum_eq_sum fun b hb =>
        h.apply_eq_zero_of_not_rel fun hab => hb (himage a ha b hab)
    _ = ∑ b ∈ B, ∑ a ∈ A, J (a, b) := Finset.sum_comm
    _ ≤ ∑ b ∈ B, ∑' a, J (a, b) :=
      Finset.sum_le_sum fun _ _ => ENNReal.sum_le_tsum A
    _ = ∑ b ∈ B, ν b := Finset.sum_congr rfl fun b _ => congrFun h.margR_eq b

/-- Every supported exact coupling satisfies the finite-event mass bound. -/
theorem Coupled.eventMass_le {R : α → β → Prop} {μ : Weight α} {ν : Weight β}
    (h : Coupled R μ ν) (A : Finset α) (B : Finset β)
    (himage : ∀ a ∈ A, ∀ b, R a b → b ∈ B) :
    Weight.eventMass μ A ≤ Weight.eventMass ν B := by
  obtain ⟨J, hJ⟩ := h
  exact hJ.eventMass_le A B himage

end Prob

end RelOL
