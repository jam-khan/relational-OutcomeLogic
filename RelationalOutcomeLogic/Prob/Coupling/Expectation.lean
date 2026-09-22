import RelationalOutcomeLogic.Prob.Coupling.Basic
import RelationalOutcomeLogic.Algebra.ENNReal.Expectation

/-!
# Expectations transported by exact couplings

Pathwise accounting in a relational postcondition implies an expectation bound.
No finiteness or normalization assumption is needed for this transport; constants
are scaled by total mass when a client evaluates the resulting bound.
-/

namespace RelOL.Prob
open scoped ENNReal
variable {α β : Type*}

theorem expectation_margL (J : Weight (α × β)) (f : α → ℝ≥0∞) :
    Weight.expectation (margL J) f = Weight.expectation J (fun p => f p.1) := by
  simp only [Weight.expectation, margL, ENNReal.tsum_mul_right, ENNReal.tsum_prod']

theorem expectation_margR (J : Weight (α × β)) (f : β → ℝ≥0∞) :
    Weight.expectation (margR J) f = Weight.expectation J (fun p => f p.2) := by
  simp only [Weight.expectation, margR, ENNReal.tsum_prod']
  simp_rw [← ENNReal.tsum_mul_right]
  exact ENNReal.tsum_comm

theorem Coupled.expectation_le {R : α → β → Prop} {μ : Weight α} {ν : Weight β}
    (H : Coupled R μ ν) (f : α → ℝ≥0∞) (g : β → ℝ≥0∞)
    (h : ∀ a b, R a b → f a ≤ g b) :
    Weight.expectation μ f ≤ Weight.expectation ν g := by
  obtain ⟨J, hJ⟩ := H
  rw [← hJ.margL_eq, ← hJ.margR_eq, expectation_margL, expectation_margR]
  exact Weight.expectation_mono_on_support J (fun p hp => h p.1 p.2 (hJ.supported _ _ hp))

theorem Coupled.expectation_eq {R : α → β → Prop} {μ : Weight α} {ν : Weight β}
    (H : Coupled R μ ν) (f : α → ℝ≥0∞) (g : β → ℝ≥0∞)
    (h : ∀ a b, R a b → f a = g b) :
    Weight.expectation μ f = Weight.expectation ν g := by
  obtain ⟨J, hJ⟩ := H
  rw [← hJ.margL_eq, ← hJ.margR_eq, expectation_margL, expectation_margR]
  exact Weight.expectation_congr_on_support J (fun p hp => h p.1 p.2 (hJ.supported _ _ hp))

end RelOL.Prob
