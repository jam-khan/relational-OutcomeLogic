import RelationalOutcomeLogic.Algebra.ENNReal.Basic

/-!
# Nonnegative expectations of discrete outcome weights

Expectation is an unnormalized weighted sum. It records abstract operation costs;
interpreting those costs as physical runtime requires an additional model.
All laws allow infinite weights and values. Probability is needed only when a
constant bound is turned into an unscaled expectation bound.
-/

namespace RelOL.Weight

open scoped ENNReal

variable {α β : Type*}

noncomputable def expectation (μ : Weight α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' a, μ a * f a

@[simp] theorem expectation_pure (a : α) (f : α → ℝ≥0∞) :
    expectation (pure a) f = f a := by
  classical
  simp [expectation, pure]

@[simp] theorem expectation_zero (f : α → ℝ≥0∞) : expectation 0 f = 0 := by
  simp [expectation]

theorem expectation_const (μ : Weight α) (c : ℝ≥0∞) :
    expectation μ (fun _ => c) = mass μ * c := ENNReal.tsum_mul_right

theorem expectation_add (μ ν : Weight α) (f : α → ℝ≥0∞) :
    expectation (μ + ν) f = expectation μ f + expectation ν f := by
  simp only [expectation, Pi.add_apply, add_mul, ENNReal.tsum_add]

theorem expectation_smul (r : ℝ≥0∞) (μ : Weight α) (f : α → ℝ≥0∞) :
    expectation (r • μ) f = r * expectation μ f := by
  simp only [expectation, Pi.smul_apply, smul_eq_mul, mul_assoc, ENNReal.tsum_mul_left]

theorem expectation_add_cost (μ : Weight α) (f g : α → ℝ≥0∞) :
    expectation μ (fun a => f a + g a) = expectation μ f + expectation μ g := by
  simp only [expectation, mul_add, ENNReal.tsum_add]

theorem expectation_finset_sum_cost {ι : Type*} (s : Finset ι)
    (μ : Weight α) (f : ι → α → ℝ≥0∞) :
    expectation μ (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, expectation μ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expectation]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, expectation_add_cost, ih]

theorem expectation_bind (μ : Weight α) (k : α → Weight β) (f : β → ℝ≥0∞) :
    expectation (bind μ k) f = expectation μ (fun a => expectation (k a) f) := by
  simp only [expectation, bind, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right,
    mul_assoc]
  exact ENNReal.tsum_comm

theorem expectation_mono_on_support (μ : Weight α) {f g : α → ℝ≥0∞}
    (h : ∀ a ∈ support μ, f a ≤ g a) : expectation μ f ≤ expectation μ g := by
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases ha : μ a = 0
  · simp [ha]
  · exact mul_le_mul_right (h a ha) _

theorem expectation_congr_on_support (μ : Weight α) {f g : α → ℝ≥0∞}
    (h : ∀ a ∈ support μ, f a = g a) : expectation μ f = expectation μ g := by
  apply le_antisymm
  · exact expectation_mono_on_support μ (fun a ha => (h a ha).le)
  · exact expectation_mono_on_support μ (fun a ha => (h a ha).ge)

theorem expectation_le_of_bound {μ : Weight α} (hμ : IsProbability μ)
    {f : α → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ a ∈ support μ, f a ≤ c) :
    expectation μ f ≤ c := by
  calc
    expectation μ f ≤ expectation μ (fun _ => c) := expectation_mono_on_support μ h
    _ = c := by rw [expectation_const, hμ, one_mul]

end RelOL.Weight
