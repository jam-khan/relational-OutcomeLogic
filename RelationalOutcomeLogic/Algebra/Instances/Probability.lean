import RelationalOutcomeLogic.Algebra.OrderedScalar
import RelationalOutcomeLogic.Algebra.WeightOrder

/-!
# Extended nonnegative weights

The total ambient semiring is `ℝ≥0∞`. Probability and subprobability are mass
bounds on weights, not claims that unrestricted addition preserves probability.
-/

open scoped ENNReal

namespace RelOL.Algebra

noncomputable instance : SummationSemiring ℝ≥0∞ where
  sum f := ∑' i, f i
  sum_zero := tsum_zero
  sum_add _ _ := ENNReal.tsum_add
  sum_single j x := by
    classical
    simp
  sum_comm _ := ENNReal.tsum_comm
  sum_prod _ := ENNReal.tsum_prod'
  mul_sum _ _ := ENNReal.tsum_mul_left
  sum_mul _ _ := ENNReal.tsum_mul_right

instance : PositiveSummation ℝ≥0∞ where
  sum_eq_zero _ := ENNReal.tsum_eq_zero

instance : OmegaSummationSemiring ℝ≥0∞ where
  zero_eq_bot := rfl
  add_mono := add_le_add
  mul_mono := fun h₁ h₂ => mul_le_mul' h₁ h₂
  sum_mono := ENNReal.tsum_le_tsum
  sum_iSup := RelOL.Weight.tsum_iSup_of_monotone
  mul_iSup_left a f _ := ENNReal.mul_iSup a f
  mul_iSup_right f _ a := ENNReal.iSup_mul f a

/-- The chosen summation is the finite-subsum supremum used by Outcome Logic. -/
theorem ennreal_sum_eq_iSup_finset {ι : Type*} (f : ι → ℝ≥0∞) :
    SummationSemiring.sum f = ⨆ s : Finset ι, ∑ i ∈ s, f i :=
  ENNReal.tsum_eq_iSup_sum

end RelOL.Algebra
