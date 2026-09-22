import RelationalOutcomeLogic.Algebra.ENNReal.Basic

/-!
# Reordering and discarding independent probability samples

These laws expose the algebra needed to move a speculative draft sample past an
independent verification step. Discarding a sample requires mass one; independence
is explicit in the types of the two kernels in `bind_comm`.
-/

namespace RelOL.Weight

open scoped ENNReal

variable {α β γ : Type*}

theorem bind_comm (μ : Weight α) (ν : Weight β) (f : α → β → Weight γ) :
    bind μ (fun a => bind ν (f a)) = bind ν (fun b => bind μ (fun a => f a b)) := by
  funext c
  simp only [bind, ← ENNReal.tsum_mul_left, ← mul_assoc]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro b
  apply tsum_congr
  intro a
  rw [mul_comm (μ a) (ν b)]

/-- A sampled value that is never used can be discarded when its weight has mass one. -/
theorem bind_const_of_isProbability (μ : Weight α) (hμ : IsProbability μ)
    (ν : Weight β) : bind μ (fun _ => ν) = ν := by
  funext b
  simp only [bind, ENNReal.tsum_mul_right]
  change mass μ * ν b = ν b
  rw [hμ, one_mul]

end RelOL.Weight
