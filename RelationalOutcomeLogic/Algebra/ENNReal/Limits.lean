import RelationalOutcomeLogic.Algebra.ENNReal.Basic
import Mathlib.Order.FixedPoints

/-!
# Increasing limits of weights

Bind and mass preserve suprema of increasing sequences. The monotonicity hypotheses
are essential: arbitrary pointwise suprema can combine mass from incompatible inputs.
The boundary witnesses are in `Examples.Probability.AlgebraBoundaries`.
-/

namespace RelOL.Weight

open scoped ENNReal
open OmegaCompletePartialOrder

variable {α β : Type*}

/-- Nonnegative sums commute with increasing sequential limits. -/
theorem tsum_iSup_of_monotone (f : ℕ → Weight α) (hf : Monotone f) :
    (∑' a, ⨆ n, f n a) = ⨆ n, ∑' a, f n a := by
  simp only [ENNReal.tsum_eq_iSup_sum]
  simp_rw [ENNReal.finsetSum_iSup_of_monotone (fun a i j hij => hf hij a)]
  exact iSup_comm

/-- Mass is continuous along increasing sequences. -/
theorem mass_iSup (μ : ℕ → Weight α) (hμ : Monotone μ) :
    mass (⨆ n, μ n) = ⨆ n, mass (μ n) := by
  simp only [mass, iSup_apply]
  exact tsum_iSup_of_monotone μ hμ

/-- An increasing limit of subprobabilities remains a subprobability. -/
theorem IsSubprob.iSup {μ : ℕ → Weight α} (hμ : Monotone μ)
    (hmass : ∀ n, IsSubprob (μ n)) : IsSubprob (⨆ n, μ n) := by
  change mass (⨆ n, μ n) ≤ 1
  rw [mass_iSup μ hμ]
  exact iSup_le hmass

/-- Bind is continuous in its input weights. -/
theorem bind_iSup_left (μ : ℕ → Weight α) (hμ : Monotone μ) (k : α → Weight β) :
    bind (⨆ n, μ n) k = ⨆ n, bind (μ n) k := by
  funext b
  simp only [bind, iSup_apply, ENNReal.iSup_mul]
  exact tsum_iSup_of_monotone _ (fun i j hij a => mul_le_mul_left (hμ hij a) _)

/-- Bind is continuous in its continuation. -/
theorem bind_iSup_right (μ : Weight α) (k : ℕ → α → Weight β) (hk : Monotone k) :
    bind μ (⨆ n, k n) = ⨆ n, bind μ (k n) := by
  funext b
  simp only [bind, iSup_apply, ENNReal.mul_iSup]
  exact tsum_iSup_of_monotone _ (fun i j hij a => mul_le_mul_right (hk hij a b) _)

/-- When both inputs increase, one common index suffices for their joint limit. -/
theorem bind_iSup (μ : ℕ → Weight α) (hμ : Monotone μ)
    (k : ℕ → α → Weight β) (hk : Monotone k) :
    bind (⨆ n, μ n) (⨆ n, k n) = ⨆ n, bind (μ n) (k n) := by
  rw [bind_iSup_left μ hμ]
  simp_rw [bind_iSup_right _ k hk]
  apply le_antisymm
  · refine iSup_le fun i => iSup_le fun j => ?_
    exact le_iSup_of_le (max i j)
      (bind_mono (hμ (Nat.le_max_left i j)) (hk (Nat.le_max_right i j)))
  · exact iSup_le fun n => le_iSup_of_le n (le_iSup (fun j => bind (μ n) (k j)) n)

/-- The input-weight operation can be used with Mathlib's omega-continuous maps. -/
theorem bind_ωScottContinuous_left (k : α → Weight β) :
    ωScottContinuous (fun μ : Weight α => bind μ k) := by
  refine ωScottContinuous.of_monotone_map_ωSup ⟨fun _ _ h => bind_mono_left h k, ?_⟩
  intro c
  have hc : ωSup c = ⨆ n, c n :=
    le_antisymm (ωSup_le c _ fun n => le_iSup _ n) (iSup_le fun n => le_ωSup c n)
  rw [hc, bind_iSup_left c (OrderHomClass.mono c) k]
  exact le_antisymm (iSup_le fun n =>
    le_ωSup (c.map ⟨fun ν => bind ν k, fun _ _ h => bind_mono_left h k⟩) n)
    (ωSup_le _ _ fun n => le_iSup _ n)

/-- Continuity in the continuation is the key ingredient for loop fixed points. -/
theorem bind_ωScottContinuous_right (μ : Weight α) :
    ωScottContinuous (bind μ : (α → Weight β) → Weight β) := by
  refine ωScottContinuous.of_monotone_map_ωSup ⟨fun _ _ h => bind_mono_right μ h, ?_⟩
  intro c
  have hc : ωSup c = ⨆ n, c n :=
    le_antisymm (ωSup_le c _ fun n => le_iSup _ n) (iSup_le fun n => le_ωSup c n)
  rw [hc, bind_iSup_right μ c (OrderHomClass.mono c)]
  exact le_antisymm (iSup_le fun n =>
    le_ωSup (c.map ⟨bind μ, fun _ _ h => bind_mono_right μ h⟩) n)
    (ωSup_le _ _ fun n => le_iSup _ n)

end RelOL.Weight
