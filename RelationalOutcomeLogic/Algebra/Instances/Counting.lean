import RelationalOutcomeLogic.Algebra.OrderedScalar
import Mathlib.Topology.Instances.ENat
import Mathlib.Data.ENat.BigOperators
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Order.T5

/-!
# Extended natural trace counts

Each outcome records how many terminating traces reach it. Infinite counts are
permitted, so arbitrary branching and increasing loop limits remain defined.
-/

namespace RelOL.Algebra

private theorem enat_hasSum {ι : Type*} (f : ι → ℕ∞) :
    HasSum f (⨆ s : Finset ι, ∑ i ∈ s, f i) :=
  tendsto_atTop_iSup fun _ _ => Finset.sum_le_sum_of_subset

theorem enat_summable {ι : Type*} (f : ι → ℕ∞) : Summable f :=
  ⟨_, enat_hasSum f⟩

noncomputable instance : SummationSemiring ℕ∞ where
  sum f := ∑' i, f i
  sum_zero := tsum_zero
  sum_add f g := (enat_summable f).tsum_add (enat_summable g)
  sum_single j x := by
    classical
    simp
  sum_comm f := (enat_summable _).tsum_comm' (fun _ => enat_summable _) (fun _ => enat_summable _)
  sum_prod f := (enat_summable f).tsum_prod' (fun _ => enat_summable _)
  mul_sum r f := (enat_summable f).tsum_mul_left r
  sum_mul f r := (enat_summable f).tsum_mul_right r

instance : PositiveSummation ℕ∞ where
  sum_eq_zero f := (enat_summable f).tsum_eq_zero_iff

/-- Trace-count summation has the canonical finite-subsum meaning. -/
theorem enat_sum_eq_iSup_finset {ι : Type*} (f : ι → ℕ∞) :
    SummationSemiring.sum f = ⨆ s : Finset ι, ∑ i ∈ s, f i :=
  (enat_hasSum f).tsum_eq

instance : OmegaSummationSemiring ℕ∞ where
  zero_eq_bot := rfl
  add_mono := add_le_add
  mul_mono := fun h₁ h₂ => mul_le_mul' h₁ h₂
  sum_mono h := (enat_summable _).tsum_le_tsum h (enat_summable _)
  sum_iSup f hf := by
    simp only [enat_sum_eq_iSup_finset]
    simp_rw [ENat.sum_iSup_of_monotone (fun i a b hab => hf hab i)]
    exact iSup_comm
  mul_iSup_left a f _ := ENat.mul_iSup a f
  mul_iSup_right f _ a := ENat.iSup_mul f a

end RelOL.Algebra
