import RelationalOutcomeLogic.Algebra.Scalar.Order
import Mathlib.Algebra.Tropical.Basic
import Mathlib.Data.ENNReal.Operations
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Tropical minimum-cost weights

Choice selects the cheaper cost; sequencing adds costs. The natural semiring
order reverses the numerical order, so increasing semantic information lowers
the numerical minimum cost. Semiring zero is infinite cost; one is cost zero.
-/

open scoped ENNReal

namespace RelOL.Algebra

/-- Nonnegative tropical costs, with their natural (reverse numerical) order. -/
def Cost : Type := Tropical ℝ≥0∞

namespace Cost

/-- The numerical cost represented by a tropical weight. -/
def value (c : Cost) : ℝ≥0∞ := Tropical.untrop c

/-- Regard a nonnegative extended number as a cost. -/
def ofValue (c : ℝ≥0∞) : Cost := Tropical.trop c

noncomputable instance : CommSemiring Cost := inferInstanceAs (CommSemiring (Tropical ℝ≥0∞))

private def orderEquiv : Cost ≃ ℝ≥0∞ᵒᵈ where
  toFun := value
  invFun := ofValue
  left_inv := Tropical.trop_untrop
  right_inv := Tropical.untrop_trop

noncomputable instance : CompleteLattice Cost := orderEquiv.completeLattice

private def orderIso : Cost ≃o ℝ≥0∞ᵒᵈ where
  toEquiv := orderEquiv
  map_rel_iff' := Iff.rfl

@[ext] theorem ext {a b : Cost} (h : value a = value b) : a = b := Tropical.untrop_injective h

@[simp] theorem value_ofValue (c : ℝ≥0∞) : value (ofValue c) = c := rfl
@[simp] theorem ofValue_value (c : Cost) : ofValue (value c) = c := rfl
@[simp] theorem value_zero : value (0 : Cost) = ⊤ := rfl
@[simp] theorem value_one : value (1 : Cost) = 0 := rfl
@[simp] theorem value_add (a b : Cost) : value (a + b) = min (value a) (value b) := rfl
@[simp] theorem value_mul (a b : Cost) : value (a * b) = value a + value b := rfl
@[simp] theorem le_iff (a b : Cost) : a ≤ b ↔ value b ≤ value a := Iff.rfl
@[simp] theorem lt_iff (a b : Cost) : a < b ↔ value b < value a := Iff.rfl

theorem ne_zero_iff (c : Cost) : c ≠ 0 ↔ value c ≠ ⊤ :=
  ⟨fun h hz => h (ext hz), fun h hz => h (congrArg value hz)⟩

instance : NoZeroDivisors Cost where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} h := by
    have he : value a + value b = ⊤ := congrArg value h
    rcases ENNReal.add_eq_top.mp he with ha | hb
    · exact Or.inl (ext ha)
    · exact Or.inr (ext hb)

@[simp] theorem value_iSup {ι : Sort*} (f : ι → Cost) :
    value (⨆ i, f i) = ⨅ i, value (f i) := orderIso.map_iSup f

noncomputable instance : SummationSemiring Cost where
  sum f := ofValue (⨅ i, value (f i))
  sum_zero := by intro ι; apply ext; simp
  sum_add f g := by
    apply ext
    change (⨅ i, min (value (f i)) (value (g i))) = min (⨅ i, value (f i)) (⨅ i, value (g i))
    exact iInf_inf_eq
  sum_single j x := by
    classical
    apply ext
    change (⨅ i, value (if i = j then x else 0)) = value x
    apply le_antisymm
    · exact (iInf_le _ j).trans_eq (by simp)
    · apply le_iInf
      intro i
      by_cases h : i = j <;> simp [h]
  sum_comm f := by apply ext; exact iInf_comm
  sum_prod f := by apply ext; exact iInf_prod
  mul_sum r f := by apply ext; exact ENNReal.add_iInf.symm
  sum_mul f r := by apply ext; exact ENNReal.iInf_add.symm

@[simp] theorem value_sum {ι : Type*} (f : ι → Cost) :
    value (SummationSemiring.sum f) = ⨅ i, value (f i) := rfl

instance : PositiveSummation Cost where
  sum_eq_zero f := by
    constructor
    · intro h i
      apply ext
      have he := congrArg value h
      simp only [value_sum, value_zero, iInf_eq_top] at he
      exact he i
    · intro h
      apply ext
      simp only [value_sum, value_zero, iInf_eq_top]
      intro i
      rw [h i, value_zero]

instance : OmegaSummationSemiring Cost where
  zero_eq_bot := rfl
  add_mono {a b c d} h₁ h₂ := by
    change min (value b) (value d) ≤ min (value a) (value c)
    exact min_le_min h₁ h₂
  mul_mono {a b c d} h₁ h₂ := by
    change value b + value d ≤ value a + value c
    exact add_le_add h₁ h₂
  sum_mono {ι} {f g} h := by
    change (⨅ i, value (g i)) ≤ ⨅ i, value (f i)
    exact iInf_mono fun i => h i
  sum_iSup f _ := by
    apply ext
    simp only [value_sum, value_iSup]
    exact iInf_comm
  mul_iSup_left a f _ := by
    apply ext
    simp only [value_mul, value_iSup]
    exact ENNReal.add_iInf
  mul_iSup_right f _ a := by
    apply ext
    simp only [value_mul, value_iSup]
    exact ENNReal.iInf_add

theorem add_eq_sup (a b : Cost) : a + b = a ⊔ b := rfl

theorem finset_sum_eq_iSup {ι : Type*} (s : Finset ι) (f : ι → Cost) :
    ∑ i ∈ s, f i = ⨆ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.notMem_empty, iSup_false, iSup_bot]; rfl
  | @insert i s hi ih => simp only [Finset.sum_insert hi, Finset.iSup_insert, ih, add_eq_sup]

/-- Minimum-cost summation agrees with the canonical finite-subsum supremum
in the natural, reverse numerical order. -/
theorem sum_eq_iSup_finset {ι : Type*} (f : ι → Cost) :
    SummationSemiring.sum f = ⨆ s : Finset ι, ∑ i ∈ s, f i := by
  simp_rw [finset_sum_eq_iSup]
  rw [← iSup_eq_iSup_finset]
  apply ext
  simp

/-- The reverse numerical order is the semiring's natural additive order. -/
theorem le_iff_exists_add (a b : Cost) : a ≤ b ↔ ∃ c, a + c = b := by
  constructor
  · intro h
    exact ⟨b, (add_eq_sup a b).trans (sup_eq_right.mpr h)⟩
  · rintro ⟨c, hc⟩
    rw [← hc, add_eq_sup]
    exact le_sup_left

end Cost
end RelOL.Algebra
