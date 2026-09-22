import RelationalOutcomeLogic.Algebra.OrderedScalar
import Mathlib.Computability.Language
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite-word trace languages

Weights are sets of finite words, choice is union, and sequencing concatenates
words in execution order. This provides a noncommutative scalar instance.
Unlike the TOPLAS paper's language model, this instance does not include infinite
words: it records traces of terminating executions only.
-/

namespace RelOL.Algebra

instance {Γ : Type*} : NoZeroDivisors (Language Γ) where
  eq_zero_or_eq_zero_of_mul_eq_zero h := Set.image2_eq_empty_iff.mp h

noncomputable instance {Γ : Type*} : SummationSemiring (Language Γ) where
  sum f := ⨆ i, f i
  sum_zero := by intro ι; exact iSup_bot
  sum_add f g := iSup_sup_eq
  sum_single j x := by
    classical
    apply le_antisymm
    · apply iSup_le
      intro i
      by_cases hi : i = j
      · simp [hi]
      · simp only [hi, ite_false]
        exact bot_le
    · exact le_iSup_of_le j (by simp)
  sum_comm _ := iSup_comm
  sum_prod _ := iSup_prod
  mul_sum r f := (Language.mul_iSup f r).symm
  sum_mul f r := (Language.iSup_mul f r).symm

instance {Γ : Type*} : PositiveSummation (Language Γ) where
  sum_eq_zero _ := iSup_eq_bot

instance {Γ : Type*} : OmegaSummationSemiring (Language Γ) where
  zero_eq_bot := rfl
  add_mono := sup_le_sup
  mul_mono h₁ h₂ := mul_le_mul' h₁ h₂
  sum_mono := iSup_mono
  sum_iSup _ _ := iSup_comm
  mul_iSup_left r f _ := Language.mul_iSup f r
  mul_iSup_right f _ r := Language.iSup_mul f r

namespace TraceLanguage

variable {Γ : Type*}

theorem add_eq_sup (l m : Language Γ) : l + m = l ⊔ m := rfl

theorem finset_sum_eq_iSup {ι : Type*} (s : Finset ι) (f : ι → Language Γ) :
    ∑ i ∈ s, f i = ⨆ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.notMem_empty, iSup_false, iSup_bot]; rfl
  | @insert i s hi ih => simp only [Finset.sum_insert hi, Finset.iSup_insert, ih, add_eq_sup]

/-- Language union is the canonical finite-subsum supremum. -/
theorem sum_eq_iSup_finset {ι : Type*} (f : ι → Language Γ) :
    SummationSemiring.sum f = ⨆ s : Finset ι, ∑ i ∈ s, f i := by
  simp_rw [finset_sum_eq_iSup]
  exact iSup_eq_iSup_finset f

/-- Language inclusion is the natural additive order. -/
theorem le_iff_exists_add (l m : Language Γ) : l ≤ m ↔ ∃ n, l + n = m := by
  constructor
  · intro h
    exact ⟨m, (add_eq_sup l m).trans (sup_eq_right.mpr h)⟩
  · rintro ⟨n, hn⟩
    rw [← hn, add_eq_sup]
    exact le_sup_left

end TraceLanguage
end RelOL.Algebra
