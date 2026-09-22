import RelationalOutcomeLogic.Algebra.Scalar.Order
import Mathlib.Order.PropInstances
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Boolean reachability weights

The semiring operations are disjunction and conjunction. This dedicated type avoids
introducing arithmetic instances on `Prop` or confusing reachability with XOR.
-/

namespace RelOL.Algebra

/-- Propositions regarded as Boolean reachability weights. -/
def Reachability : Type := Prop

namespace Reachability

/-- Read a reachability weight as a proposition. -/
def holds (p : Reachability) : Prop := p

instance : Zero Reachability := ⟨False⟩
instance : One Reachability := ⟨True⟩
instance : Add Reachability := ⟨Or⟩
instance : Mul Reachability := ⟨And⟩

instance : CommSemiring Reachability where
  add_assoc _ _ _ := propext or_assoc
  zero_add p := false_or p
  add_zero p := or_false p
  add_comm _ _ := propext or_comm
  nsmul := nsmulRec
  mul_assoc _ _ _ := propext and_assoc
  one_mul p := true_and p
  mul_one p := and_true p
  mul_comm _ _ := propext and_comm
  left_distrib _ _ _ := propext and_or_left
  right_distrib _ _ _ := propext or_and_right
  zero_mul p := false_and p
  mul_zero p := and_false p
  natCast n := n ≠ 0
  natCast_zero := by change (0 ≠ 0) = False; simp
  natCast_succ n := by change (n + 1 ≠ 0) = ((n ≠ 0) ∨ True); simp

instance : CompleteLattice Reachability :=
  inferInstanceAs (CompleteLattice Prop)

instance : Nontrivial Reachability := inferInstanceAs (Nontrivial Prop)

instance : NoZeroDivisors Reachability where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} h := by
    classical
    change (holds a ∧ holds b) = False at h
    have hn : ¬ (holds a ∧ holds b) := fun hab => Eq.mp h hab
    rcases not_and_or.mp hn with ha | hb
    · exact Or.inl (propext ⟨ha, False.elim⟩)
    · exact Or.inr (propext ⟨hb, False.elim⟩)

@[simp] theorem holds_zero : holds (0 : Reachability) ↔ False := Iff.rfl
@[simp] theorem holds_one : holds (1 : Reachability) ↔ True := Iff.rfl
@[simp] theorem holds_add (p q : Reachability) : holds (p + q) ↔ holds p ∨ holds q := Iff.rfl
@[simp] theorem holds_mul (p q : Reachability) : holds (p * q) ↔ holds p ∧ holds q := Iff.rfl
@[simp] theorem holds_iSup {ι : Sort*} (f : ι → Reachability) :
    holds (⨆ i, f i) ↔ ∃ i, holds (f i) := by
  change (⨆ i, (f i : Prop)) ↔ ∃ i, (f i : Prop)
  exact Iff.of_eq (iSup_Prop_eq (p := fun i => (f i : Prop)))

noncomputable instance : SummationSemiring Reachability where
  sum f := ∃ i, holds (f i)
  sum_zero := by intro ι; change (∃ _ : ι, False) = False; simp
  sum_add f g := by
    change (∃ i, holds (f i) ∨ holds (g i)) = ((∃ i, holds (f i)) ∨ ∃ i, holds (g i))
    simp only [exists_or]
  sum_single j x := by
    classical
    change (∃ i, holds (if i = j then x else 0)) = x
    apply propext
    constructor
    · rintro ⟨i, hi⟩
      by_cases h : i = j
      · simpa [h, holds] using hi
      · simp [h, holds, OfNat.ofNat, Zero.zero] at hi
    · intro hx
      exact ⟨j, by simpa [holds] using hx⟩
  sum_comm f := propext ⟨fun ⟨i, j, h⟩ => ⟨j, i, h⟩, fun ⟨j, i, h⟩ => ⟨i, j, h⟩⟩
  sum_prod f := propext ⟨fun ⟨⟨i, j⟩, h⟩ => ⟨i, j, h⟩, fun ⟨i, j, h⟩ => ⟨(i, j), h⟩⟩
  mul_sum r f := by
    change (∃ i, holds r ∧ holds (f i)) = (holds r ∧ ∃ i, holds (f i))
    simp only [exists_and_left]
  sum_mul f r := by
    change (∃ i, holds (f i) ∧ holds r) = ((∃ i, holds (f i)) ∧ holds r)
    simp only [exists_and_right]

instance : PositiveSummation Reachability where
  sum_eq_zero f := by
    change (∃ i, holds (f i)) = False ↔ ∀ i, (f i : Prop) = False
    constructor
    · intro h i
      apply propext
      exact ⟨fun hi => (Eq.mp h ⟨i, hi⟩).elim, False.elim⟩
    · intro h
      apply propext
      exact ⟨fun ⟨i, hi⟩ => Eq.mp (h i) hi, False.elim⟩

instance : OmegaSummationSemiring Reachability where
  zero_eq_bot := rfl
  add_mono h₁ h₂ := fun h => h.elim (fun h => Or.inl (h₁ h)) (fun h => Or.inr (h₂ h))
  mul_mono h₁ h₂ := fun h => ⟨h₁ h.1, h₂ h.2⟩
  sum_mono h := fun ⟨i, hi⟩ => ⟨i, h i hi⟩
  sum_iSup f _ := by
    apply propext
    change (∃ i, holds (⨆ n, f n i)) ↔ holds (⨆ n, SummationSemiring.sum (f n))
    simp only [holds_iSup]
    exact ⟨fun ⟨i, n, h⟩ => ⟨n, i, h⟩, fun ⟨n, i, h⟩ => ⟨i, n, h⟩⟩
  mul_iSup_left a f _ := by
    apply propext
    change holds (a * ⨆ n, f n) ↔ holds (⨆ n, a * f n)
    simp only [holds_mul, holds_iSup, exists_and_left]
  mul_iSup_right f _ a := by
    apply propext
    change holds ((⨆ n, f n) * a) ↔ holds (⨆ n, f n * a)
    simp only [holds_mul, holds_iSup, exists_and_right]

theorem holds_eq_iff (p q : Reachability) : p = q ↔ (holds p ↔ holds q) :=
  ⟨fun h => h ▸ Iff.rfl, propext⟩

theorem add_eq_sup (p q : Reachability) : p + q = p ⊔ q := rfl

theorem finset_sum_eq_iSup {ι : Type*} (s : Finset ι) (f : ι → Reachability) :
    ∑ i ∈ s, f i = ⨆ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.notMem_empty, iSup_false, iSup_bot]; rfl
  | @insert i s hi ih => simp only [Finset.sum_insert hi, Finset.iSup_insert, ih, add_eq_sup]

/-- Boolean summation agrees with the finite-subsum definition in Outcome Logic. -/
theorem sum_eq_iSup_finset {ι : Type*} (f : ι → Reachability) :
    SummationSemiring.sum f = ⨆ s : Finset ι, ∑ i ∈ s, f i := by
  simp_rw [finset_sum_eq_iSup]
  rw [← iSup_eq_iSup_finset]
  apply propext
  exact (holds_iSup f).symm

/-- The order is exactly the semiring's natural additive order. -/
theorem le_iff_exists_add (p q : Reachability) : p ≤ q ↔ ∃ r, p + r = q := by
  constructor
  · intro h
    exact ⟨q, sup_eq_right.mpr h⟩
  · rintro ⟨r, hr⟩
    rw [← hr, add_eq_sup]
    exact le_sup_left

end Reachability
end RelOL.Algebra
