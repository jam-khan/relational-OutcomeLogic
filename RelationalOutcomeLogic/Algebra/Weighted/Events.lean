import RelationalOutcomeLogic.Algebra.Weighted.Coupling
import RelationalOutcomeLogic.Algebra.Scalar.Order
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Finite events in weighted outcomes

Finite event weights, their algebraic and order laws, and the necessary event bound
for an exact coupling. These facts do not depend on relational assertions or
refutation certificates.
-/

universe u v

namespace RelOL.Algebra.Weighted

variable {K : Type v} [Semiring K] [CompleteLattice K]
variable [SummationSemiring.{u} K] [OmegaSummationSemiring.{u} K]
variable {α β : Type u}

open SummationSemiring

/-- Weight of a finite event, using the scalar addition of the model. -/
noncomputable def eventMass (μ : Weight K α) (A : Finset α) : K := ∑ a ∈ A, μ a

omit [CompleteLattice K] [SummationSemiring.{u} K] [OmegaSummationSemiring.{u} K] in
@[simp] theorem eventMass_empty (μ : Weight K α) : eventMass μ ∅ = 0 := by
  simp [eventMass]

omit [CompleteLattice K] [SummationSemiring.{u} K] [OmegaSummationSemiring.{u} K] in
@[simp] theorem eventMass_singleton (μ : Weight K α) (a : α) : eventMass μ {a} = μ a := by
  simp [eventMass]

omit [CompleteLattice K] [SummationSemiring.{u} K] [OmegaSummationSemiring.{u} K] in
@[simp] theorem eventMass_zero (A : Finset α) : eventMass (0 : Weight K α) A = 0 := by
  simp [eventMass]

omit [CompleteLattice K] [OmegaSummationSemiring.{u} K] in
open Classical in
/-- Finite event sums agree with the chosen unrestricted summation. -/
theorem sum_indicator_finset (μ : Weight K α) (A : Finset α) :
    sum (fun a => if a ∈ A then μ a else 0) = eventMass μ A := by
  classical
  induction A using Finset.induction_on with
  | empty => simp only [Finset.notMem_empty, ite_false, sum_zero, eventMass_empty]
  | @insert a A ha ih =>
    calc
      _ = sum (fun x => (if x = a then μ a else 0) + (if x ∈ A then μ x else 0)) := by
        apply sum_congr
        intro x
        by_cases hxa : x = a
        · simp [hxa, ha]
        · simp [hxa]
      _ = μ a + eventMass μ A := by rw [sum_add, sum_single, ih]
      _ = _ := by simp [eventMass, ha]

omit [CompleteLattice K] [OmegaSummationSemiring.{u} K] in
theorem sum_eq_eventMass {μ : Weight K α} (A : Finset α)
    (h : ∀ a, a ∉ A → μ a = 0) : sum μ = eventMass μ A := by
  classical
  rw [← sum_indicator_finset]
  apply sum_congr
  intro a
  by_cases ha : a ∈ A <;> simp [ha, h a]

omit [CompleteLattice K] [OmegaSummationSemiring.{u} K] in
@[simp] theorem eventMass_univ [Fintype α] (μ : Weight K α) :
    eventMass μ Finset.univ = mass μ := by
  exact (sum_eq_eventMass Finset.univ fun a ha => (ha (Finset.mem_univ a)).elim).symm

theorem finset_sum_mono {f g : α → K} (A : Finset α)
    (h : ∀ a ∈ A, f a ≤ g a) : (∑ a ∈ A, f a) ≤ ∑ a ∈ A, g a := by
  classical
  induction A using Finset.induction_on with
  | empty => exact le_rfl
  | @insert a A ha ih =>
    simp only [Finset.sum_insert ha]
    exact OmegaSummationSemiring.add_mono (h a (Finset.mem_insert_self _ _))
      (ih fun x hx => h x (Finset.mem_insert_of_mem hx))

theorem eventMass_mono {μ ν : Weight K α} (h : μ ≤ ν) (A : Finset α) :
    eventMass μ A ≤ eventMass ν A := finset_sum_mono A fun a _ => h a

theorem eventMass_mono_set (μ : Weight K α) {A B : Finset α} (h : A ⊆ B) :
    eventMass μ A ≤ eventMass μ B := by
  classical
  rw [← sum_indicator_finset, ← sum_indicator_finset]
  apply OmegaSummationSemiring.sum_mono
  intro a
  by_cases ha : a ∈ A
  · simp only [ha, h ha, ite_true]
    exact le_rfl
  · simp only [ha, ite_false]
    rw [OmegaSummationSemiring.zero_eq_bot]
    exact bot_le

theorem eventMass_le_mass (μ : Weight K α) (A : Finset α) : eventMass μ A ≤ mass μ := by
  classical
  rw [← sum_indicator_finset]
  apply OmegaSummationSemiring.sum_mono
  intro a
  by_cases ha : a ∈ A
  · simp only [ha, ite_true]
    exact le_rfl
  · simp only [ha, ite_false]
    rw [OmegaSummationSemiring.zero_eq_bot]
    exact bot_le

omit [CompleteLattice K] [SummationSemiring.{u} K] [OmegaSummationSemiring.{u} K] in
theorem eventMass_add (μ ν : Weight K α) (A : Finset α) :
    eventMass (μ + ν) A = eventMass μ A + eventMass ν A := Finset.sum_add_distrib

omit [CompleteLattice K] [SummationSemiring.{u} K] [OmegaSummationSemiring.{u} K] in
theorem eventMass_scale (r : K) (μ : Weight K α) (A : Finset α) :
    eventMass (scale r μ) A = r * eventMass μ A := by
  simp only [eventMass, scale, Finset.mul_sum]

/-- A finite event can only couple into an event with at least as much weight. -/
theorem IsCoupling.eventMass_le {R : α → β → Prop} {μ : Weight K α} {ν : Weight K β}
    {J : Weight K (α × β)} (h : IsCoupling R μ ν J) (A : Finset α) (B : Finset β)
    (himage : ∀ a ∈ A, ∀ b, R a b → b ∈ B) : eventMass μ A ≤ eventMass ν B := by
  classical
  change (∑ a ∈ A, μ a) ≤ ∑ b ∈ B, ν b
  calc
    ∑ a ∈ A, μ a = ∑ a ∈ A, ∑ b ∈ B, J (a, b) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [← h.margL_eq]
      apply sum_eq_eventMass B
      intro b hb
      by_contra hj
      exact hb (himage a ha b (h.supported a b hj))
    _ = ∑ b ∈ B, ∑ a ∈ A, J (a, b) := Finset.sum_comm
    _ ≤ ∑ b ∈ B, sum (fun a => J (a, b)) :=
      finset_sum_mono B fun _ _ => eventMass_le_mass _ A
    _ = ∑ b ∈ B, ν b := Finset.sum_congr rfl fun b _ => congrFun h.margR_eq b

theorem Coupled.eventMass_le {R : α → β → Prop} {μ : Weight K α} {ν : Weight K β}
    (h : Coupled R μ ν) (A : Finset α) (B : Finset β)
    (himage : ∀ a ∈ A, ∀ b, R a b → b ∈ B) : eventMass μ A ≤ eventMass ν B := by
  obtain ⟨J, hJ⟩ := h
  exact hJ.eventMass_le A B himage

end RelOL.Algebra.Weighted
