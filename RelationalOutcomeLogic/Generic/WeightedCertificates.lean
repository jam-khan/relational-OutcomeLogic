import RelationalOutcomeLogic.Algebra.WeightedOrder
import RelationalOutcomeLogic.Generic.WeightedLogic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Quantitative refutation over ordered summation semirings

The weights of finite events provide necessary bounds for an exact coupling.
A strict deficit refutes the coupling, and a concrete input lifts the certificate
to a refutation of the common relational judgment. The argument uses the chosen
semiring order, so for tropical costs its inequalities reverse numerical cost.
No normalization, subtraction, division, or commutative multiplication is needed.
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

namespace RelOL.Generic

open Algebra Algebra.Weighted

variable {K : Type v} [Semiring K] [CompleteLattice K]
variable [SummationSemiring.{u} K] [OmegaSummationSemiring.{u} K]
variable {α β γ δ : Type u}

/-- An imbalance of finite event weights ruling out every exact joint witness. -/
structure MassDeficitCert (R : α → β → Prop) (μ : Weighted.Weight K α)
    (ν : Weighted.Weight K β) where
  left : Finset α
  right : Finset β
  cover : ∀ a ∈ left, ∀ b, R a b → b ∈ right
  deficit : eventMass ν right < eventMass μ left

theorem MassDeficitCert.refutes {R : α → β → Prop}
    {μ : Weighted.Weight K α} {ν : Weighted.Weight K β}
    (C : MassDeficitCert R μ ν) : ¬ Weighted.Coupled R μ ν := by
  intro h
  exact (not_lt_of_ge (h.eventMass_le C.left C.right C.cover)) C.deficit

theorem no_massDeficitCert_of_coupled {R : α → β → Prop}
    {μ : Weighted.Weight K α} {ν : Weighted.Weight K β}
    (h : Weighted.Coupled R μ ν) : ¬ Nonempty (MassDeficitCert R μ ν) := by
  rintro ⟨C⟩
  exact C.refutes h

def MassDeficitCert.of_bounds {R : α → β → Prop}
    {μ : Weighted.Weight K α} {ν : Weighted.Weight K β}
    (A : Finset α) (B : Finset β) (hcover : ∀ a ∈ A, ∀ b, R a b → b ∈ B)
    {lower upper : K} (hleft : lower ≤ eventMass μ A)
    (hright : eventMass ν B ≤ upper) (hgap : upper < lower) : MassDeficitCert R μ ν where
  left := A
  right := B
  cover := hcover
  deficit := hright.trans_lt (hgap.trans_le hleft)

/-- A mismatch at one observation suffices to refute exact equality coupling. -/
def MassDeficitCert.singletonEq {μ ν : Weighted.Weight K α} (a : α) (h : ν a < μ a) :
    MassDeficitCert Eq μ ν where
  left := {a}
  right := {a}
  cover := by
    intro x hx y hxy
    simpa only [Finset.mem_singleton, ← hxy] using hx
  deficit := by simpa only [eventMass_singleton] using h

theorem MassDeficitCert.refutes_post {R : α → β → Prop}
    {μ : Weighted.Weight K α} {ν : Weighted.Weight K β}
    (C : MassDeficitCert R μ ν) {Q : RAssn (Weighted.Weight K) α β}
    (hQ : entail Q (couple R)) : ¬ Q μ ν := fun h => C.refutes (hQ μ ν h)

/-- A deficit for the union relation rules out every additive split into its pieces. -/
theorem MassDeficitCert.refutes_oplus {R S : α → β → Prop}
    {μ : Weighted.Weight K α} {ν : Weighted.Weight K β}
    (C : MassDeficitCert (fun a b => R a b ∨ S a b) μ ν) :
    ¬ oplus (couple R) (couple S) μ ν := by
  rintro ⟨μ₁, μ₂, ν₁, ν₂, rfl, rfl, h₁, h₂⟩
  exact C.refutes (Weighted.Coupled.add
    (Weighted.Coupled.mono h₁ fun _ _ h => Or.inl h)
    (Weighted.Coupled.mono h₂ fun _ _ h => Or.inr h))

/-- An imbalance in actual outputs at a concrete pair of initial states. -/
structure BugCert (F : Weighted.Weight K α → Weighted.Weight K γ)
    (G : Weighted.Weight K β → Weighted.Weight K δ) (R : γ → δ → Prop) where
  s₀ : α
  s₀' : β
  deficit : MassDeficitCert R (F (Weighted.pure s₀)) (G (Weighted.pure s₀'))

theorem BugCert.refutes {F : Weighted.Weight K α → Weighted.Weight K γ}
    {G : Weighted.Weight K β → Weighted.Weight K δ} {R : γ → δ → Prop}
    (C : BugCert F G R) {P : RAssn (Weighted.Weight K) α β}
    (hP : P (Weighted.pure C.s₀) (Weighted.pure C.s₀')) :
    ¬ quadSem F G P (couple R) := by
  intro h
  exact C.deficit.refutes (h _ _ hP)

theorem BugCert.refutes_of_entails {F : Weighted.Weight K α → Weighted.Weight K γ}
    {G : Weighted.Weight K β → Weighted.Weight K δ} {R : γ → δ → Prop}
    (C : BugCert F G R) {P : RAssn (Weighted.Weight K) α β}
    {Q : RAssn (Weighted.Weight K) γ δ}
    (hP : P (Weighted.pure C.s₀) (Weighted.pure C.s₀')) (hQ : entail Q (couple R)) :
    ¬ quadSem F G P Q := by
  intro h
  exact C.deficit.refutes_post hQ (h _ _ hP)

end RelOL.Generic
