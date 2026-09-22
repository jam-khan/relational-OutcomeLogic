import RelationalOutcomeLogic.Generic.Rules
import RelationalOutcomeLogic.Generic.Loops.Semantics
import RelationalOutcomeLogic.Generic.Coupling
import RelationalOutcomeLogic.Algebra.Weighted.Iteration
import RelationalOutcomeLogic.Algebra.Weighted.Coupling
import RelationalOutcomeLogic.Algebra.Instances.Probability
import RelationalOutcomeLogic.Prob.Semantics.Commands
import RelationalOutcomeLogic.Prob.Coupling.Basic
import RelationalOutcomeLogic.Subsumption.PRHL.Embedding

/-! # Probability semantics as an instance of the shared outcome logic

The instances and compatibility theorems identify the concrete API with the
shared assertions, execution, and full loop semantics.
-/

universe u

namespace RelOL

noncomputable instance weightOutcomeModel : OutcomeModel (Weight : Type u → Type u) where
  empty := 0
  add := (· + ·)
  pure := Weight.pure
  bind := Weight.bind
  add_assoc := add_assoc
  add_comm := add_comm
  empty_add := zero_add
  add_empty := add_zero
  pure_bind := Weight.pure_bind
  bind_pure := Weight.bind_pure
  bind_assoc := Weight.bind_assoc
  empty_bind := Weight.zero_bind
  bind_empty := Weight.bind_zero
  add_bind := Weight.add_bind
  bind_add := Weight.bind_add

instance weightIterationModel : IterationModel (Weight : Type u → Type u) where
  empty_eq_bot := rfl
  bind_mono := Weight.bind_mono
  bind_iSup_right := Weight.bind_iSup_right

namespace Generic

open scoped ENNReal

variable {α β γ δ : Type u}

@[simp] theorem weight_empty_eq : (OutcomeModel.empty : Weight α) = 0 := rfl
@[simp] theorem weight_add_eq (x y : Weight α) : OutcomeModel.add x y = x + y := rfl
@[simp] theorem weight_pure_eq (a : α) :
    (OutcomeModel.pure a : Weight α) = Weight.pure a := rfl
@[simp] theorem weight_bind_eq (x : Weight α) (k : α → Weight β) :
    OutcomeModel.bind x k = Weight.bind x k := rfl

theorem weight_oplus_eq (P Q : Prob.RAssn α β) :
    oplus (M := Weight) P Q = Prob.oplus P Q := rfl
theorem weight_emp_eq : (emp : RAssn Weight α β) = Prob.emp := rfl
theorem weight_exactly_eq (x : Weight α) (y : Weight β) :
    exactly x y = Prob.exactly x y := rfl
theorem weight_quadSem_eq (F : Weight α → Weight γ) (G : Weight β → Weight δ)
    (P : Prob.RAssn α β) (Q : Prob.RAssn γ δ) :
    quadSem F G P Q = Prob.quadSem F G P Q := rfl
theorem weight_quad_eq (P : Prob.RAssn α β) (Q : Prob.RAssn α β)
    (c : Prob.Cmd α) (d : Prob.Cmd β) :
    quad P (Prob.sem c) (Prob.sem d) Q = Prob.quad P c d Q := rfl

/-- Existing probabilistic judgments inherit exactly the same proof. -/
theorem weight_quad_split {P P' Q Q' : Prob.RAssn α β}
    {c : Prob.Cmd α} {d : Prob.Cmd β}
    (h : Prob.quad P c d Q) (h' : Prob.quad P' c d Q') :
    Prob.quad (Prob.oplus P P') c d (Prob.oplus Q Q') :=
  quad_split (M := Weight) h h'

@[simp] theorem ennreal_pure_eq (a : α) :
    (Algebra.Weighted.pure a : Algebra.Weighted.Weight ℝ≥0∞ α) = Weight.pure a := rfl

@[simp] theorem ennreal_bind_eq (μ : Weight α) (k : α → Weight β) :
    Algebra.Weighted.bind μ k = Weight.bind μ k := rfl

@[simp] theorem ennreal_mass_eq (μ : Weight α) : Algebra.Weighted.mass μ = Weight.mass μ := rfl

theorem ennreal_isCoupling_iff (R : α → β → Prop) (μ : Weight α) (ν : Weight β)
    (J : Weight (α × β)) :
    Algebra.Weighted.IsCoupling R μ ν J ↔ Prob.IsCoupling R μ ν J := by
  constructor <;> intro h <;> exact ⟨h.margL_eq, h.margR_eq, h.supported⟩

theorem ennreal_coupled_iff (R : α → β → Prop) (μ : Weight α) (ν : Weight β) :
    Algebra.Weighted.Coupled R μ ν ↔ Prob.Coupled R μ ν := by
  simp only [Algebra.Weighted.Coupled, Prob.Coupled, ennreal_isCoupling_iff]

theorem ennreal_couple_eq (R : α → β → Prop) :
    Generic.couple (K := ℝ≥0∞) R = Prob.couple R := by
  funext μ ν
  exact propext (ennreal_coupled_iff R μ ν)

theorem ennreal_prhl_iff (R : α → β → Prop) (k : α → Weight γ) (l : β → Weight δ)
    (S : γ → δ → Prop) : Generic.prhl R k l S ↔ Prob.prhlSem R k l S := by
  simp only [Generic.prhl, Prob.prhlSem, ennreal_coupled_iff]

theorem ennreal_prhl_commands_iff (R S : α → β → Prop) (c : Prob.Cmd α) (d : Prob.Cmd β) :
    Generic.prhl R (Prob.sem c) (Prob.sem d) S ↔ Prob.prhl R c d S :=
  ennreal_prhl_iff R (Prob.sem c) (Prob.sem d) S

theorem weight_loopIter_eq (g : α → Prop) (k : α → Weight α) (n : ℕ) :
    Generic.loopIter g k n = Prob.loopIter g k n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext s
      simp only [Generic.loopIter, Prob.loopIter, ih, weight_bind_eq, weight_pure_eq]

theorem weight_loopSem_eq (g : α → Prop) (k : α → Weight α) :
    Generic.loopSem g k = Prob.loopSem g k := by
  funext s
  simp only [Generic.loopSem, Prob.loopSem, weight_loopIter_eq]

end Generic
end RelOL
