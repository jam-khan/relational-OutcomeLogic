import RelationalOutcomeLogic.Generic.Concrete
import RelationalOutcomeLogic.Generic.Iteration
import RelationalOutcomeLogic.Generic.WeightedLogic
import RelationalOutcomeLogic.Algebra.WeightedOrder
import RelationalOutcomeLogic.Algebra.WeightedCoupling
import RelationalOutcomeLogic.Algebra.Instances.Probability
import RelationalOutcomeLogic.Prob.Loop
import RelationalOutcomeLogic.Prob.Coupling
import RelationalOutcomeLogic.Subsumption.PRHL

/-!
# Compatibility with the existing Set and probability developments

The old interfaces remain available. These equalities identify their execution and
exact coupling semantics with the shared constructions, including full loops.
-/

universe u

namespace RelOL

instance setIterationModel : IterationModel (Set : Type u → Type u) where
  empty_eq_bot := rfl
  bind_mono := by
    intro α β x y k l hxy hkl
    exact (kleisli_mono hxy).trans (kleisli_mono_fun hkl y)
  bind_iSup_right := by
    intro α β x k _
    change kleisli (⨆ n, k n) x = ⨆ n, kleisli (k n) x
    ext b
    simp only [mem_kleisli, iSup_apply]
    constructor
    · rintro ⟨a, ha, s, ⟨n, rfl⟩, hb⟩
      exact ⟨kleisli (k n) x, ⟨n, rfl⟩, mem_kleisli.mpr ⟨a, ha, hb⟩⟩
    · rintro ⟨s, ⟨n, rfl⟩, hb⟩
      obtain ⟨a, ha, hb⟩ := mem_kleisli.mp hb
      exact ⟨a, ha, k n a, ⟨n, rfl⟩, hb⟩

instance weightIterationModel : IterationModel (Weight : Type u → Type u) where
  empty_eq_bot := rfl
  bind_mono := Weight.bind_mono
  bind_iSup_right := Weight.bind_iSup_right

namespace Generic

open scoped ENNReal

variable {α β γ δ : Type u}

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

theorem set_loopIter_eq (g : α → Prop) (k : α → Set α) (n : ℕ) :
    Generic.loopIter g k n = RelOL.loopIter g k n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext s
      simp only [Generic.loopIter, RelOL.loopIter, ih, set_bind_eq, set_pure_eq]

theorem set_loopSem_eq (g : α → Prop) (k : α → Set α) :
    Generic.loopSem g k = RelOL.loopSem g k := by
  funext s
  simp only [Generic.loopSem, RelOL.loopSem, set_loopIter_eq]
  rfl

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
