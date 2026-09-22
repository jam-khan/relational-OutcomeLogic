import RelationalOutcomeLogic.Generic.Rules
import RelationalOutcomeLogic.Generic.Loops.Semantics
import RelationalOutcomeLogic.Set.Judgment

/-! # Set semantics as an instance of the shared outcome logic

The instances and compatibility theorems identify the concrete API with the
shared assertions, execution, and full loop semantics.
-/

universe u

namespace RelOL

instance setOutcomeModel : OutcomeModel (Set : Type u → Type u) where
  empty := ∅
  add := (· ∪ ·)
  pure a := {a}
  bind x k := kleisli k x
  add_assoc := Set.union_assoc
  add_comm := Set.union_comm
  empty_add := Set.empty_union
  add_empty := Set.union_empty
  pure_bind a k := kleisli_singleton k a
  bind_pure x := by ext a; simp
  bind_assoc x k l := kleisli_comp k l x
  empty_bind := kleisli_empty
  bind_empty x := by ext a; simp
  add_bind x y k := kleisli_union k x y
  bind_add x k l := kleisli_pointwise_union k l x

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

namespace Generic

variable {α β γ δ : Type u}

@[simp] theorem set_empty_eq : (OutcomeModel.empty : Set α) = ∅ := rfl
@[simp] theorem set_add_eq (x y : Set α) : OutcomeModel.add x y = x ∪ y := rfl
@[simp] theorem set_pure_eq (a : α) : (OutcomeModel.pure a : Set α) = {a} := rfl
@[simp] theorem set_bind_eq (x : Set α) (k : α → Set β) :
    OutcomeModel.bind x k = kleisli k x := rfl

theorem set_oplus_eq (P Q : RelOL.RAssn α β) :
    oplus (M := Set) P Q = RelOL.oplus P Q := rfl
theorem set_emp_eq : (emp : RAssn Set α β) = RelOL.rempty := rfl
theorem set_exactly_eq (x : Set α) (y : Set β) :
    exactly x y = RelOL.exactly x y := rfl
theorem set_quadSem_eq (F : Set α → Set γ) (G : Set β → Set δ)
    (P : RelOL.RAssn α β) (Q : RelOL.RAssn γ δ) :
    quadSem F G P Q = RelOL.quadSem F G P Q := rfl
theorem set_quad_eq (P Q : RelOL.RAssn RelOL.State RelOL.State) (c d : Cmd) :
    quad P (sem c) (sem d) Q = RelOL.quad P c d Q := rfl

/-- Existing set judgments inherit the shared additive rule. -/
theorem set_quad_split {P P' Q Q' : RelOL.RAssn RelOL.State RelOL.State} {c d : Cmd}
    (h : RelOL.quad P c d Q) (h' : RelOL.quad P' c d Q') :
    RelOL.quad (RelOL.oplus P P') c d (RelOL.oplus Q Q') :=
  quad_split (M := Set) h h'

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

end Generic
end RelOL
