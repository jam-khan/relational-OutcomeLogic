import RelationalOutcomeLogic.Generic.Rules
import RelationalOutcomeLogic.Quadruple
import RelationalOutcomeLogic.Prob.Lang

/-!
# Concrete models and compatibility with the existing logics

The original set and probability APIs remain unchanged. Their additive assertions
and semantic judgments are definitionally the corresponding shared constructions;
the instantiated splitting proofs below use the shared theorem directly.
-/

namespace RelOL

universe u

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

namespace Generic

variable {α β γ δ : Type u}

@[simp] theorem set_empty_eq : (OutcomeModel.empty : Set α) = ∅ := rfl
@[simp] theorem set_add_eq (x y : Set α) : OutcomeModel.add x y = x ∪ y := rfl
@[simp] theorem set_pure_eq (a : α) : (OutcomeModel.pure a : Set α) = {a} := rfl
@[simp] theorem set_bind_eq (x : Set α) (k : α → Set β) :
    OutcomeModel.bind x k = kleisli k x := rfl

@[simp] theorem weight_empty_eq : (OutcomeModel.empty : Weight α) = 0 := rfl
@[simp] theorem weight_add_eq (x y : Weight α) : OutcomeModel.add x y = x + y := rfl
@[simp] theorem weight_pure_eq (a : α) :
    (OutcomeModel.pure a : Weight α) = Weight.pure a := rfl
@[simp] theorem weight_bind_eq (x : Weight α) (k : α → Weight β) :
    OutcomeModel.bind x k = Weight.bind x k := rfl

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

/-- Existing set judgments inherit the shared additive rule. -/
theorem set_quad_split {P P' Q Q' : RelOL.RAssn RelOL.State RelOL.State} {c d : Cmd}
    (h : RelOL.quad P c d Q) (h' : RelOL.quad P' c d Q') :
    RelOL.quad (RelOL.oplus P P') c d (RelOL.oplus Q Q') :=
  quad_split (M := Set) h h'

/-- Existing probabilistic judgments inherit exactly the same proof. -/
theorem weight_quad_split {P P' Q Q' : Prob.RAssn α β}
    {c : Prob.Cmd α} {d : Prob.Cmd β}
    (h : Prob.quad P c d Q) (h' : Prob.quad P' c d Q') :
    Prob.quad (Prob.oplus P P') c d (Prob.oplus Q Q') :=
  quad_split (M := Weight) h h'

end Generic
end RelOL
