import RelationalOutcomeLogic.Lang
import RelationalOutcomeLogic.Assertions

/-!
# The relational quadruple

Two-level definition:

* `quadSem F G R S` — the semantic quadruple over abstract lift functions
  `F, G`. All proof rules are established at this level (with union/empty-
  preservation hypotheses where needed), so they transfer unchanged to any
  language whose lift is a `kleisli` instance — including the heterogeneous
  pair in `Hetero/`.
* `quad R c c' S` (notation `⦃R⦄ c ~ c' ⦃S⦄`) — the homogeneous instance,
  keeping Hoare's forward shape: pre-models are pushed through the Kleisli
  extensions of both programs.
-/

namespace RelOL

variable {α β γ δ : Type*}

/-- Semantic relational quadruple over abstract lift functions. -/
def quadSem (F : Set α → Set γ) (G : Set β → Set δ) (R : RAssn α β) (S : RAssn γ δ) : Prop :=
  ∀ m m', R m m' → S (F m) (G m')

/-- The homogeneous relational Outcome Logic quadruple. -/
def quad (R : RAssn State State) (c c' : Cmd) (S : RAssn State State) : Prop :=
  quadSem (semLift c) (semLift c') R S

@[inherit_doc] scoped notation:50 "⦃" R "⦄ " c:51 " ~ " c':51 " ⦃" S "⦄" => quad R c c' S

theorem quad_skip (R : RAssn State State) : ⦃R⦄ Cmd.skip ~ Cmd.skip ⦃R⦄ := by
  intro m m' hm
  simpa [semLift_skip] using hm

end RelOL
