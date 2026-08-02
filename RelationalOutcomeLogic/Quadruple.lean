import RelationalOutcomeLogic.Lang
import RelationalOutcomeLogic.Assertions

/-!
  # Relational Outcome Logic Quadruple `⟨P⟩ c ~ c' ⟨S⟩`
-/

namespace RelOL

variable {α β γ δ : Type*}

-- Semantic relational quadruple over abstract lift functions.
def quadSem (F : Set α → Set γ) (G : Set β → Set δ) (R : RAssn α β) (S : RAssn γ δ) : Prop :=
  ∀ m m', R m m' → S (F m) (G m')

-- Homogeneous (same-language) Relational Outcome Logic quadruple
def quad (R : RAssn State State) (c c' : Cmd) (S : RAssn State State) : Prop :=
  quadSem (semLift c) (semLift c') R S

@[inherit_doc] scoped notation:50 "⦃" R "⦄ " c:51 " ~ " c':51 " ⦃" S "⦄" => quad R c c' S

-- Example
theorem quad_skip (R : RAssn State State) : ⦃R⦄ Cmd.skip ~ Cmd.skip ⦃R⦄ := by
  rw [quad, quadSem]; simp
