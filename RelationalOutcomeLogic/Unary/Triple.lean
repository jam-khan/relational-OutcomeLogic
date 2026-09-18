import RelationalOutcomeLogic.Lang
import RelationalOutcomeLogic.Unary.Assertions

/-!
# The unary Outcome Logic triple `⦅P⦆ c ⦅Q⦆`

`⌜b⌝` is the atom of a program guard, e.g. `⌜x = 1⌝`; the term form `⌜p⌝` also works.
-/

namespace OL

open RelOL

def triple (P : Assn State) (c : Cmd) (Q : Assn State) : Prop :=
  ∀ m, P m → Q (semLift c m)

scoped notation "⌜" p "⌝" => atomU p
scoped syntax "⌜" rbexp "⌝" : term
macro_rules | `(⌜$b:rbexp⌝) => `(atomU ⟦$b:rbexp⟧)
scoped notation:50 "⦅" P "⦆ " c:50 " ⦅" Q "⦆" => triple P c Q

variable {P P' Q Q' R P₁ P₂ Q₁ Q₂ : Assn State} {c c₁ c₂ : Cmd}

theorem triple_conseq (hP : P' ⟹ᵤ P) (h : ⦅P⦆ c ⦅Q⦆) (hQ : Q ⟹ᵤ Q') : ⦅P'⦆ c ⦅Q'⦆ :=
  fun m hm => hQ _ (h m (hP m hm))

theorem triple_seq (h₁ : ⦅P⦆ c₁ ⦅Q⦆) (h₂ : ⦅Q⦆ c₂ ⦅R⦆) : ⦅P⦆ c₁ ;; c₂ ⦅R⦆ := by
  intro m hm
  rw [semLift_seq]
  exact h₂ _ (h₁ m hm)

theorem triple_split (h₁ : ⦅P₁⦆ c ⦅Q₁⦆) (h₂ : ⦅P₂⦆ c ⦅Q₂⦆) : ⦅P₁ ⊕ᵤ P₂⦆ c ⦅Q₁ ⊕ᵤ Q₂⦆ := by
  rintro m ⟨m₁, m₂, rfl, hm₁, hm₂⟩
  rw [semLift_union]
  exact oplusU_intro (h₁ _ hm₁) (h₂ _ hm₂)

theorem triple_choice (h₁ : ⦅P⦆ c₁ ⦅Q₁⦆) (h₂ : ⦅P⦆ c₂ ⦅Q₂⦆) : ⦅P⦆ c₁ + c₂ ⦅Q₁ ⊕ᵤ Q₂⦆ := by
  intro m hm
  simp only [Cmd.add_def, semLift_choice]
  exact oplusU_intro (h₁ m hm) (h₂ m hm)

end OL
