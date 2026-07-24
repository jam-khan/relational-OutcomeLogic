import RelationalOutcomeLogic.Lang
import RelationalOutcomeLogic.Unary.Assertions

/-!
# The unary Outcome Logic triple and its rules

The OL triple keeps Hoare's forward shape (OOPSLA 2023, Def. 4.4):
`⊨ ⟨P⟩ C ⟨Q⟩ ⟺ ∀ m, m ⊨ P → ⟦C⟧†(m) ⊨ Q`, with the Kleisli extension
`semLift`. Rule soundness here is the unary warm-up for the relational rules;
`triple_split` exercises the bind/⋄ compatibility law (`semLift_union`).
-/

namespace OL

open RelOL

/-- The Outcome Logic triple (forward shape, Kleisli extension). -/
def triple (P : Assn State) (c : Cmd) (Q : Assn State) : Prop :=
  ∀ m, P m → Q (semLift c m)

theorem triple_conseq {P P' Q Q' : Assn State} {c : Cmd} (hP : ∀ m, P' m → P m)
    (h : triple P c Q) (hQ : ∀ m, Q m → Q' m) : triple P' c Q' :=
  fun m hm => hQ _ (h m (hP m hm))

theorem triple_seq {P Q R : Assn State} {c₁ c₂ : Cmd} (h₁ : triple P c₁ Q)
    (h₂ : triple Q c₂ R) : triple P (.seq c₁ c₂) R := by
  intro m hm
  rw [semLift_seq]
  exact h₂ _ (h₁ m hm)

/-- The Split rule (OL Fig. 4): pre and post split along `⊕` simultaneously.
Sound because `semLift` distributes over `∪` (the execution-model law). -/
theorem triple_split {P₁ P₂ Q₁ Q₂ : Assn State} {c : Cmd} (h₁ : triple P₁ c Q₁)
    (h₂ : triple P₂ c Q₂) : triple (oplusU P₁ P₂) c (oplusU Q₁ Q₂) := by
  rintro m ⟨m₁, m₂, rfl, hm₁, hm₂⟩
  rw [semLift_union]
  exact oplusU_intro (h₁ _ hm₁) (h₂ _ hm₂)

/-- The Choice/Plus rule (OL Fig. 4): same precondition on both branches,
results joined by `⊕`. -/
theorem triple_choice {P Q₁ Q₂ : Assn State} {c₁ c₂ : Cmd} (h₁ : triple P c₁ Q₁)
    (h₂ : triple P c₂ Q₂) : triple P (.choice c₁ c₂) (oplusU Q₁ Q₂) := by
  intro m hm
  rw [semLift_choice]
  exact oplusU_intro (h₁ m hm) (h₂ m hm)

end OL
