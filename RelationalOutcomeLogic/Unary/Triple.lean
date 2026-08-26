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

-- The Outcome Logic triple (forward shape, Kleisli extension)
def triple (P : Assn State) (c : Cmd) (Q : Assn State) : Prop :=
  ∀ m, P m → Q (semLift c m)

/- ## Notation

  `⌜b⌝`            atomic assertion, `b` a program guard: `⌜x = 1⌉` is
                   `atomU (fun s => s "x" = 1)`. The term form `⌜p⌝` with
                   `p : State → Prop` also works (write `↑p` inside compounds).
  `⦅P⦆ c ⦅Q⦆`      the triple.

The paper writes `⟨P⟩ c ⟨Q⟩`, but `⟨…⟩` is the anonymous constructor and
`⦃…⦄`/`⟪…⟫` are already the relational brackets, so the triple gets `⦅…⦆`.
The program slot is level 50, so `;;`-chains need no parens.
-/

scoped notation "⌜" p "⌝" => atomU p
scoped syntax "⌜" rbexp "⌝" : term
macro_rules | `(⌜$b:rbexp⌝) => `(atomU ⟦$b:rbexp⟧)

scoped notation:50 "⦅" P "⦆ " c:50 " ⦅" Q "⦆" => triple P c Q

theorem triple_conseq {P P' Q Q' : Assn State} {c : Cmd}
  (hP : P' ⟹ᵤ P) (h : ⦅P⦆ c ⦅Q⦆) (hQ : Q ⟹ᵤ Q') :
  ------------------------------------------------
                ⦅P'⦆ c ⦅Q'⦆ :=
  fun m hm => hQ _ (h m (hP m hm))

theorem triple_seq {P Q R : Assn State} {c₁ c₂ : Cmd}
  (h₁ : ⦅P⦆ c₁ ⦅Q⦆) (h₂ : ⦅Q⦆ c₂ ⦅R⦆) :
  -----------------------------------
    ⦅P⦆ c₁ ;; c₂ ⦅R⦆ := by
  intro m hm
  rw [semLift_seq]
  exact h₂ _ (h₁ m hm)

/-
  The Split rule (OL Fig. 4): pre and post split along `⊕` simultaneously.
  Sound because `semLift` distributes over `∪` (the execution-model law).
-/
theorem triple_split {P₁ P₂ Q₁ Q₂ : Assn State} {c : Cmd}
  (h₁ : ⦅P₁⦆ c ⦅Q₁⦆) (h₂ : ⦅P₂⦆ c ⦅Q₂⦆) :
  -----------------------------------
      ⦅P₁ ⊕ᵤ P₂⦆ c ⦅Q₁ ⊕ᵤ Q₂⦆
  := by rintro m ⟨m₁, m₂, rfl, hm₁, hm₂⟩
        rw [semLift_union]
        exact oplusU_intro (h₁ _ hm₁) (h₂ _ hm₂)

/-
  The Choice/Plus rule (OL Fig. 4):
  same precondition on both branches, results joined by `⊕`.
-/
theorem triple_choice {P Q₁ Q₂ : Assn State} {c₁ c₂ : Cmd}
                (h₁ : ⦅P⦆ c₁ ⦅Q₁⦆)
    ------------------------------------------
    (h₂ : ⦅P⦆ c₂ ⦅Q₂⦆) : ⦅P⦆ c₁ + c₂ ⦅Q₁ ⊕ᵤ Q₂⦆ := by
  intro m hm
  simp only [Cmd.add_def, semLift_choice]
  exact oplusU_intro (h₁ m hm) (h₂ m hm)

end OL
