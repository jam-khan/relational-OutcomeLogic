import RelationalOutcomeLogic.Quadruple

/-!
# Soundness of the RelOL proof rules

All rules are proved at the `quadSem` level where possible (language-independent).
-/

namespace RelOL

variable {α β γ δ ε ζ : Type*}

-- Structural rules (semantic)

/-
  R' ⇒ R    ⟨R⟩ F ~ G ⟨S⟩   S ⇒ S'
  -------------------------------- Conseq
          ⟨R'⟩ F ~ G ⟨S'⟩
-/
theorem quadSem_conseq {F : Set α → Set γ} {G : Set β → Set δ}
    {R R' : RAssn α β} {S S' : RAssn γ δ} (hR : entail R' R)
    (h : quadSem F G R S) (hS : entail S S') : quadSem F G R' S' := by
  unfold entail at hR hS
  unfold quadSem
  unfold quadSem at h
  intro m m' hR1
  apply hS
  apply h
  apply hR
  assumption

/-
  The Sym rule: flip the two sides.
  Swaps carrier types, so it is available
  unchanged in the heterogeneous setting.

    ⟨R⟩ F ~ G ⟨S⟩
  ----------------- Sym    R⊤(m', m) := R(m, m')
    ⟨R⊤⟩ G ~ F ⟨S⊤⟩

  Enables deriving right-sided rules from left-side, and vice versa.
-/
theorem quadSem_sym {F : Set α → Set γ} {G : Set β → Set δ}
    {R : RAssn α β} {S : RAssn γ δ} (h : quadSem F G R S) :
    quadSem G F R.swap S.swap :=
  fun m' m hm => h m m' hm

/-
  Sequencing at the semantic level:
  quadruples compose along function composition of the lifts.

  ⟨R⟩ F ~ G ⟨S⟩       ⟨S⟩ F' ~ G' ⟨T⟩
  ----------------------------------- Comp
        ⟨R⟩ F' ∘ F, G' ∘ G ⟨T⟩
-/
theorem quadSem_comp
  {F : Set α → Set γ} {G : Set β → Set δ}
  {F' : Set γ → Set ε} {G' : Set δ → Set ζ}
  {R : RAssn α β} {S : RAssn γ δ} {T : RAssn ε ζ}
  (h₁ : quadSem F G R S) (h₂ : quadSem F' G' S T) :
    quadSem (F' ∘ F) (G' ∘ G) R T :=
  fun m m' hm => h₂ _ _ (h₁ m m' hm)

/- Any quadruple with post `⊤` holds.

  ----------------- True
    ⟨R⟩ F ~ G ⟨⊤⟩
-/
theorem quadSem_rtop
  (F : Set α → Set γ) (G : Set β → Set δ) (R : RAssn α β) :
    quadSem F G R rtop := by
  unfold quadSem
  intro m m' hR
  unfold rtop; grind


end RelOL
