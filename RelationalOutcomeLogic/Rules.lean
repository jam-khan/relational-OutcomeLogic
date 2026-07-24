import RelationalOutcomeLogic.Quadruple

/-!
# Soundness of the RelOL proof rules

All rules are proved at the `quadSem` level where possible (language-independent;
union-preservation enters as a hypothesis discharged by the Kleisli kit), then
instantiated to `quad`.

Design notes recorded in Notes.md:
* **Split** (`quadSem_split`) is the load-bearing wall (Context.MD §6). At the
  *soundness* level it goes through cleanly — the D.3-style side conditions
  belong to the inversion/falsification direction (Metatheory.lean), not here.
* **One-sided Choice** (`quad_choice_left`) is where the overlap-friendly `⊕`
  pays off: the passive side must self-split `X = X ∪ X`, which a
  disjointness-constrained `⊕` would forbid — the rule would be *false*.
* **Sym** swaps the carriers, so it remains well-typed heterogeneously
  (Murray's completeness-critical Sym rule, for free).
-/

namespace RelOL

variable {α β γ δ ε ζ : Type*}

/-! ## Structural rules (fully semantic) -/

theorem quadSem_conseq {F : Set α → Set γ} {G : Set β → Set δ}
    {R R' : RAssn α β} {S S' : RAssn γ δ} (hR : entail R' R)
    (h : quadSem F G R S) (hS : entail S S') : quadSem F G R' S' :=
  fun m m' hm => hS _ _ (h m m' (hR m m' hm))

/-- The Sym rule: flip the two sides. Swaps carrier types, so it is available
unchanged in the heterogeneous setting. -/
theorem quadSem_sym {F : Set α → Set γ} {G : Set β → Set δ}
    {R : RAssn α β} {S : RAssn γ δ} (h : quadSem F G R S) :
    quadSem G F R.swap S.swap :=
  fun m' m hm => h m m' hm

/-- Sequencing at the semantic level: quadruples compose along function
composition of the lifts. -/
theorem quadSem_comp {F : Set α → Set γ} {G : Set β → Set δ}
    {F' : Set γ → Set ε} {G' : Set δ → Set ζ}
    {R : RAssn α β} {S : RAssn γ δ} {T : RAssn ε ζ}
    (h₁ : quadSem F G R S) (h₂ : quadSem F' G' S T) :
    quadSem (F' ∘ F) (G' ∘ G) R T :=
  fun m m' hm => h₂ _ _ (h₁ m m' hm)

/-- **Split** (the load-bearing wall): quadruples for the same program pair
combine along simultaneous `⊕`-splits of pre- and postcondition. Sound because
both lifts preserve `∪` (the execution-model law). -/
theorem quadSem_split {F : Set α → Set γ} {G : Set β → Set δ}
    {R₁ R₂ : RAssn α β} {S₁ S₂ : RAssn γ δ}
    (hF : ∀ m₁ m₂, F (m₁ ∪ m₂) = F m₁ ∪ F m₂)
    (hG : ∀ m₁ m₂, G (m₁ ∪ m₂) = G m₁ ∪ G m₂)
    (h₁ : quadSem F G R₁ S₁) (h₂ : quadSem F G R₂ S₂) :
    quadSem F G (R₁ ⊕ₒ R₂) (S₁ ⊕ₒ S₂) := by
  rintro m m' ⟨m₁, m₂, m₁', m₂', rfl, rfl, hm₁, hm₂⟩
  rw [hF, hG]
  exact oplus_intro (h₁ _ _ hm₁) (h₂ _ _ hm₂)

/-- Any quadruple with post `⊤` holds. -/
theorem quadSem_rtop (F : Set α → Set γ) (G : Set β → Set δ) (R : RAssn α β) :
    quadSem F G R rtop := fun _ _ _ => trivial

/-! ## Command-level rules -/

theorem quad_conseq {R R' S S' : RAssn State State} {c c' : Cmd} (hR : entail R' R)
    (h : ⦃R⦄ c ~ c' ⦃S⦄) (hS : entail S S') : ⦃R'⦄ c ~ c' ⦃S'⦄ :=
  quadSem_conseq hR h hS

theorem quad_sym {R S : RAssn State State} {c c' : Cmd} (h : ⦃R⦄ c ~ c' ⦃S⦄) :
    ⦃R.swap⦄ c' ~ c ⦃S.swap⦄ :=
  quadSem_sym h

theorem quad_seq {R S T : RAssn State State} {c₁ c₂ c₁' c₂' : Cmd}
    (h₁ : ⦃R⦄ c₁ ~ c₁' ⦃S⦄) (h₂ : ⦃S⦄ c₂ ~ c₂' ⦃T⦄) :
    ⦃R⦄ Cmd.seq c₁ c₂ ~ Cmd.seq c₁' c₂' ⦃T⦄ := by
  intro m m' hm
  rw [semLift_seq, semLift_seq]
  exact h₂ _ _ (h₁ _ _ hm)

theorem quad_split {R₁ R₂ S₁ S₂ : RAssn State State} {c c' : Cmd}
    (h₁ : ⦃R₁⦄ c ~ c' ⦃S₁⦄) (h₂ : ⦃R₂⦄ c ~ c' ⦃S₂⦄) :
    ⦃R₁ ⊕ₒ R₂⦄ c ~ c' ⦃S₁ ⊕ₒ S₂⦄ :=
  quadSem_split (semLift_union c) (semLift_union c') h₁ h₂

/-- Synchronized Choice: both sides branch together. -/
theorem quad_choice_sync {R S₁ S₂ : RAssn State State} {c₁ c₂ c₁' c₂' : Cmd}
    (h₁ : ⦃R⦄ c₁ ~ c₁' ⦃S₁⦄) (h₂ : ⦃R⦄ c₂ ~ c₂' ⦃S₂⦄) :
    ⦃R⦄ Cmd.choice c₁ c₂ ~ Cmd.choice c₁' c₂' ⦃S₁ ⊕ₒ S₂⦄ := by
  intro m m' hm
  rw [semLift_choice, semLift_choice]
  exact oplus_intro (h₁ _ _ hm) (h₂ _ _ hm)

/-- One-sided Choice: only the left program branches. The right side must
self-split `X = X ∪ X` — this is exactly where overlap-friendly `⊕` is
essential (a disjoint `⊕` would make this rule false). -/
theorem quad_choice_left {R S₁ S₂ : RAssn State State} {c₁ c₂ c' : Cmd}
    (h₁ : ⦃R⦄ c₁ ~ c' ⦃S₁⦄) (h₂ : ⦃R⦄ c₂ ~ c' ⦃S₂⦄) :
    ⦃R⦄ Cmd.choice c₁ c₂ ~ c' ⦃S₁ ⊕ₒ S₂⦄ := by
  intro m m' hm
  rw [semLift_choice, ← Set.union_self (semLift c' m')]
  exact oplus_intro (h₁ _ _ hm) (h₂ _ _ hm)

theorem quad_rtop (R : RAssn State State) (c c' : Cmd) : ⦃R⦄ c ~ c' ⦃rtop⦄ :=
  quadSem_rtop _ _ _

/-- **UnderApprox** (the OL-vs-IL selling point, derived): a quadruple survives
adding nondeterministic branches once the postcondition drops outcomes via `⊕ ⊤`. -/
theorem quad_underapprox {R S : RAssn State State} {c c' : Cmd} (h : ⦃R⦄ c ~ c' ⦃S⦄)
    (d : Cmd) : ⦃R⦄ Cmd.choice c d ~ c' ⦃S ⊕ₒ rtop⦄ :=
  quad_choice_left h (quad_rtop R d c')

end RelOL
