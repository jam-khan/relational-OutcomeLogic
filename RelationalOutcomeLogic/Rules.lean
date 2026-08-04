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
    {R R' : RAssn α β} {S S' : RAssn γ δ} (hR : R' ⟹ₒ R)
    (h : ⟪R⟫ F , G ⟪S⟫) (hS : S ⟹ₒ S') : ⟪R'⟫ F , G ⟪S'⟫ := by
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
    {R : RAssn α β} {S : RAssn γ δ} (h : ⟪R⟫ F , G ⟪S⟫) :
    ⟪Rᵀ⟫ G , F ⟪Sᵀ⟫ :=
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
  (h₁ : ⟪R⟫ F , G ⟪S⟫) (h₂ : ⟪S⟫ F' , G' ⟪T⟫) :
    ⟪R⟫ F' ∘ F , G' ∘ G ⟪T⟫ :=
  fun m m' hm => h₂ _ _ (h₁ m m' hm)

/-
  F(a ∪ b) = F(a) ∪ F(b)      G(a ∪ b) = G(a) ∪ G(b)
    ⟨R₁⟩ F, G ⟨S₁⟩              ⟨R₂⟩ F, G ⟨S₂⟩
──────────────────────────────────────────────────────  Split-Sem
           ⟨R₁ ⊕ R₂⟩ F, G ⟨S₁ ⊕ S₂⟩

  Why this rule?

  Let's say starting state is composed of two pieces, e.g., R₁ ⊕ R₂,
  and we know what execution does to each state individually.

  ⟨R₁⟩ F, G ⟨S₁⟩
  ⟨R₂⟩ F, G ⟨S₂⟩

  Side conditions:
  - F(a ∪ b) (run everthing at once) = F(a) ∪ F(b) (run group a, run group b, combine/pool)
  - G(a ∪ b) = G(a) ∪ G(b)

  This means that running the combined group
  = (equals)
  running each group separately and combining results

  In essence: a precondition already split into groups (R₁ ⊕ R₂) stays
  split through execution — each group evolves independently (the ∪-laws),
  and the postcondition inherits the same grouping (S₁ ⊕ S₂).
-/
theorem quadSem_split {F : Set α → Set γ} {G : Set β → Set δ}
    {R₁ R₂ : RAssn α β} {S₁ S₂ : RAssn γ δ}
    -- These conditions must be observed by the semantics
    (hF : ∀ m₁ m₂, F (m₁ ∪ m₂) = F m₁ ∪ F m₂)
    (hG : ∀ m₁ m₂, G (m₁ ∪ m₂) = G m₁ ∪ G m₂)
    (h₁ : ⟪R₁⟫ F , G ⟪S₁⟫) (h₂ : ⟪R₂⟫ F , G ⟪S₂⟫) :
    ⟪R₁ ⊕ₒ R₂⟫ F , G ⟪S₁ ⊕ₒ S₂⟫ := by
  rintro m m' ⟨m₁, m₂, m₁', m₂', rfl, rfl, hm₁, hm₂⟩
  rw [hF, hG]
  exact oplus_intro (h₁ _ _ hm₁) (h₂ _ _ hm₂)

/- Any quadruple with post `⊤` holds.

  ----------------- True
    ⟨R⟩ F ~ G ⟨⊤⟩
-/
theorem quadSem_rtop
  (F : Set α → Set γ) (G : Set β → Set δ) (R : RAssn α β) :
    ⟪R⟫ F , G ⟪⊤ₒ⟫ := by
  unfold quadSem
  intro m m' hR
  unfold rtop; grind

-- `Command-level rules`

/-
    R' ⇒ R      ⦃R⦄ c ~ c' ⦃S⦄      S ⇒ S'
  ─────────────────────────────────────────   Conseq          (quad_conseq)
            ⦃R'⦄ c ~ c' ⦃S'⦄

  Difference between above semantic rule is that
  this is instantiated to a specific `Cmd` language,
  whereas the Semantic conseq rule is generic over
  arbitrary lift functions `F := Set α → Set γ`
-/
theorem quad_conseq
  {R R' S S' : RAssn State State} {c c' : Cmd}
  (hR : R' ⟹ₒ R) (h : ⦃R⦄ c ~ c' ⦃S⦄) (hS : S ⟹ₒ S') :
    ⦃R'⦄ c ~ c' ⦃S'⦄ := by
  apply quadSem_conseq hR h hS

/-
    ⟨R⟩ c ~ c ⟨S⟩
  ----------------- Sym   R⊤(m', m) := R(m, m')
  ⟨R⊤⟩ c' ~ c ⟨S⊤⟩
-/
theorem quad_sym
  {R S : RAssn State State} {c c' : Cmd} (h : ⦃R⦄ c ~ c' ⦃S⦄) :
    ⦃Rᵀ⦄ c' ~ c ⦃Sᵀ⦄ :=
  quadSem_sym h

/-
    ⦃R⦄ c₁ ~ c₁' ⦃S⦄      ⦃S⦄ c₂ ~ c₂' ⦃T⦄
  ────────────────────────────────────────  Seq
       ⦃R⦄ c₁ ; c₂ ~ c₁' ; c₂' ⦃T⦄

  Both sides sequence in lockstep, supported by mid-condition `S`:
  This is the instantiation of `quadSem_comp` to programs, plus
  computation law `semLift (c₁; c₂) = semLift c₂ ∘ semLift c₁`.
-/
theorem quad_seq
  {R S T : RAssn State State} {c₁ c₂ c₁' c₂' : Cmd}
  (h₁ : ⦃R⦄ c₁ ~ c₁' ⦃S⦄) (h₂ : ⦃S⦄ c₂ ~ c₂' ⦃T⦄) :
    ⦃R⦄ c₁ ;; c₂ ~ c₁' ;; c₂' ⦃T⦄ := by
  rw [quad, quadSem]
  intro m m' hm
  simp only [semLift_seq]
  rw [quad, quadSem] at h₁
  rw [quad, quadSem] at h₂
  apply h₂; apply h₁; assumption

/-
  Below is the structural/syntactic rule based on the
  semantic rule `quadSem_split`.

    ⦃R₁⦄ c ~ c' ⦃S₁⦄      ⦃R₂⦄ c ~ c' ⦃S₂⦄
  ──────────────────────────────────────  Split
        ⦃R₁ ⊕ R₂⦄ c ~ c' ⦃S₁ ⊕ S₂⦄

  Example program (couldn't be proved without it.)


-/
theorem quad_split
  {R₁ R₂ S₁ S₂ : RAssn State State} {c c' : Cmd}
  (h₁ : ⦃R₁⦄ c ~ c' ⦃S₁⦄) (h₂ : ⦃R₂⦄ c ~ c' ⦃S₂⦄) :
    ⦃R₁ ⊕ₒ R₂⦄ c ~ c' ⦃S₁ ⊕ₒ S₂⦄ := by
  apply quadSem_split (semLift_union c) (semLift_union c') h₁ h₂

/-!
## Worked example: why Split is indispensable

  `P  =  (x := 1  +  x := 2) ; y := x`, compared with itself.

  The choice produces an ⊕-shaped mid-condition; the assignment after it
  can only be handled by opening that ⊕ — and Split is the only rule that
  can. Derivation (M₁ = ⌈x=1∧x'=1⌉, M₂ = ⌈x=2∧x'=2⌉, Sᵢ likewise for y):

      d₁ (Asgn+Conseq)   d₂ (Asgn+Conseq)      e₁ (Asgn)   e₂ (Asgn)
      ───────────────────────────── Choice     ──────────────────── Split
      ⦃tt⦄ choice ~ choice ⦃M₁ ⊕ M₂⦄           ⦃M₁ ⊕ M₂⦄ y:=x ~ y:=x ⦃S₁ ⊕ S₂⦄
      ──────────────────────────────────────────────────────────────── Seq
                      ⦃tt⦄ P ~ P ⦃S₁ ⊕ S₂⦄

  The `have`-blocks below mirror the tree nodes one-to-one. The leaves are
  proved semantically inline; once `quad_choice_sync` and `quad_assign`
  land, each collapses to a rule application. -/
example :
    ⦃⌈True⌉⦄
      (x ::= 1) + (x ::= 2) ;; y ::= x
      ~ (x ::= 1) + (x ::= 2) ;; y ::= x
    ⦃⌈y = 1 ∧ y' = 1⌉ ⊕ₒ ⌈y = 2 ∧ y' = 2⌉⦄ := by
  -- d₁ : first branch establishes M₁  (≡ Asgn axiom, upcoming `quad_assign`)
  have d₁ : ⦃⌈True⌉⦄ x ::= 1 ~ x ::= 1 ⦃⌈x = 1 ∧ x' = 1⌉⦄ := by
    rintro m m' ⟨⟨s, hs⟩, ⟨s', hs'⟩, -⟩
    rw [semLift_assign, semLift_assign]
    refine ⟨⟨_, Set.mem_image_of_mem _ hs⟩, ⟨_, Set.mem_image_of_mem _ hs'⟩, ?_⟩
    rintro t ⟨u, hu, rfl⟩ t' ⟨u', hu', rfl⟩
    simp
  -- d₂ : second branch establishes M₂
  have d₂ : ⦃⌈True⌉⦄ x ::= 2 ~ x ::= 2 ⦃⌈x = 2 ∧ x' = 2⌉⦄ := by
    rintro m m' ⟨⟨s, hs⟩, ⟨s', hs'⟩, -⟩
    rw [semLift_assign, semLift_assign]
    refine ⟨⟨_, Set.mem_image_of_mem _ hs⟩, ⟨_, Set.mem_image_of_mem _ hs'⟩, ?_⟩
    rintro t ⟨u, hu, rfl⟩ t' ⟨u', hu', rfl⟩
    simp
  -- Choice node: the ⊕ is BORN here  (≡ upcoming `quad_choice_sync`)
  have hChoice : ⦃⌈True⌉⦄
      (x ::= 1) + (x ::= 2) ~ (x ::= 1) + (x ::= 2)
      ⦃⌈x = 1 ∧ x' = 1⌉ ⊕ₒ ⌈x = 2 ∧ x' = 2⌉⦄ := by
    intro m m' hm
    simp only [Cmd.add_def, semLift_choice]
    exact oplus_intro (d₁ m m' hm) (d₂ m m' hm)
  -- e₁ : uniform group x=1 through the assignment  (≡ Asgn axiom)
  have e₁ : ⦃⌈x = 1 ∧ x' = 1⌉⦄ y ::= x ~ y ::= x ⦃⌈y = 1 ∧ y' = 1⌉⦄ := by
    rintro m m' ⟨⟨s, hs⟩, ⟨s', hs'⟩, hall⟩
    rw [semLift_assign, semLift_assign]
    refine ⟨⟨_, Set.mem_image_of_mem _ hs⟩, ⟨_, Set.mem_image_of_mem _ hs'⟩, ?_⟩
    rintro t ⟨u, hu, rfl⟩ t' ⟨u', hu', rfl⟩
    simpa using hall u hu u' hu'
  -- e₂ : uniform group x=2
  have e₂ : ⦃⌈x = 2 ∧ x' = 2⌉⦄ y ::= x ~ y ::= x ⦃⌈y = 2 ∧ y' = 2⌉⦄ := by
    rintro m m' ⟨⟨s, hs⟩, ⟨s', hs'⟩, hall⟩
    rw [semLift_assign, semLift_assign]
    refine ⟨⟨_, Set.mem_image_of_mem _ hs⟩, ⟨_, Set.mem_image_of_mem _ hs'⟩, ?_⟩
    rintro t ⟨u, hu, rfl⟩ t' ⟨u', hu', rfl⟩
    simpa using hall u hu u' hu'
  -- Split node: the ⊕ is CONSUMED here — no other rule can open it
  have hSplit := quad_split e₁ e₂
  -- Seq node: glue the halves along the ⊕-shaped mid-condition
  exact quad_seq hChoice hSplit

end RelOL
