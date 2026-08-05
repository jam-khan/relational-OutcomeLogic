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
  {R S : RAssn State State} {c c' : Cmd}
  (h : ⦃R⦄ c ~ c' ⦃S⦄) :
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

/-
    ⦃R⦄ c₁ ~ c₁' ⦃S₁⦄      ⦃R⦄ c₂ ~ c₂' ⦃S₂⦄
  ──────────────────────────────────────────  Choice
      ⦃R⦄ c₁ + c₂ ~ c₁' + c₂' ⦃S₁ ⊕ S₂⦄

  Synchronized choice: both sides branch together. The ⊕ in the
  postcondition is born here — branch i contributes its outcomes to Sᵢ.
-/
theorem quad_choice_sync {R S₁ S₂ : RAssn State State} {c₁ c₂ c₁' c₂' : Cmd}
  (h₁ : ⦃R⦄ c₁ ~ c₁' ⦃S₁⦄)
  (h₂ : ⦃R⦄ c₂ ~ c₂' ⦃S₂⦄) :
    ⦃R⦄ c₁ + c₂ ~ c₁' + c₂' ⦃S₁ ⊕ₒ S₂⦄ := by
  intro m m' hm
  simp only [Cmd.add_def, semLift_choice]
  exact oplus_intro (h₁ _ _ hm) (h₂ _ _ hm)

/-
    ⦃R⦄ c₁ ~ c' ⦃S₁⦄      ⦃R⦄ c₂ ~ c' ⦃S₂⦄
  ─────────────────────────────────────────  Choice-L
         ⦃R⦄ c₁ + c₂ ~ c' ⦃S₁ ⊕ S₂⦄

  Only the left program branches; the passive right side must self-split
  X = X ∪ X. Exactly here overlap-friendly ⊕ is essential — a disjoint ⊕
  would make this rule false.
-/
theorem quad_choice_left {R S₁ S₂ : RAssn State State} {c₁ c₂ c' : Cmd}
  (h₁ : ⦃R⦄ c₁ ~ c' ⦃S₁⦄)
  (h₂ : ⦃R⦄ c₂ ~ c' ⦃S₂⦄) :
    ⦃R⦄ c₁ + c₂ ~ c' ⦃S₁ ⊕ₒ S₂⦄ := by
  intro m m' hm
  simp only [Cmd.add_def, semLift_choice]
  rw [← Set.union_self (semLift c' m')]
  exact oplus_intro (h₁ _ _ hm) (h₂ _ _ hm)

/-
  ────────────────── True
    ⦃R⦄ c ~ c' ⦃⊤⦄
-/
theorem quad_rtop (R : RAssn State State) (c c' : Cmd) :
  ⦃R⦄ c ~ c' ⦃⊤ₒ⦄ := by
  apply quadSem_rtop _ _ _

/-
       ⦃R⦄ c ~ c' ⦃S⦄
  ──────────────────────────  UnderApprox    (derived: Choice-L + True)
    ⦃R⦄ c + d ~ c' ⦃S ⊕ ⊤⦄

  A quadruple survives adding nondeterministic branches once ⊕ ⊤ drops
  the new outcomes — the OL-vs-IL selling point.
-/
theorem quad_underapprox {R S : RAssn State State} {c c' d : Cmd}
  (h : ⦃R⦄ c ~ c' ⦃S⦄) :
    ⦃R⦄ c + d ~ c' ⦃S ⊕ₒ ⊤ₒ⦄ := by
  have e₁ : ⦃R⦄ d ~ c' ⦃⊤ₒ⦄ := quad_rtop R d c'
  apply quad_choice_left h e₁

/-
    ⦃R⦄ c ~ c₁' ⦃S₁⦄      ⦃R⦄ c ~ c₂' ⦃S₂⦄
  ─────────────────────────────────────────  Choice-R    (derived: Sym ∘ Choice-L ∘ Sym)
         ⦃R⦄ c ~ c₁' + c₂' ⦃S₁ ⊕ S₂⦄

  Closes the "derivable" claim in the paper's rule figure.
-/
theorem quad_choice_right {R S₁ S₂ : RAssn State State} {c c₁' c₂' : Cmd}
    (h₁ : ⦃R⦄ c ~ c₁' ⦃S₁⦄)
    (h₂ : ⦃R⦄ c ~ c₂' ⦃S₂⦄) :
      ⦃R⦄ c ~ c₁' + c₂' ⦃S₁ ⊕ₒ S₂⦄ := by
  have d₁ : ⦃R⦄ c ~ c₁' ⦃S₁⦄                := by
    assumption
  have d₂ : ⦃R⦄ c ~ c₂' ⦃S₂⦄                := by
    assumption
  have d₃ : ⦃Rᵀ⦄ c₁' ~ c ⦃S₁ᵀ⦄              := by
    apply quad_sym d₁
  have d₄ : ⦃Rᵀ⦄ c₁' + c₂' ~ c ⦃S₁ᵀ ⊕ₒ S₂ᵀ⦄ := by
    apply quad_choice_left d₃ (quad_sym h₂)
  have h := quad_sym (quad_choice_left (quad_sym h₁) (quad_sym h₂))
  rwa [RAssn.swap_swap, RAssn.swap_oplus, RAssn.swap_swap, RAssn.swap_swap] at h

/-! ## Atomic axioms and conditional rules -/

/-
  ────────────────────────────────────────────────────── Asgn
    ⦃⌈r[x := e, x' := e']⌉⦄ x ::= e ~ x' ::= e' ⦃⌈r⌉⦄

  Floyd-style forward axiom on atoms: the precondition is r pre-composed
  with both updates, i.e. r (s[x ↦ e s]) (s'[x' ↦ e' s']).
-/
theorem quad_assign
  {r : State → State → Prop} (x x' : String) (e e' : State → Int) :
    ⦃⌈fun s s' => r (Function.update s x (e s)) (Function.update s' x' (e' s'))⌉⦄
      ↑x ::= ↑e ~ ↑x' ::= ↑e'
    ⦃⌈r⌉⦄ := by
  rintro m m' ⟨⟨s₀, hs₀⟩, ⟨s₀', hs₀'⟩, hall⟩
  rw [semLift_assign, semLift_assign]
  refine ⟨⟨_, Set.mem_image_of_mem _ hs₀⟩, ⟨_, Set.mem_image_of_mem _ hs₀'⟩, ?_⟩
  rintro t ⟨s, hs, rfl⟩ t' ⟨s', hs', rfl⟩
  exact hall s hs s' hs'

/-
  ──────────────────────────────────────── Asgn-L
    ⦃⌈r[x := e]⌉⦄ x ::= e ~ SKIP ⦃⌈r⌉⦄

  One-sided: the left program assigns, the right stays put.
-/
theorem quad_assign_left {r : State → State → Prop} (x : String) (e : State → Int) :
    ⦃⌈fun s s' => r (Function.update s x (e s)) s'⌉⦄
      ↑x ::= ↑e ~ SKIP
    ⦃⌈r⌉⦄ := by
  rintro m m' ⟨⟨s₀, hs₀⟩, hne', hall⟩
  rw [semLift_assign, semLift_skip]
  refine ⟨⟨_, Set.mem_image_of_mem _ hs₀⟩, hne', ?_⟩
  rintro t ⟨s, hs, rfl⟩ t' ht'
  exact hall s hs t' ht'

/-
    R ⊨ b, b' uniformly true                  ⦃R⦄ c₁ ~ c₁' ⦃S⦄
  ──────────────────────────────────────────────────────────────  If-TT
    ⦃R⦄ IF b THEN c₁ ELSE c₂ END ~ IF b' THEN c₁' ELSE c₂' END ⦃S⦄

  Both guards true on every state of every pre-model, so both sides take
  the then-branch. Uniformly false: `quad_ite_neg`. Mixed pre-models:
  `quad_split` the precondition first.
-/
theorem quad_ite_pos {R S : RAssn State State} {b b' : State → Prop}
  {c₁ c₂ c₁' c₂' : Cmd}
  (hb : ∀ m m', R m m' → (∀ s ∈ m, b s) ∧ (∀ s' ∈ m', b' s'))
  (h : ⦃R⦄ c₁ ~ c₁' ⦃S⦄) :
    ⦃R⦄
      IF ↑b THEN c₁ ELSE c₂ END ~ IF ↑b' THEN c₁' ELSE c₂' END
    ⦃S⦄ := by
  intro m m' hm
  obtain ⟨h₁, h₂⟩ := hb m m' hm
  rw [semLift_ite_pos h₁, semLift_ite_pos h₂]
  exact h m m' hm

/-
    R ⊨ b, b' uniformly false                 ⦃R⦄ c₂ ~ c₂' ⦃S⦄
  ──────────────────────────────────────────────────────────────  If-FF
    ⦃R⦄ IF b THEN c₁ ELSE c₂ END ~ IF b' THEN c₁' ELSE c₂' END ⦃S⦄
-/
theorem quad_ite_neg {R S : RAssn State State} {b b' : State → Prop} {c₁ c₂ c₁' c₂' : Cmd}
  (hb : ∀ m m', R m m' → (∀ s ∈ m, ¬ b s) ∧ (∀ s' ∈ m', ¬ b' s'))
  (h : ⦃R⦄ c₂ ~ c₂' ⦃S⦄) :
    ⦃R⦄
      IF ↑b THEN c₁ ELSE c₂ END ~ IF ↑b' THEN c₁' ELSE c₂' END
    ⦃S⦄ := by
  intro m m' hm
  obtain ⟨h₁, h₂⟩ := hb m m' hm
  rw [semLift_ite_neg h₁, semLift_ite_neg h₂]
  exact h m m' hm

/-
    R ⊨ b uniformly true      ⦃R⦄ c₁ ~ c' ⦃S⦄
  ─────────────────────────────────────────────  If-L-TT
     ⦃R⦄ IF b THEN c₁ ELSE c₂ END ~ c' ⦃S⦄

  One-sided: only the left program branches. Uniformly-false variant below.
-/
theorem quad_ite_left_pos {R S : RAssn State State} {b : State → Prop} {c₁ c₂ c' : Cmd}
  (hb : ∀ m m', R m m' → ∀ s ∈ m, b s)
  (h : ⦃R⦄ c₁ ~ c' ⦃S⦄) :
    ⦃R⦄
      IF ↑b THEN c₁ ELSE c₂ END ~ c'
    ⦃S⦄ := by
  intro m m' hm
  rw [semLift_ite_pos (hb m m' hm)]
  exact h m m' hm

theorem quad_ite_left_neg {R S : RAssn State State} {b : State → Prop} {c₁ c₂ c' : Cmd}
  (hb : ∀ m m', R m m' → ∀ s ∈ m, ¬ b s)
  (h : ⦃R⦄ c₂ ~ c' ⦃S⦄) :
    ⦃R⦄
      IF ↑b THEN c₁ ELSE c₂ END ~ c'
    ⦃S⦄ := by
  intro m m' hm
  rw [semLift_ite_neg (hb m m' hm)]
  exact h m m' hm

/-! ## While rules

Three tiers, matching the three uses:
* unrolling (`quad_while_unroll_left/right`) — replace the loop by one step;
* fuel (`quad_while_fuel`) — an `⊕ ⊤` certificate on truncated loops transfers
  to the full loops, the workhorse for certifying violations of loop programs;
* ranked invariant (`quad_while_inv`) — the exhaustive reading, for loops whose
  synchronized iteration count is bounded by the rank of the invariant. -/

/-
    ⦃R⦄ IF b THEN c ;; WHILE b DO c END ELSE SKIP END ~ c' ⦃S⦄
  ────────────────────────────────────────────────────────────  Unroll-L
                ⦃R⦄ WHILE b DO c END ~ c' ⦃S⦄

  The loop is its one-step unrolling (`sem_while_eq_unroll`), so proving
  the unrolled form proves the loop. Right-side version below.
-/
theorem quad_while_unroll_left {R S : RAssn State State} {b : State → Prop}
    {c c' : Cmd}
    (h : ⦃R⦄ IF ↑b THEN c ;; WHILE ↑b DO c END ELSE SKIP END ~ c' ⦃S⦄) :
    ⦃R⦄ WHILE ↑b DO c END ~ c' ⦃S⦄ := by
  intro m m' hm
  have hs := h m m' hm
  rwa [show semLift (Cmd.ite b (Cmd.seq c (Cmd.while b c)) Cmd.skip) m
      = semLift (Cmd.while b c) m from by
    unfold semLift; rw [← sem_while_eq_unroll]] at hs

theorem quad_while_unroll_right {R S : RAssn State State} {b' : State → Prop}
    {c c' : Cmd}
    (h : ⦃R⦄ c ~ IF ↑b' THEN c' ;; WHILE ↑b' DO c' END ELSE SKIP END ⦃S⦄) :
    ⦃R⦄ c ~ WHILE ↑b' DO c' END ⦃S⦄ := by
  intro m m' hm
  have hs := h m m' hm
  rwa [show semLift (Cmd.ite b' (Cmd.seq c' (Cmd.while b' c')) Cmd.skip) m'
      = semLift (Cmd.while b' c') m' from by
    unfold semLift; rw [← sem_while_eq_unroll]] at hs

/-
    ⟪R⟫ loopⁿ , loop'ⁿ' ⟪S ⊕ ⊤⟫              loopⁿ := kleisli (loopIter b (sem c) n)
  ─────────────────────────────────────────────────  Fuel
    ⦃R⦄ WHILE b DO c END ~ WHILE b' DO c' END ⦃S ⊕ ⊤⦄

  An ⊕ ⊤ certificate proved against fuel-truncated loops transfers to the
  full loops: truncations under-approximate the loop semantics and ⊕ ⊤
  absorbs the rest. The workhorse for certifying violations of loop programs.
-/
theorem quad_while_fuel {R S : RAssn State State} {b b' : State → Prop}
    {c c' : Cmd} (n n' : ℕ)
    (h : ⟪R⟫ kleisli (loopIter b (sem c) n) , kleisli (loopIter b' (sem c') n')
      ⟪S ⊕ₒ ⊤ₒ⟫) :
    ⦃R⦄
      WHILE ↑b DO c END ~ WHILE ↑b' DO c' END
    ⦃S ⊕ₒ ⊤ₒ⦄ := by
  intro m m' hm
  refine oplus_top_mono (h m m' hm) ?_ ?_
  · exact kleisli_mono_fun (fun s => loopIter_subset_sem b c n s) m
  · exact kleisli_mono_fun (fun s => loopIter_subset_sem b' c' n' s) m'

/-
    I(k+1) ⊨ b, b' true    I(0) ⊨ b, b' false    ∀ k, ⦃I(k+1)⦄ c ~ c' ⦃I(k)⦄
  ───────────────────────────────────────────────────────────────────────────  While-Inv
           ⦃I(k)⦄ WHILE b DO c END ~ WHILE b' DO c' END ⦃I(0)⦄

  Ranked invariant, the exhaustive reading: I(k) holds with k synchronized
  iterations remaining. The rank decides both guards uniformly, so both
  loops run for exactly the rank's iterations — divergence never enters.
-/
theorem quad_while_inv {I : ℕ → RAssn State State} {b b' : State → Prop} {c c' : Cmd}
    (hpos : ∀ k m m', I (k + 1) m m' → (∀ s ∈ m, b s) ∧ (∀ s' ∈ m', b' s'))
    (hzero : ∀ m m', I 0 m m' → (∀ s ∈ m, ¬ b s) ∧ (∀ s' ∈ m', ¬ b' s'))
    (hbody : ∀ k, ⦃I (k + 1)⦄ c ~ c' ⦃I k⦄) (k : ℕ) :
    ⦃I k⦄
      WHILE ↑b DO c END ~ WHILE ↑b' DO c' END
    ⦃I 0⦄ := by
  induction k with
  | zero =>
    intro m m' hm
    obtain ⟨h₁, h₂⟩ := hzero m m' hm
    rwa [semLift_while_neg h₁, semLift_while_neg h₂]
  | succ k ih =>
    intro m m' hm
    obtain ⟨h₁, h₂⟩ := hpos k m m' hm
    rw [semLift_while_pos h₁, semLift_while_pos h₂]
    exact ih _ _ (hbody k m m' hm)

/-
    I(k+1) ⊨ b true      I(0) ⊨ b false      ∀ k, ⦃I(k+1)⦄ c ~ SKIP ⦃I(k)⦄
  ─────────────────────────────────────────────────────────────────────────  While-L
                 ⦃I(k)⦄ WHILE b DO c END ~ SKIP ⦃I(0)⦄

  One-sided ranked While: the left program loops, the right stays put.
-/
theorem quad_while_left {I : ℕ → RAssn State State} {b : State → Prop} {c : Cmd}
  (hpos : ∀ k m m', I (k + 1) m m' → ∀ s ∈ m, b s)
  (hzero : ∀ m m', I 0 m m' → ∀ s ∈ m, ¬ b s)
  (hbody : ∀ k, ⦃I (k + 1)⦄ c ~ SKIP ⦃I k⦄) (k : ℕ) :
    ⦃I k⦄
      WHILE ↑b DO c END ~ SKIP
    ⦃I 0⦄ := by
  induction k with
  | zero =>
    intro m m' hm
    rwa [semLift_while_neg (hzero m m' hm), semLift_skip]
  | succ k ih =>
    intro m m' hm
    rw [semLift_while_pos (hpos k m m' hm)]
    refine ih _ _ ?_
    have hb := hbody k m m' hm
    rwa [semLift_skip] at hb

end RelOL
