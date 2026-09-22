import RelationalOutcomeLogic.Set.Judgment
import RelationalOutcomeLogic.Set.Coupling

/-!
# Proof rules (all sound by construction)

Structural rules are proved at the `quadSem` level, for arbitrary lifts. The coupling
tier takes quadruple premises and rests on `quadSem_couple_lift_iff`, stated for any
Kleisli lifts so the heterogeneous instances reuse it.
-/

namespace RelOL

variable {α β γ δ ε ζ : Type*}

/-! ## Structural rules, semantic level -/

theorem quadSem_conseq {F : Set α → Set γ} {G : Set β → Set δ}
    {R R' : RAssn α β} {S S' : RAssn γ δ} (hR : R' ⟹ₒ R)
    (h : ⟪R⟫ F , G ⟪S⟫) (hS : S ⟹ₒ S') : ⟪R'⟫ F , G ⟪S'⟫ :=
  fun m m' hm => hS _ _ (h m m' (hR m m' hm))

theorem quadSem_sym {F : Set α → Set γ} {G : Set β → Set δ}
    {R : RAssn α β} {S : RAssn γ δ} (h : ⟪R⟫ F , G ⟪S⟫) : ⟪Rᵀ⟫ G , F ⟪Sᵀ⟫ :=
  fun m' m hm => h m m' hm

theorem quadSem_comp {F : Set α → Set γ} {G : Set β → Set δ}
    {F' : Set γ → Set ε} {G' : Set δ → Set ζ}
    {R : RAssn α β} {S : RAssn γ δ} {T : RAssn ε ζ}
    (h₁ : ⟪R⟫ F , G ⟪S⟫) (h₂ : ⟪S⟫ F' , G' ⟪T⟫) : ⟪R⟫ F' ∘ F , G' ∘ G ⟪T⟫ :=
  fun m m' hm => h₂ _ _ (h₁ m m' hm)

/-- Split: the only `⊕`-eliminator. Needs lifts that preserve unions. -/
theorem quadSem_split {F : Set α → Set γ} {G : Set β → Set δ}
    {R₁ R₂ : RAssn α β} {S₁ S₂ : RAssn γ δ}
    (hF : ∀ m₁ m₂, F (m₁ ∪ m₂) = F m₁ ∪ F m₂) (hG : ∀ m₁ m₂, G (m₁ ∪ m₂) = G m₁ ∪ G m₂)
    (h₁ : ⟪R₁⟫ F , G ⟪S₁⟫) (h₂ : ⟪R₂⟫ F , G ⟪S₂⟫) : ⟪R₁ ⊕ₒ R₂⟫ F , G ⟪S₁ ⊕ₒ S₂⟫ := by
  rintro m m' ⟨m₁, m₂, m₁', m₂', rfl, rfl, hm₁, hm₂⟩
  rw [hF, hG]
  exact oplus_intro (h₁ _ _ hm₁) (h₂ _ _ hm₂)

theorem quadSem_splitFam {ι : Type*} {F : Set α → Set γ} {G : Set β → Set δ}
    {φ : ι → RAssn α β} {ψ : ι → RAssn γ δ}
    (hF : ∀ f : ι → Set α, F (⋃ i, f i) = ⋃ i, F (f i))
    (hG : ∀ g : ι → Set β, G (⋃ i, g i) = ⋃ i, G (g i))
    (h : ∀ i, ⟪φ i⟫ F , G ⟪ψ i⟫) : ⟪oplusFam φ⟫ F , G ⟪oplusFam ψ⟫ := by
  rintro m m' ⟨f, g, rfl, rfl, hfg⟩
  rw [hF, hG]
  exact ⟨fun i => F (f i), fun i => G (g i), rfl, rfl, fun i => h i _ _ (hfg i)⟩

theorem quadSem_rtop (F : Set α → Set γ) (G : Set β → Set δ) (R : RAssn α β) :
    ⟪R⟫ F , G ⟪⊤ₒ⟫ :=
  fun _ _ _ => trivial

theorem quadSem_false {F : Set α → Set γ} {G : Set β → Set δ} (S : RAssn γ δ) :
    ⟪fun _ _ => False⟫ F , G ⟪S⟫ :=
  fun _ _ h => h.elim

theorem quadSem_conj {F : Set α → Set γ} {G : Set β → Set δ}
    {R₁ R₂ : RAssn α β} {S₁ S₂ : RAssn γ δ} (h₁ : ⟪R₁⟫ F , G ⟪S₁⟫) (h₂ : ⟪R₂⟫ F , G ⟪S₂⟫) :
    ⟪fun m m' => R₁ m m' ∧ R₂ m m'⟫ F , G ⟪fun n n' => S₁ n n' ∧ S₂ n n'⟫ :=
  fun m m' hm => ⟨h₁ m m' hm.1, h₂ m m' hm.2⟩

theorem quadSem_disj {F : Set α → Set γ} {G : Set β → Set δ}
    {R₁ R₂ : RAssn α β} {S₁ S₂ : RAssn γ δ} (h₁ : ⟪R₁⟫ F , G ⟪S₁⟫) (h₂ : ⟪R₂⟫ F , G ⟪S₂⟫) :
    ⟪fun m m' => R₁ m m' ∨ R₂ m m'⟫ F , G ⟪fun n n' => S₁ n n' ∨ S₂ n n'⟫ :=
  fun m m' hm => hm.imp (h₁ m m') (h₂ m m')

theorem quadSem_exists {ι : Sort*} {F : Set α → Set γ} {G : Set β → Set δ}
    {R : ι → RAssn α β} {S : ι → RAssn γ δ} (h : ∀ i, ⟪R i⟫ F , G ⟪S i⟫) :
    ⟪fun m m' => ∃ i, R i m m'⟫ F , G ⟪fun n n' => ∃ i, S i n n'⟫ :=
  fun m m' ⟨i, hi⟩ => ⟨i, h i m m' hi⟩

/-! ## Structural rules, command level -/

section Commands

variable {R R' S S' T R₁ R₂ S₁ S₂ : RAssn State State} {c c' d c₁ c₂ c₁' c₂' : Cmd}
  {b b' : State → Prop}

theorem quad_conseq (hR : R' ⟹ₒ R) (h : ⦃R⦄ c ~ c' ⦃S⦄) (hS : S ⟹ₒ S') : ⦃R'⦄ c ~ c' ⦃S'⦄ :=
  quadSem_conseq hR h hS

theorem quad_sym (h : ⦃R⦄ c ~ c' ⦃S⦄) : ⦃Rᵀ⦄ c' ~ c ⦃Sᵀ⦄ :=
  quadSem_sym h

theorem quad_seq (h₁ : ⦃R⦄ c₁ ~ c₁' ⦃S⦄) (h₂ : ⦃S⦄ c₂ ~ c₂' ⦃T⦄) :
    ⦃R⦄ c₁ ;; c₂ ~ c₁' ;; c₂' ⦃T⦄ := by
  intro m m' hm
  rw [semLift_seq, semLift_seq]
  exact h₂ _ _ (h₁ m m' hm)

theorem quad_split (h₁ : ⦃R₁⦄ c ~ c' ⦃S₁⦄) (h₂ : ⦃R₂⦄ c ~ c' ⦃S₂⦄) :
    ⦃R₁ ⊕ₒ R₂⦄ c ~ c' ⦃S₁ ⊕ₒ S₂⦄ :=
  quadSem_split (semLift_union c) (semLift_union c') h₁ h₂

theorem quad_splitFam {ι : Type*} {φ ψ : ι → RAssn State State}
    (h : ∀ i, ⦃φ i⦄ c ~ c' ⦃ψ i⦄) : ⦃oplusFam φ⦄ c ~ c' ⦃oplusFam ψ⦄ :=
  quadSem_splitFam (fun f => kleisli_iUnion _ f) (fun g => kleisli_iUnion _ g) h

theorem quad_rtop (R : RAssn State State) (c c' : Cmd) : ⦃R⦄ c ~ c' ⦃⊤ₒ⦄ :=
  quadSem_rtop _ _ _

/-- Joint divergence is preserved by every pair of programs. -/
theorem quad_rempty (c c' : Cmd) : ⦃rempty⦄ c ~ c' ⦃rempty⦄ := by
  rintro m m' ⟨rfl, rfl⟩
  exact ⟨semLift_empty c, semLift_empty c'⟩

theorem quad_empty_left (c c' : Cmd) : ⦃fun m _ => m = ∅⦄ c ~ c' ⦃fun n _ => n = ∅⦄ := by
  rintro m m' rfl
  exact semLift_empty c

theorem quad_diverge_left (R : RAssn State State) (c c' : Cmd) :
    ⦃R⦄ WHILE True DO c END ~ c' ⦃fun n _ => n = ∅⦄ := by
  intro m m' _
  refine Set.eq_empty_of_forall_notMem fun t ht => ?_
  obtain ⟨s, -, ht⟩ := mem_semLift.mp ht
  rw [sem_while_true] at ht
  exact ht

/-! ## Atomic commands -/

theorem quad_skip (R : RAssn State State) : ⦃R⦄ SKIP ~ SKIP ⦃R⦄ := by
  intro m m' h
  rwa [semLift_skip, semLift_skip]

/-- Assignment, backward form, for an arbitrary postcondition. -/
theorem quad_assign_any (S : RAssn State State) (x x' : String) (e e' : State → Int) :
    ⦃fun m m' => S ((fun s => Function.update s x (e s)) '' m)
        ((fun s => Function.update s x' (e' s)) '' m')⦄
      ↑x ::= ↑e ~ ↑x' ::= ↑e'
    ⦃S⦄ := by
  intro m m' h
  rwa [semLift_assign, semLift_assign]

theorem quad_assign {r : State → State → Prop} (x x' : String) (e e' : State → Int) :
    ⦃⌈fun s s' => r (Function.update s x (e s)) (Function.update s' x' (e' s'))⌉⦄
      ↑x ::= ↑e ~ ↑x' ::= ↑e'
    ⦃⌈r⌉⦄ := by
  refine quad_conseq ?_ (quad_assign_any _ x x' e e') fun _ _ h => h
  rintro m m' ⟨hne, hne', hall⟩
  refine ⟨hne.image _, hne'.image _, ?_⟩
  rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩
  exact hall s hs s' hs'

theorem quad_assign_left {r : State → State → Prop} (x : String) (e : State → Int) :
    ⦃⌈fun s s' => r (Function.update s x (e s)) s'⌉⦄ ↑x ::= ↑e ~ SKIP ⦃⌈r⌉⦄ := by
  rintro m m' ⟨hne, hne', hall⟩
  rw [semLift_assign, semLift_skip]
  refine ⟨hne.image _, hne', ?_⟩
  rintro _ ⟨s, hs, rfl⟩ t' ht'
  exact hall s hs t' ht'

/-! ## Choice -/

/-- Choice: both sides branch together; this is where `⊕` is born. -/
theorem quad_choice_sync (h₁ : ⦃R⦄ c₁ ~ c₁' ⦃S₁⦄) (h₂ : ⦃R⦄ c₂ ~ c₂' ⦃S₂⦄) :
    ⦃R⦄ c₁ + c₂ ~ c₁' + c₂' ⦃S₁ ⊕ₒ S₂⦄ := by
  intro m m' hm
  simp only [Cmd.add_def, semLift_choice]
  exact oplus_intro (h₁ _ _ hm) (h₂ _ _ hm)

/-- Choice-L: the passive side self-splits `X = X ∪ X` (needs overlap-friendly `⊕`). -/
theorem quad_choice_left (h₁ : ⦃R⦄ c₁ ~ c' ⦃S₁⦄) (h₂ : ⦃R⦄ c₂ ~ c' ⦃S₂⦄) :
    ⦃R⦄ c₁ + c₂ ~ c' ⦃S₁ ⊕ₒ S₂⦄ := by
  intro m m' hm
  simp only [Cmd.add_def, semLift_choice]
  rw [← Set.union_self (semLift c' m')]
  exact oplus_intro (h₁ _ _ hm) (h₂ _ _ hm)

theorem quad_choice_right (h₁ : ⦃R⦄ c ~ c₁' ⦃S₁⦄) (h₂ : ⦃R⦄ c ~ c₂' ⦃S₂⦄) :
    ⦃R⦄ c ~ c₁' + c₂' ⦃S₁ ⊕ₒ S₂⦄ := by
  have h := quad_sym (quad_choice_left (quad_sym h₁) (quad_sym h₂))
  rwa [RAssn.swap_swap, RAssn.swap_oplus, RAssn.swap_swap, RAssn.swap_swap] at h

/-- A quadruple survives adding branches once `⊕ ⊤` drops the new outcomes. -/
theorem quad_underapprox (h : ⦃R⦄ c ~ c' ⦃S⦄) : ⦃R⦄ c + d ~ c' ⦃S ⊕ₒ ⊤ₒ⦄ :=
  quad_choice_left h (quad_rtop R d c')

/-! ## Conditionals (uniform guards; mixed pre-models go through Split) -/

theorem quad_ite_pos (hb : ∀ m m', R m m' → (∀ s ∈ m, b s) ∧ (∀ s' ∈ m', b' s'))
    (h : ⦃R⦄ c₁ ~ c₁' ⦃S⦄) :
    ⦃R⦄ IF ↑b THEN c₁ ELSE c₂ END ~ IF ↑b' THEN c₁' ELSE c₂' END ⦃S⦄ := by
  intro m m' hm
  rw [semLift_ite_pos (hb m m' hm).1, semLift_ite_pos (hb m m' hm).2]
  exact h m m' hm

theorem quad_ite_neg (hb : ∀ m m', R m m' → (∀ s ∈ m, ¬ b s) ∧ (∀ s' ∈ m', ¬ b' s'))
    (h : ⦃R⦄ c₂ ~ c₂' ⦃S⦄) :
    ⦃R⦄ IF ↑b THEN c₁ ELSE c₂ END ~ IF ↑b' THEN c₁' ELSE c₂' END ⦃S⦄ := by
  intro m m' hm
  rw [semLift_ite_neg (hb m m' hm).1, semLift_ite_neg (hb m m' hm).2]
  exact h m m' hm

/-- If: the precondition is split by guard value (derived from Split). -/
theorem quad_ite (hb₁ : ∀ m m', R₁ m m' → (∀ s ∈ m, b s) ∧ (∀ s' ∈ m', b' s'))
    (hb₂ : ∀ m m', R₂ m m' → (∀ s ∈ m, ¬ b s) ∧ (∀ s' ∈ m', ¬ b' s'))
    (h₁ : ⦃R₁⦄ c₁ ~ c₁' ⦃S₁⦄) (h₂ : ⦃R₂⦄ c₂ ~ c₂' ⦃S₂⦄) :
    ⦃R₁ ⊕ₒ R₂⦄ IF ↑b THEN c₁ ELSE c₂ END ~ IF ↑b' THEN c₁' ELSE c₂' END ⦃S₁ ⊕ₒ S₂⦄ :=
  quad_split (quad_ite_pos hb₁ h₁) (quad_ite_neg hb₂ h₂)

theorem quad_ite_left_pos (hb : ∀ m m', R m m' → ∀ s ∈ m, b s) (h : ⦃R⦄ c₁ ~ c' ⦃S⦄) :
    ⦃R⦄ IF ↑b THEN c₁ ELSE c₂ END ~ c' ⦃S⦄ := by
  intro m m' hm
  rw [semLift_ite_pos (hb m m' hm)]
  exact h m m' hm

theorem quad_ite_left_neg (hb : ∀ m m', R m m' → ∀ s ∈ m, ¬ b s) (h : ⦃R⦄ c₂ ~ c' ⦃S⦄) :
    ⦃R⦄ IF ↑b THEN c₁ ELSE c₂ END ~ c' ⦃S⦄ := by
  intro m m' hm
  rw [semLift_ite_neg (hb m m' hm)]
  exact h m m' hm

/-! ## Loops -/

theorem quad_while_unroll_left
    (h : ⦃R⦄ IF ↑b THEN c ;; WHILE ↑b DO c END ELSE SKIP END ~ c' ⦃S⦄) :
    ⦃R⦄ WHILE ↑b DO c END ~ c' ⦃S⦄ := by
  intro m m' hm
  rw [semLift_while_eq_unroll b c]
  exact h m m' hm

theorem quad_while_unroll_right
    (h : ⦃R⦄ c ~ IF ↑b' THEN c' ;; WHILE ↑b' DO c' END ELSE SKIP END ⦃S⦄) :
    ⦃R⦄ c ~ WHILE ↑b' DO c' END ⦃S⦄ := by
  intro m m' hm
  rw [semLift_while_eq_unroll b' c']
  exact h m m' hm

/-- Fuel: an `⊕ ⊤` certificate on truncated loops transfers to the full loops. -/
theorem quad_while_fuel (n n' : ℕ)
    (h : ⟪R⟫ kleisli (loopIter b (sem c) n) , kleisli (loopIter b' (sem c') n') ⟪S ⊕ₒ ⊤ₒ⟫) :
    ⦃R⦄ WHILE ↑b DO c END ~ WHILE ↑b' DO c' END ⦃S ⊕ₒ ⊤ₒ⦄ := fun m m' hm =>
  oplus_top_mono (h m m' hm) (kleisli_mono_fun (fun s => loopIter_subset_sem b c n s) m)
    (kleisli_mono_fun (fun s => loopIter_subset_sem b' c' n' s) m')

/-- While-Inv: `I k` holds with `k` synchronised iterations remaining. -/
theorem quad_while_inv {I : ℕ → RAssn State State}
    (hpos : ∀ k m m', I (k + 1) m m' → (∀ s ∈ m, b s) ∧ (∀ s' ∈ m', b' s'))
    (hzero : ∀ m m', I 0 m m' → (∀ s ∈ m, ¬ b s) ∧ (∀ s' ∈ m', ¬ b' s'))
    (hbody : ∀ k, ⦃I (k + 1)⦄ c ~ c' ⦃I k⦄) (k : ℕ) :
    ⦃I k⦄ WHILE ↑b DO c END ~ WHILE ↑b' DO c' END ⦃I 0⦄ := by
  induction k with
  | zero =>
    intro m m' hm
    rwa [semLift_while_neg (hzero m m' hm).1, semLift_while_neg (hzero m m' hm).2]
  | succ k ih =>
    intro m m' hm
    rw [semLift_while_pos (hpos k m m' hm).1, semLift_while_pos (hpos k m m' hm).2]
    exact ih _ _ (hbody k m m' hm)

theorem quad_while_left {I : ℕ → RAssn State State}
    (hpos : ∀ k m m', I (k + 1) m m' → ∀ s ∈ m, b s)
    (hzero : ∀ m m', I 0 m m' → ∀ s ∈ m, ¬ b s)
    (hbody : ∀ k, ⦃I (k + 1)⦄ c ~ SKIP ⦃I k⦄) (k : ℕ) :
    ⦃I k⦄ WHILE ↑b DO c END ~ SKIP ⦃I 0⦄ := by
  induction k with
  | zero =>
    intro m m' hm
    rwa [semLift_while_neg (hzero m m' hm), semLift_skip]
  | succ k ih =>
    intro m m' hm
    rw [semLift_while_pos (hpos k m m' hm)]
    have hb := hbody k m m' hm
    rw [semLift_skip] at hb
    exact ih _ _ hb

/-- Any family of models of the `ψ n` unions to a model of `ψinf`. -/
def Converges (ψ : ℕ → RAssn α β) (ψinf : RAssn α β) : Prop :=
  ∀ (e : ℕ → Set α) (e' : ℕ → Set β), (∀ n, ψ n (e n) (e' n)) → ψinf (⋃ n, e n) (⋃ n, e' n)

private theorem loop_side_eq {b : State → Prop} {c : Cmd} (m e : ℕ → Set State)
    (hm : ∀ n, ∀ s ∈ m n, b s) (he : ∀ n, ∀ s ∈ e n, ¬ b s)
    (hstep : ∀ n, semLift c (m n) = m (n + 1) ∪ e (n + 1)) :
    semLift (.while b c) (m 0 ∪ e 0) = ⋃ n, e n := by
  have unroll : ∀ k, semLift (.while b c) (m k)
      = semLift (.while b c) (m (k + 1)) ∪ e (k + 1) := fun k => by
    rw [semLift_while_pos (hm k), hstep k, semLift_union, semLift_while_neg (he (k + 1))]
  have sub : ∀ k, semLift (.while b c) (m k) ⊆ semLift (.while b c) (m 0) := by
    intro k
    induction k with
    | zero => exact subset_rfl
    | succ k ih => exact fun t ht => ih (unroll k ▸ Set.mem_union_left _ ht)
  have key : ∀ j k, kleisli (loopIter b (sem c) j) (m k) ⊆ ⋃ n, e n := by
    intro j
    induction j with
    | zero => intro k t ht; simp at ht
    | succ j ih =>
      intro k t ht
      obtain ⟨s, hs, ht⟩ := mem_kleisli.mp ht
      rw [loopIter_succ_pos (hm k s hs)] at ht
      have ht' : t ∈ kleisli (loopIter b (sem c) j) (semLift c (m k)) :=
        kleisli_mono (fun u hu => mem_semLift.mpr ⟨s, hs, hu⟩) ht
      rw [hstep k, kleisli_union] at ht'
      rcases ht' with ht' | ht'
      · exact ih (k + 1) ht'
      · obtain ⟨u, hu, ht'⟩ := mem_kleisli.mp ht'
        cases j with
        | zero => simp at ht'
        | succ j =>
          rw [loopIter_succ_neg (he (k + 1) u hu), Set.mem_singleton_iff] at ht'
          exact Set.mem_iUnion.mpr ⟨k + 1, ht' ▸ hu⟩
  rw [semLift_union, semLift_while_neg (he 0)]
  apply Set.eq_of_subset_of_subset
  · rintro t (ht | ht)
    · obtain ⟨s, hs, ht⟩ := mem_semLift.mp ht
      obtain ⟨j, ht⟩ := Set.mem_iUnion.mp ht
      exact key j 0 (mem_kleisli.mpr ⟨s, hs, ht⟩)
    · exact Set.mem_iUnion.mpr ⟨0, ht⟩
  · refine Set.iUnion_subset fun n => ?_
    cases n with
    | zero => exact Set.subset_union_right
    | succ k => exact fun t ht => Or.inl (sub k (unroll k ▸ Set.mem_union_right _ ht))

/-- While-Fam: `φ n` still iterates after `n` steps, `ψ n` exits at step `n`.
Exhaustive and divergence-tolerant: no fuel, no `⊕ ⊤`, no termination premise. -/
theorem quad_while_fam {φ ψ : ℕ → RAssn State State} {ψinf : RAssn State State}
    (hφ : ∀ n m m', φ n m m' → (∀ s ∈ m, b s) ∧ (∀ s' ∈ m', b' s'))
    (hψ : ∀ n m m', ψ n m m' → (∀ s ∈ m, ¬ b s) ∧ (∀ s' ∈ m', ¬ b' s'))
    (hbody : ∀ n, ⦃φ n⦄ c ~ c' ⦃φ (n + 1) ⊕ₒ ψ (n + 1)⦄) (hconv : Converges ψ ψinf) :
    ⦃φ 0 ⊕ₒ ψ 0⦄ WHILE ↑b DO c END ~ WHILE ↑b' DO c' END ⦃ψinf⦄ := by
  rintro m m' ⟨m₀, e₀, m₀', e₀', rfl, rfl, h0, he0⟩
  have hstep : ∀ n (p : {p : Set State × Set State // φ n p.1 p.2}),
      ∃ q : {q : Set State × Set State // φ (n + 1) q.1 q.2} × (Set State × Set State),
        ψ (n + 1) q.2.1 q.2.2 ∧ semLift c p.1.1 = q.1.1.1 ∪ q.2.1 ∧
          semLift c' p.1.2 = q.1.1.2 ∪ q.2.2 := by
    intro n ⟨⟨mn, mn'⟩, hp⟩
    obtain ⟨m₁, e, m₁', e', hm, hm', hφ', hψ'⟩ := hbody n mn mn' hp
    exact ⟨(⟨(m₁, m₁'), hφ'⟩, (e, e')), hψ', hm, hm'⟩
  choose nxt hnxt using hstep
  let chain : (n : ℕ) → {p : Set State × Set State // φ n p.1 p.2} :=
    fun n => Nat.rec ⟨(m₀, m₀'), h0⟩ (fun k acc => (nxt k acc).1) n
  let e : ℕ → Set State := fun n => Nat.casesOn n e₀ fun k => (nxt k (chain k)).2.1
  let e' : ℕ → Set State := fun n => Nat.casesOn n e₀' fun k => (nxt k (chain k)).2.2
  have hψe : ∀ n, ψ n (e n) (e' n) := fun n => by
    cases n with
    | zero => exact he0
    | succ k => exact (hnxt k (chain k)).1
  have hL : semLift (.while b c) (m₀ ∪ e₀) = ⋃ n, e n :=
    loop_side_eq (fun n => (chain n).1.1) e (fun n => (hφ n _ _ (chain n).2).1)
      (fun n => (hψ n _ _ (hψe n)).1) fun n => (hnxt n (chain n)).2.1
  have hR : semLift (.while b' c') (m₀' ∪ e₀') = ⋃ n, e' n :=
    loop_side_eq (fun n => (chain n).1.2) e' (fun n => (hφ n _ _ (chain n).2).2)
      (fun n => (hψ n _ _ (hψe n)).2) fun n => (hnxt n (chain n)).2.2
  rw [hL, hR]
  exact hconv e e' hψe

end Commands

/-! ## Coupling tier -/

/-- C-Lift: over Kleisli lifts a coupling quadruple is exactly its singleton instances. -/
theorem quadSem_couple_lift_iff {r : α → β → Prop} {r' : γ → δ → Prop}
    {k : α → Set γ} {k' : β → Set δ} :
    ⟪couple r⟫ kleisli k , kleisli k' ⟪couple r'⟫ ↔ ∀ x y, r x y → couple r' (k x) (k' y) := by
  refine ⟨fun h x y hr => ?_, fun h _ _ hm => couple_bind hm h⟩
  have := h {x} {y} (couple_singleton_iff.mpr hr)
  rwa [kleisli_singleton, kleisli_singleton] at this

theorem quadSem_coupleL_lift_iff {r : α → β → Prop} {r' : γ → δ → Prop}
    {k : α → Set γ} {k' : β → Set δ} :
    ⟪coupleL r⟫ kleisli k , kleisli k' ⟪coupleL r'⟫ ↔
      ∀ x y, r x y → coupleL r' (k x) (k' y) := by
  refine ⟨fun h x y hr => ?_, fun h _ _ hm => coupleL_bind hm h⟩
  have := h {x} {y} (coupleL_singleton_iff.mpr hr)
  rwa [kleisli_singleton, kleisli_singleton] at this

theorem quadSem_atom_iff {r : α → β → Prop} {r' : γ → δ → Prop}
    {k : α → Set γ} {k' : β → Set δ} :
    ⟪atom r⟫ kleisli k , kleisli k' ⟪atom r'⟫ ↔ ∀ x y, r x y → atom r' (k x) (k' y) := by
  constructor
  · intro h x y hr
    have := h {x} {y} (atom_singleton_iff.mpr hr)
    rwa [kleisli_singleton, kleisli_singleton] at this
  · rintro h m m' ⟨⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩, hall⟩
    obtain ⟨⟨t, ht⟩, ⟨t', ht'⟩, -⟩ := h x₀ y₀ (hall x₀ hx₀ y₀ hy₀)
    refine ⟨⟨t, mem_kleisli.mpr ⟨x₀, hx₀, ht⟩⟩, ⟨t', mem_kleisli.mpr ⟨y₀, hy₀, ht'⟩⟩, ?_⟩
    intro u hu v hv
    obtain ⟨x, hx, hu⟩ := mem_kleisli.mp hu
    obtain ⟨y, hy, hv⟩ := mem_kleisli.mp hv
    exact (h x y (hall x hx y hy)).2.2 u hu v hv

section Coupling

variable {r r' : State → State → Prop} {c c' c₁ c₂ c₁' c₂' : Cmd} {b b' : State → Prop}

theorem quad_couple_lift_iff :
    ⦃couple r⦄ c ~ c' ⦃couple r'⦄ ↔ ∀ s s', r s s' → couple r' (sem c s) (sem c' s') :=
  quadSem_couple_lift_iff

theorem quad_coupleL_lift_iff :
    ⦃coupleL r⦄ c ~ c' ⦃coupleL r'⦄ ↔ ∀ s s', r s s' → coupleL r' (sem c s) (sem c' s') :=
  quadSem_coupleL_lift_iff

theorem quad_atom_iff :
    ⦃atom r⦄ c ~ c' ⦃atom r'⦄ ↔ ∀ s s', r s s' → atom r' (sem c s) (sem c' s') :=
  quadSem_atom_iff

/-- Bitotal = left-total ∧ right-total; the two directions may use different mid-relations. -/
theorem quad_couple_of_LR (hL : ⦃coupleL r⦄ c ~ c' ⦃coupleL r'⦄)
    (hR : ⦃coupleR r⦄ c ~ c' ⦃coupleR r'⦄) : ⦃couple r⦄ c ~ c' ⦃couple r'⦄ :=
  fun m m' hm => ⟨hL m m' hm.1, hR m m' hm.2⟩

/-- An unsatisfiable coupling holds only of `(∅, ∅)`, from which every coupling follows. -/
theorem quad_couple_false {p : State → State → Prop} (hp : ∀ s s', ¬ p s s') :
    ⦃couple p⦄ c ~ c' ⦃couple r'⦄ :=
  quad_couple_lift_iff.mpr fun s s' h => (hp s s' h).elim

theorem quad_assign_couple (x x' : String) (e e' : State → Int) :
    ⦃couple fun s s' => r (Function.update s x (e s)) (Function.update s' x' (e' s'))⦄
      ↑x ::= ↑e ~ ↑x' ::= ↑e'
    ⦃couple r⦄ :=
  quad_couple_lift_iff.mpr fun s s' hr => by
    rw [sem_assign, sem_assign]
    exact couple_singleton_iff.mpr hr

private theorem oplus_couple_self (r : α → β → Prop) : couple r ⊕ₒ couple r ⟹ₒ couple r := by
  rw [oplus_couple_eq]
  exact couple_mono fun _ _ h => h.elim id id

/-- C-Choice: Choice followed by the `⊕`-collapse; the post needs no `⊕`. -/
theorem quad_choice_couple (h₁ : ⦃couple r⦄ c₁ ~ c₁' ⦃couple r'⦄)
    (h₂ : ⦃couple r⦄ c₂ ~ c₂' ⦃couple r'⦄) : ⦃couple r⦄ c₁ + c₂ ~ c₁' + c₂' ⦃couple r'⦄ :=
  quad_conseq (fun _ _ h => h) (quad_choice_sync h₁ h₂) (oplus_couple_self r')

theorem quad_choice_left_couple (h₁ : ⦃couple r⦄ c₁ ~ c' ⦃couple r'⦄)
    (h₂ : ⦃couple r⦄ c₂ ~ c' ⦃couple r'⦄) : ⦃couple r⦄ c₁ + c₂ ~ c' ⦃couple r'⦄ :=
  quad_conseq (fun _ _ h => h) (quad_choice_left h₁ h₂) (oplus_couple_self r')

/-- C-If, four-way: no guard synchronisation. -/
theorem quad_ite_couple_async
    (h₁₁ : ⦃couple fun s s' => r s s' ∧ b s ∧ b' s'⦄ c₁ ~ c₁' ⦃couple r'⦄)
    (h₁₂ : ⦃couple fun s s' => r s s' ∧ b s ∧ ¬ b' s'⦄ c₁ ~ c₂' ⦃couple r'⦄)
    (h₂₁ : ⦃couple fun s s' => r s s' ∧ ¬ b s ∧ b' s'⦄ c₂ ~ c₁' ⦃couple r'⦄)
    (h₂₂ : ⦃couple fun s s' => r s s' ∧ ¬ b s ∧ ¬ b' s'⦄ c₂ ~ c₂' ⦃couple r'⦄) :
    ⦃couple r⦄ IF ↑b THEN c₁ ELSE c₂ END ~ IF ↑b' THEN c₁' ELSE c₂' END ⦃couple r'⦄ := by
  rw [quad_couple_lift_iff] at h₁₁ h₁₂ h₂₁ h₂₂ ⊢
  intro s s' hr
  by_cases hb : b s <;> by_cases hb' : b' s'
  · rw [sem_ite_pos hb, sem_ite_pos hb']; exact h₁₁ s s' ⟨hr, hb, hb'⟩
  · rw [sem_ite_pos hb, sem_ite_neg hb']; exact h₁₂ s s' ⟨hr, hb, hb'⟩
  · rw [sem_ite_neg hb, sem_ite_pos hb']; exact h₂₁ s s' ⟨hr, hb, hb'⟩
  · rw [sem_ite_neg hb, sem_ite_neg hb']; exact h₂₂ s s' ⟨hr, hb, hb'⟩

/-- C-If, synchronised: the mixed premises are discharged by `quad_couple_false`. -/
theorem quad_ite_couple (hguard : ∀ s s', r s s' → (b s ↔ b' s'))
    (h₁ : ⦃couple fun s s' => r s s' ∧ b s ∧ b' s'⦄ c₁ ~ c₁' ⦃couple r'⦄)
    (h₂ : ⦃couple fun s s' => r s s' ∧ ¬ b s ∧ ¬ b' s'⦄ c₂ ~ c₂' ⦃couple r'⦄) :
    ⦃couple r⦄ IF ↑b THEN c₁ ELSE c₂ END ~ IF ↑b' THEN c₁' ELSE c₂' END ⦃couple r'⦄ :=
  quad_ite_couple_async h₁
    (quad_couple_false fun s s' ⟨hr, hb, hb'⟩ => hb' ((hguard s s' hr).mp hb))
    (quad_couple_false fun s s' ⟨hr, hb, hb'⟩ => hb ((hguard s s' hr).mpr hb')) h₂

/-- C-While: no fuel, no `⊕ ⊤`, no termination premise. -/
theorem quad_while_couple (hguard : ∀ s s', r s s' → (b s ↔ b' s'))
    (hbody : ⦃couple fun s s' => r s s' ∧ b s ∧ b' s'⦄ c ~ c' ⦃couple r⦄) :
    ⦃couple r⦄ WHILE ↑b DO c END ~ WHILE ↑b' DO c' END
      ⦃couple fun t t' => r t t' ∧ ¬ b t ∧ ¬ b' t'⦄ :=
  quad_couple_lift_iff.mpr fun s s' hr => loopSem_couple hguard
    (fun x y h hb hb' => quad_couple_lift_iff.mp hbody x y ⟨h, hb, hb'⟩) s s' hr

theorem quad_while_coupleL (hguard : ∀ s s', r s s' → (b s ↔ b' s'))
    (hbody : ⦃coupleL fun s s' => r s s' ∧ b s ∧ b' s'⦄ c ~ c' ⦃coupleL r⦄) :
    ⦃coupleL r⦄ WHILE ↑b DO c END ~ WHILE ↑b' DO c' END
      ⦃coupleL fun t t' => r t t' ∧ ¬ b t ∧ ¬ b' t'⦄ :=
  quad_coupleL_lift_iff.mpr fun s s' hr => loopSem_coupleL hguard
    (fun x y h hb hb' => quad_coupleL_lift_iff.mp hbody x y ⟨h, hb, hb'⟩) s s' hr

/-! ### One-sided loops -/

private theorem loopIter_left_inv {s' : State}
    (hpres : ∀ s, r s s' → b s → ∀ t ∈ sem c s, r t s') :
    ∀ n s, r s s' → ∀ t ∈ loopIter b (sem c) n s, r t s' ∧ ¬ b t := by
  intro n
  induction n with
  | zero => intro s _ t ht; simp at ht
  | succ n ih =>
    intro s hr t ht
    by_cases hb : b s
    · rw [loopIter_succ_pos hb] at ht
      obtain ⟨u, hu, ht⟩ := mem_kleisli.mp ht
      exact ih u (hpres s hr hb u hu) t ht
    · rw [loopIter_succ_neg hb, Set.mem_singleton_iff] at ht
      exact ht ▸ ⟨hr, hb⟩

/-- ∀∃, loop on the ∀-side: no termination premise. -/
theorem quad_while_left_coupleL
    (hbody : ⦃coupleL fun s s' => r s s' ∧ b s⦄ c ~ SKIP ⦃coupleL r⦄) :
    ⦃coupleL r⦄ WHILE ↑b DO c END ~ SKIP ⦃coupleL fun t t' => r t t' ∧ ¬ b t⦄ := by
  rw [quad_coupleL_lift_iff] at hbody ⊢
  intro s s' hr t ht
  obtain ⟨n, ht⟩ := Set.mem_iUnion.mp ht
  refine ⟨s', rfl, loopIter_left_inv (fun s hr hb u hu => ?_) n s hr t ht⟩
  obtain ⟨v, hv, hru⟩ := hbody s s' ⟨hr, hb⟩ u hu
  exact (Set.mem_singleton_iff.mp hv) ▸ hru

/-- Bitotal, loop on one side: some run must terminate (variant `V`). -/
theorem quad_while_left_couple (V : State → ℕ)
    (hpres : ∀ s s', r s s' → b s → ∀ t ∈ sem c s, r t s')
    (hdec : ∀ s s', r s s' → b s → ∃ t ∈ sem c s, V t < V s) :
    ⦃couple r⦄ WHILE ↑b DO c END ~ SKIP ⦃couple fun t t' => r t t' ∧ ¬ b t⦄ := by
  rw [quad_couple_lift_iff]
  intro s s' hr
  rw [sem_skip]
  constructor
  · intro t ht
    obtain ⟨n, ht⟩ := Set.mem_iUnion.mp ht
    exact ⟨s', rfl, loopIter_left_inv (fun s hr hb => hpres s s' hr hb) n s hr t ht⟩
  · rintro y rfl
    have aux : ∀ k s, V s = k → r s y → ∃ t ∈ sem (.while b c) s, r t y ∧ ¬ b t := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro s hk hr
        by_cases hb : b s
        · obtain ⟨u, hu, hV⟩ := hdec s y hr hb
          obtain ⟨t, ht, hprop⟩ := ih (V u) (hk ▸ hV) u rfl (hpres s y hr hb u hu)
          exact ⟨t, by rw [sem_while_pos hb]; exact mem_semLift.mpr ⟨u, hu, ht⟩, hprop⟩
        · exact ⟨s, by rw [sem_while_neg hb]; rfl, hr, hb⟩
    exact aux (V s) s rfl hr

/-- The termination premise above is necessary. -/
theorem quad_while_left_couple_needs_termination :
    ¬ ⦃couple fun _ _ => True⦄ WHILE True DO SKIP END ~ SKIP ⦃couple fun _ _ => True⦄ := by
  intro h
  obtain ⟨x, hx, -⟩ :=
    (quad_couple_lift_iff.mp h (fun _ => 0) (fun _ => 0) trivial).2 (fun _ => 0) (by simp)
  rw [sem_while_true] at hx
  exact hx

end Coupling

/-! ## Worked example: Choice creates an `⊕`, only Split can open it -/

example :
    ⦃⌈True⌉⦄
      (x ::= 1) + (x ::= 2) ;; y ::= x ~ (x ::= 1) + (x ::= 2) ;; y ::= x
    ⦃⌈y = 1 ∧ y' = 1⌉ ⊕ₒ ⌈y = 2 ∧ y' = 2⌉⦄ := by
  have d₁ : ⦃⌈True⌉⦄ x ::= 1 ~ x ::= 1 ⦃⌈x = 1 ∧ x' = 1⌉⦄ :=
    quad_conseq (fun _ _ h => ⟨h.1, h.2.1, by simp⟩) (quad_assign "x" "x" _ _) fun _ _ h => h
  have d₂ : ⦃⌈True⌉⦄ x ::= 2 ~ x ::= 2 ⦃⌈x = 2 ∧ x' = 2⌉⦄ :=
    quad_conseq (fun _ _ h => ⟨h.1, h.2.1, by simp⟩) (quad_assign "x" "x" _ _) fun _ _ h => h
  have e₁ : ⦃⌈x = 1 ∧ x' = 1⌉⦄ y ::= x ~ y ::= x ⦃⌈y = 1 ∧ y' = 1⌉⦄ :=
    quad_conseq (fun _ _ h => ⟨h.1, h.2.1, fun s hs s' hs' => by simpa using h.2.2 s hs s' hs'⟩)
      (quad_assign "y" "y" _ _) fun _ _ h => h
  have e₂ : ⦃⌈x = 2 ∧ x' = 2⌉⦄ y ::= x ~ y ::= x ⦃⌈y = 2 ∧ y' = 2⌉⦄ :=
    quad_conseq (fun _ _ h => ⟨h.1, h.2.1, fun s hs s' hs' => by simpa using h.2.2 s hs s' hs'⟩)
      (quad_assign "y" "y" _ _) fun _ _ h => h
  exact quad_seq (quad_choice_sync d₁ d₂) (quad_split e₁ e₂)

end RelOL
