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

/-- One-sided Choice on the right, derived from `Choice-L` via `Sym` (closing
the "derivable" claim in the paper's rule figure). -/
theorem quad_choice_right {R S₁ S₂ : RAssn State State} {c c₁' c₂' : Cmd}
    (h₁ : ⦃R⦄ c ~ c₁' ⦃S₁⦄) (h₂ : ⦃R⦄ c ~ c₂' ⦃S₂⦄) :
    ⦃R⦄ c ~ Cmd.choice c₁' c₂' ⦃S₁ ⊕ₒ S₂⦄ := by
  have h := quad_sym (quad_choice_left (quad_sym h₁) (quad_sym h₂))
  rwa [RAssn.swap_swap, RAssn.swap_oplus, RAssn.swap_swap, RAssn.swap_swap] at h

/-! ## Atomic axioms and conditional rules -/

/-- Synchronized assignment axiom, Floyd-style forward form on atoms. -/
theorem quad_assign {r : State → State → Prop} (x x' : String) (e e' : State → Int) :
    ⦃atom fun s s' => r (Function.update s x (e s)) (Function.update s' x' (e' s'))⦄
      Cmd.assign x e ~ Cmd.assign x' e' ⦃atom r⦄ := by
  rintro m m' ⟨⟨s₀, hs₀⟩, ⟨s₀', hs₀'⟩, hall⟩
  rw [semLift_assign, semLift_assign]
  refine ⟨⟨_, Set.mem_image_of_mem _ hs₀⟩, ⟨_, Set.mem_image_of_mem _ hs₀'⟩, ?_⟩
  rintro t ⟨s, hs, rfl⟩ t' ⟨s', hs', rfl⟩
  exact hall s hs s' hs'

/-- One-sided assignment: the left program assigns, the right stays put. -/
theorem quad_assign_left {r : State → State → Prop} (x : String) (e : State → Int) :
    ⦃atom fun s s' => r (Function.update s x (e s)) s'⦄
      Cmd.assign x e ~ Cmd.skip ⦃atom r⦄ := by
  rintro m m' ⟨⟨s₀, hs₀⟩, hne', hall⟩
  rw [semLift_assign, semLift_skip]
  refine ⟨⟨_, Set.mem_image_of_mem _ hs₀⟩, hne', ?_⟩
  rintro t ⟨s, hs, rfl⟩ t' ht'
  exact hall s hs t' ht'

/-- Synchronized conditional, both guards uniformly true on the pre-models. The
uniformly-false variant is `quad_ite_neg`; mixed pre-models are handled by
splitting the precondition with `quad_split`. -/
theorem quad_ite_pos {R S : RAssn State State} {b b' : State → Prop}
    {c₁ c₂ c₁' c₂' : Cmd}
    (hb : ∀ m m', R m m' → (∀ s ∈ m, b s) ∧ (∀ s' ∈ m', b' s'))
    (h : ⦃R⦄ c₁ ~ c₁' ⦃S⦄) :
    ⦃R⦄ Cmd.ite b c₁ c₂ ~ Cmd.ite b' c₁' c₂' ⦃S⦄ := by
  intro m m' hm
  obtain ⟨h₁, h₂⟩ := hb m m' hm
  rw [semLift_ite_pos h₁, semLift_ite_pos h₂]
  exact h m m' hm

theorem quad_ite_neg {R S : RAssn State State} {b b' : State → Prop}
    {c₁ c₂ c₁' c₂' : Cmd}
    (hb : ∀ m m', R m m' → (∀ s ∈ m, ¬ b s) ∧ (∀ s' ∈ m', ¬ b' s'))
    (h : ⦃R⦄ c₂ ~ c₂' ⦃S⦄) :
    ⦃R⦄ Cmd.ite b c₁ c₂ ~ Cmd.ite b' c₁' c₂' ⦃S⦄ := by
  intro m m' hm
  obtain ⟨h₁, h₂⟩ := hb m m' hm
  rw [semLift_ite_neg h₁, semLift_ite_neg h₂]
  exact h m m' hm

/-- One-sided conditional: only the left program branches. -/
theorem quad_ite_left_pos {R S : RAssn State State} {b : State → Prop}
    {c₁ c₂ c' : Cmd} (hb : ∀ m m', R m m' → ∀ s ∈ m, b s)
    (h : ⦃R⦄ c₁ ~ c' ⦃S⦄) : ⦃R⦄ Cmd.ite b c₁ c₂ ~ c' ⦃S⦄ := by
  intro m m' hm
  rw [semLift_ite_pos (hb m m' hm)]
  exact h m m' hm

theorem quad_ite_left_neg {R S : RAssn State State} {b : State → Prop}
    {c₁ c₂ c' : Cmd} (hb : ∀ m m', R m m' → ∀ s ∈ m, ¬ b s)
    (h : ⦃R⦄ c₂ ~ c' ⦃S⦄) : ⦃R⦄ Cmd.ite b c₁ c₂ ~ c' ⦃S⦄ := by
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

/-- The loop equals its one-step unrolling (left side). -/
theorem quad_while_unroll_left {R S : RAssn State State} {b : State → Prop}
    {c c' : Cmd}
    (h : ⦃R⦄ Cmd.ite b (Cmd.seq c (Cmd.while b c)) Cmd.skip ~ c' ⦃S⦄) :
    ⦃R⦄ Cmd.while b c ~ c' ⦃S⦄ := by
  intro m m' hm
  have hs := h m m' hm
  rwa [show semLift (Cmd.ite b (Cmd.seq c (Cmd.while b c)) Cmd.skip) m
      = semLift (Cmd.while b c) m from by
    unfold semLift; rw [← sem_while_eq_unroll]] at hs

/-- The loop equals its one-step unrolling (right side). -/
theorem quad_while_unroll_right {R S : RAssn State State} {b' : State → Prop}
    {c c' : Cmd}
    (h : ⦃R⦄ c ~ Cmd.ite b' (Cmd.seq c' (Cmd.while b' c')) Cmd.skip ⦃S⦄) :
    ⦃R⦄ c ~ Cmd.while b' c' ⦃S⦄ := by
  intro m m' hm
  have hs := h m m' hm
  rwa [show semLift (Cmd.ite b' (Cmd.seq c' (Cmd.while b' c')) Cmd.skip) m'
      = semLift (Cmd.while b' c') m' from by
    unfold semLift; rw [← sem_while_eq_unroll]] at hs

/-- **Fuel rule**: an under-approximate (`⊕ ⊤`) certificate proved against
fuel-truncated loops transfers to the full loops — the truncations
under-approximate the loop semantics, and `⊕ ⊤` absorbs the rest. -/
theorem quad_while_fuel {R S : RAssn State State} {b b' : State → Prop}
    {c c' : Cmd} (n n' : ℕ)
    (h : quadSem (kleisli (loopIter b (sem c) n)) (kleisli (loopIter b' (sem c') n'))
      R (S ⊕ₒ rtop)) :
    ⦃R⦄ Cmd.while b c ~ Cmd.while b' c' ⦃S ⊕ₒ rtop⦄ := by
  intro m m' hm
  refine oplus_top_mono (h m m' hm) ?_ ?_
  · exact kleisli_mono_fun (fun s => loopIter_subset_sem b c n s) m
  · exact kleisli_mono_fun (fun s => loopIter_subset_sem b' c' n' s) m'

/-- **Ranked-invariant rule** (exhaustive reading): `I k` is the relational
invariant with `k` synchronized iterations remaining; the rank decides both
guards uniformly, so both loops terminate in exactly the rank's iterations and
divergence never enters. -/
theorem quad_while_inv {I : ℕ → RAssn State State} {b b' : State → Prop}
    {c c' : Cmd}
    (hpos : ∀ k m m', I (k + 1) m m' → (∀ s ∈ m, b s) ∧ (∀ s' ∈ m', b' s'))
    (hzero : ∀ m m', I 0 m m' → (∀ s ∈ m, ¬ b s) ∧ (∀ s' ∈ m', ¬ b' s'))
    (hbody : ∀ k, ⦃I (k + 1)⦄ c ~ c' ⦃I k⦄) (k : ℕ) :
    ⦃I k⦄ Cmd.while b c ~ Cmd.while b' c' ⦃I 0⦄ := by
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

/-- One-sided ranked While: the left program loops, the right stays put. -/
theorem quad_while_left {I : ℕ → RAssn State State} {b : State → Prop} {c : Cmd}
    (hpos : ∀ k m m', I (k + 1) m m' → ∀ s ∈ m, b s)
    (hzero : ∀ m m', I 0 m m' → ∀ s ∈ m, ¬ b s)
    (hbody : ∀ k, ⦃I (k + 1)⦄ c ~ Cmd.skip ⦃I k⦄) (k : ℕ) :
    ⦃I k⦄ Cmd.while b c ~ Cmd.skip ⦃I 0⦄ := by
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
