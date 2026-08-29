import RelationalOutcomeLogic.Rules

/-!
# Relational Hoare Logic is the weak-atom fragment of RelOL

`rhl r c c' r'` is the Benton-style relational Hoare judgment in its
partial-correctness, ∀∀ reading (every pair of terminating runs from
`r`-related states ends `r'`-related; nondeterminism is universally
quantified, divergence claims nothing).

* `rhl_iff_quad` — the exact bridge: RHL **is** the `atomW`-to-`atomW`
  quadruple. No side conditions, loops included: `atomW` is divergence-closed,
  which is precisely what RHL's partial reading requires. (`atom` would build
  in a joint-termination claim RHL does not make — that upgrade is
  `rhl_iff_quad_atom`, for the loop-free fragment.)
* `rhl_singleton_iff` — the pointwise reformulation over singleton
  preconditions.
* Benton's core rules (`Skip`, `Assign`, `Seq`, `Conseq`, synchronized `If`,
  synchronized partial `While`) all derive — `Seq` and `Conseq` directly
  through the bridge from the relational rules.
-/

namespace RelOL

/-- Benton-style relational Hoare judgment: ∀∀ over terminating runs, partial
correctness. -/
def rhl (r : State → State → Prop) (c c' : Cmd) (r' : State → State → Prop) : Prop :=
  ∀ s s', r s s' → ∀ t ∈ sem c s, ∀ t' ∈ sem c' s', r' t t'

/-- **RHL subsumption**: the relational Hoare judgment is exactly the RelOL
quadruple between weak atoms. -/
theorem rhl_iff_quad {r r' : State → State → Prop} {c c' : Cmd} :
    rhl r c c' r' ↔ ⦃atomW r⦄ c ~ c' ⦃atomW r'⦄ := by
  constructor
  · intro h m m' hall t ht t' ht'
    obtain ⟨s, hs, ht⟩ := mem_semLift.mp ht
    obtain ⟨s', hs', ht'⟩ := mem_semLift.mp ht'
    exact h s s' (hall s hs s' hs') t ht t' ht'
  · intro h s s' hr t ht t' ht'
    have hq := h {s} {s'} (by simpa using hr)
    rw [semLift_singleton, semLift_singleton] at hq
    exact hq t ht t' ht'

/-- The singleton-precondition family form of the bridge. -/
theorem rhl_singleton_iff {r r' : State → State → Prop} {c c' : Cmd} :
    rhl r c c' r' ↔ ∀ s s', r s s' →
      ⦃fun m m' => m = {s} ∧ m' = {s'}⦄ c ~ c' ⦃atomW r'⦄ := by
  constructor
  · rintro h s s' hr m m' ⟨rfl, rfl⟩
    rw [semLift_singleton, semLift_singleton]
    exact fun t ht t' ht' => h s s' hr t ht t' ht'
  · intro h s s' hr t ht t' ht'
    have hq := h s s' hr {s} {s'} ⟨rfl, rfl⟩
    rw [semLift_singleton, semLift_singleton] at hq
    exact hq t ht t' ht'

/-- Loop-free upgrade: for terminating programs the weak atom strengthens to
the reachability-bearing `atom`, i.e. RHL-partial and the exhaustive RelOL
reading coincide. -/
theorem rhl_iff_quad_atom {r r' : State → State → Prop} {c c' : Cmd}
    (hc : LoopFree c) (hc' : LoopFree c') :
    rhl r c c' r' ↔ ∀ s s', r s s' →
      ⦃fun m m' => m = {s} ∧ m' = {s'}⦄ c ~ c' ⦃atom r'⦄ := by
  rw [rhl_singleton_iff]
  constructor
  · rintro h s s' hr m m' ⟨rfl, rfl⟩
    refine ⟨?_, ?_, h s s' hr {s} {s'} ⟨rfl, rfl⟩⟩
    · rw [semLift_singleton]; exact sem_nonempty hc s
    · rw [semLift_singleton]; exact sem_nonempty hc' s'
  · rintro h s s' hr m m' ⟨rfl, rfl⟩
    exact (h s s' hr {s} {s'} ⟨rfl, rfl⟩).2.2

/-! ## Benton's core rules, through the bridge -/

theorem rhl_skip (r : State → State → Prop) : rhl r .skip .skip r := by
  rw [rhl_iff_quad]
  intro m m' hm
  rwa [semLift_skip, semLift_skip]

theorem rhl_conseq {r₀ r r' r₁ : State → State → Prop} {c c' : Cmd}
    (hpre : ∀ s s', r₀ s s' → r s s') (h : rhl r c c' r')
    (hpost : ∀ t t', r' t t' → r₁ t t') : rhl r₀ c c' r₁ := by
  rw [rhl_iff_quad] at h ⊢
  exact quadSem_conseq (atomW_mono hpre) h (atomW_mono hpost)

theorem rhl_assign {r' : State → State → Prop} (x x' : String)
    (e e' : State → Int) :
    rhl (fun s s' => r' (Function.update s x (e s)) (Function.update s' x' (e' s')))
      (.assign x e) (.assign x' e') r' := by
  intro s s' hr t ht t' ht'
  simp only [sem_assign, Set.mem_singleton_iff] at ht ht'
  subst ht ht'
  exact hr

/-- Benton's sequencing rule: an instance of relational `Seq` through the
bridge, with the weak-atom midcondition. -/
theorem rhl_seq {r rm r' : State → State → Prop} {c₁ c₂ c₁' c₂' : Cmd}
    (h₁ : rhl r c₁ c₁' rm) (h₂ : rhl rm c₂ c₂' r') :
    rhl r (.seq c₁ c₂) (.seq c₁' c₂') r' := by
  rw [rhl_iff_quad] at h₁ h₂ ⊢
  exact quad_seq h₁ h₂

/-- Benton's synchronized conditional: pointwise guard agreement. -/
theorem rhl_ite {r r' : State → State → Prop} {b b' : State → Prop}
    {c₁ c₂ c₁' c₂' : Cmd}
    (hguard : ∀ s s', r s s' → (b s ↔ b' s'))
    (h₁ : rhl (fun s s' => r s s' ∧ b s ∧ b' s') c₁ c₁' r')
    (h₂ : rhl (fun s s' => r s s' ∧ ¬ b s ∧ ¬ b' s') c₂ c₂' r') :
    rhl r (.ite b c₁ c₂) (.ite b' c₁' c₂') r' := by
  intro s s' hr t ht t' ht'
  by_cases hb : b s
  · have hb' : b' s' := (hguard s s' hr).mp hb
    rw [sem_ite_pos hb] at ht
    rw [sem_ite_pos hb'] at ht'
    exact h₁ s s' ⟨hr, hb, hb'⟩ t ht t' ht'
  · have hb' : ¬ b' s' := fun h => hb ((hguard s s' hr).mpr h)
    rw [sem_ite_neg hb] at ht
    rw [sem_ite_neg hb'] at ht'
    exact h₂ s s' ⟨hr, hb, hb'⟩ t ht t' ht'

/-- Benton's synchronized `While`, partial-correctness reading: a relational
invariant with pointwise-agreeing guards. No termination premise — divergent
runs contribute no outcomes, which the ∀∀ reading (equivalently, the weak
atom) absorbs. -/
theorem rhl_while {r : State → State → Prop} {b b' : State → Prop} {c c' : Cmd}
    (hguard : ∀ s s', r s s' → (b s ↔ b' s'))
    (hbody : rhl (fun s s' => r s s' ∧ b s ∧ b' s') c c' r) :
    rhl r (.while b c) (.while b' c')
      (fun t t' => r t t' ∧ ¬ b t ∧ ¬ b' t') := by
  have aux : ∀ n n' (s s' : State), r s s' →
      ∀ t ∈ loopIter b (sem c) n s, ∀ t' ∈ loopIter b' (sem c') n' s',
        r t t' ∧ ¬ b t ∧ ¬ b' t' := by
    intro n
    induction n with
    | zero => intro n' s s' _ t ht; simp at ht
    | succ n ih =>
      intro n' s s' hr t ht t' ht'
      by_cases hb : b s
      · have hb' : b' s' := (hguard s s' hr).mp hb
        rw [loopIter_succ_pos hb] at ht
        obtain ⟨u, hu, ht⟩ := mem_kleisli.mp ht
        cases n' with
        | zero => simp at ht'
        | succ n' =>
          rw [loopIter_succ_pos hb'] at ht'
          obtain ⟨u', hu', ht'⟩ := mem_kleisli.mp ht'
          exact ih n' u u' (hbody s s' ⟨hr, hb, hb'⟩ u hu u' hu') t ht t' ht'
      · have hb' : ¬ b' s' := fun h => hb ((hguard s s' hr).mpr h)
        rw [loopIter_succ_neg hb] at ht
        cases n' with
        | zero => simp at ht'
        | succ n' =>
          rw [loopIter_succ_neg hb'] at ht'
          simp only [Set.mem_singleton_iff] at ht ht'
          subst ht ht'
          exact ⟨hr, hb, hb'⟩
  intro s s' hr t ht t' ht'
  rw [sem_while] at ht ht'
  obtain ⟨n, ht⟩ := Set.mem_iUnion.mp ht
  obtain ⟨n', ht'⟩ := Set.mem_iUnion.mp ht'
  exact aux n n' s s' hr t ht t' ht'

end RelOL
