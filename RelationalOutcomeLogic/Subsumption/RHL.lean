import RelationalOutcomeLogic.Rules

/-! # Relational Hoare Logic is the weak-atom fragment of RelOL -/

namespace RelOL

/-- Benton-style relational Hoare judgment. -/
def rhl (r : State → State → Prop) (c c' : Cmd) (r' : State → State → Prop) : Prop :=
  ∀ s s', r s s' → ∀ t ∈ sem c s, ∀ t' ∈ sem c' s', r' t t'

/-- RHL subsumption. -/
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

/-- Loop-free upgrade. -/
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

/-- Benton's sequencing rule. -/
theorem rhl_seq {r rm r' : State → State → Prop} {c₁ c₂ c₁' c₂' : Cmd}
    (h₁ : rhl r c₁ c₁' rm) (h₂ : rhl rm c₂ c₂' r') :
    rhl r (.seq c₁ c₂) (.seq c₁' c₂') r' := by
  rw [rhl_iff_quad] at h₁ h₂ ⊢
  exact quad_seq h₁ h₂

/-- Benton's synchronized conditional. -/
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

/-- Benton's synchronized `While`, partial-correctness reading. -/
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

/-- Asynchronous While (the rDo shape): left-only, right-only and joint steps under the
schedulers `L`, `Rt`; no termination premise. -/
theorem rhl_while_async {r : State → State → Prop} {b b' : State → Prop} {c c' : Cmd}
    (L Rt : State → State → Prop)
    (hside : ∀ s s', r s s' → (b s ↔ b' s') ∨ (L s s' ∧ b s) ∨ (Rt s s' ∧ b' s'))
    (hL : rhl (fun s s' => r s s' ∧ b s ∧ L s s') c .skip r)
    (hR : rhl (fun s s' => r s s' ∧ b' s' ∧ Rt s s') .skip c' r)
    (hJ : rhl (fun s s' => r s s' ∧ b s ∧ b' s' ∧ ¬ L s s' ∧ ¬ Rt s s') c c' r) :
    rhl r (.while b c) (.while b' c') (fun t t' => r t t' ∧ ¬ b t ∧ ¬ b' t') := by
  have aux : ∀ N, ∀ n n', n + n' ≤ N → ∀ (s s' : State), r s s' →
      ∀ t ∈ loopIter b (sem c) n s, ∀ t' ∈ loopIter b' (sem c') n' s',
        r t t' ∧ ¬ b t ∧ ¬ b' t' := by
    intro N
    induction N with
    | zero =>
      intro n n' hN s s' _ t ht
      obtain rfl : n = 0 := by omega
      simp at ht
    | succ N ih =>
      intro n n' hN s s' hr t ht t' ht'
      cases n with
      | zero => simp at ht
      | succ n =>
      cases n' with
      | zero => simp at ht'
      | succ n' =>
      by_cases hLs : b s ∧ L s s'
      · rw [loopIter_succ_pos hLs.1] at ht
        obtain ⟨u, hu, ht⟩ := mem_kleisli.mp ht
        exact ih n (n' + 1) (by omega) u s'
          (hL s s' ⟨hr, hLs.1, hLs.2⟩ u hu s' (by simp)) t ht t' ht'
      by_cases hRs : b' s' ∧ Rt s s'
      · rw [loopIter_succ_pos hRs.1] at ht'
        obtain ⟨v, hv, ht'⟩ := mem_kleisli.mp ht'
        exact ih (n + 1) n' (by omega) s v
          (hR s s' ⟨hr, hRs.1, hRs.2⟩ s (by simp) v hv) t ht t' ht'
      · have hiff : b s ↔ b' s' := by
          rcases hside s s' hr with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact h
          · exact absurd ⟨h2, h1⟩ hLs
          · exact absurd ⟨h2, h1⟩ hRs
        by_cases hb : b s
        · have hb' : b' s' := hiff.mp hb
          rw [loopIter_succ_pos hb] at ht
          rw [loopIter_succ_pos hb'] at ht'
          obtain ⟨u, hu, ht⟩ := mem_kleisli.mp ht
          obtain ⟨v, hv, ht'⟩ := mem_kleisli.mp ht'
          exact ih n n' (by omega) u v
            (hJ s s' ⟨hr, hb, hb', fun h => hLs ⟨hb, h⟩, fun h => hRs ⟨hb', h⟩⟩ u hu v hv)
            t ht t' ht'
        · have hb' : ¬ b' s' := fun h => hb (hiff.mpr h)
          rw [loopIter_succ_neg hb, Set.mem_singleton_iff] at ht
          rw [loopIter_succ_neg hb', Set.mem_singleton_iff] at ht'
          subst ht ht'
          exact ⟨hr, hb, hb'⟩
  intro s s' hr t ht t' ht'
  obtain ⟨n, ht⟩ := Set.mem_iUnion.mp ht
  obtain ⟨n', ht'⟩ := Set.mem_iUnion.mp ht'
  exact aux (n + n') n n' le_rfl s s' hr t ht t' ht'

end RelOL
