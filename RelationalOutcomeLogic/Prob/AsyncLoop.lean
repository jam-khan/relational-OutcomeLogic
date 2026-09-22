import RelationalOutcomeLogic.Algebra.Alignment
import RelationalOutcomeLogic.Prob.OneSided
import RelationalOutcomeLogic.Prob.Observation

/-!
# Ranked asynchronous loop couplings

A scheduler selects left, right, or joint steps. Unilateral steps decrease a natural
rank on every supported successor; joint steps may reset it. A single chosen joint
kernel defines the product execution. Its projections are proved equal to the two
original loops, including when joint execution diverges. No uniform rank bound or
global termination assumption is required.
-/

namespace RelOL.Prob

variable {α β σ τ : Type*}

/-- A mixed alignment whose unilateral phases cannot stutter forever. -/
structure AsyncSchedule (R : α → β → Prop) (g : α → Prop) (h : β → Prop)
    (k : α → Weight α) (l : β → Weight β) where
  mode : α × β → AsyncMode
  rank : α × β → ℕ
  guards : ∀ a b, R a b → match mode (a, b) with
    | .left => g a
    | .right => h b
    | .both => g a ∧ h b
    | .done => ¬ g a ∧ ¬ h b
  left : ∀ a b, R a b → mode (a, b) = .left →
    Coupled (fun x y => R x y ∧ rank (x, y) < rank (a, b)) (k a) (Weight.pure b)
  right : ∀ a b, R a b → mode (a, b) = .right →
    Coupled (fun x y => R x y ∧ rank (x, y) < rank (a, b)) (Weight.pure a) (l b)
  both : ∀ a b, R a b → mode (a, b) = .both → Coupled R (k a) (l b)

namespace AsyncSchedule

variable {R : α → β → Prop} {g : α → Prop} {h : β → Prop}
  {k : α → Weight α} {l : β → Weight β}

/-- Choose the local joint once; every finite product approximation uses this kernel. -/
noncomputable def kernel (S : AsyncSchedule R g h k l) : α × β → Weight (α × β) := by
  classical
  exact fun p => if hp : R p.1 p.2 then
    if hm : S.mode p = .left then (S.left p.1 p.2 hp hm).choose else
    if hm : S.mode p = .right then (S.right p.1 p.2 hp hm).choose else
    if hm : S.mode p = .both then (S.both p.1 p.2 hp hm).choose else 0
    else 0

theorem kernel_left (S : AsyncSchedule R g h k l) {a : α} {b : β}
    (hab : R a b) (hm : S.mode (a, b) = .left) :
    IsCoupling (fun x y => R x y ∧ S.rank (x, y) < S.rank (a, b))
      (k a) (Weight.pure b) (S.kernel (a, b)) := by
  classical
  dsimp only [kernel]
  rw [dif_pos hab, dif_pos hm]
  exact (S.left a b hab hm).choose_spec

theorem kernel_right (S : AsyncSchedule R g h k l) {a : α} {b : β}
    (hab : R a b) (hm : S.mode (a, b) = .right) :
    IsCoupling (fun x y => R x y ∧ S.rank (x, y) < S.rank (a, b))
      (Weight.pure a) (l b) (S.kernel (a, b)) := by
  classical
  dsimp only [kernel]
  rw [dif_pos hab, dif_neg (by simp [hm]), dif_pos hm]
  exact (S.right a b hab hm).choose_spec

theorem kernel_both (S : AsyncSchedule R g h k l) {a : α} {b : β}
    (hab : R a b) (hm : S.mode (a, b) = .both) :
    IsCoupling R (k a) (l b) (S.kernel (a, b)) := by
  classical
  dsimp only [kernel]
  rw [dif_pos hab, dif_neg (by simp [hm]), dif_neg (by simp [hm]), dif_pos hm]
  exact (S.both a b hab hm).choose_spec

theorem kernel_invariant (S : AsyncSchedule R g h k l) {p : α × β}
    (hp : R p.1 p.2) (hactive : S.mode p ≠ .done)
    {q : α × β} (hq : q ∈ Weight.support (S.kernel p)) : R q.1 q.2 := by
  cases hm : S.mode p with
  | left => exact ((S.kernel_left hp hm).supported q.1 q.2 hq).1
  | right => exact ((S.kernel_right hp hm).supported q.1 q.2 hq).1
  | both => exact (S.kernel_both hp hm).supported q.1 q.2 hq
  | done => exact (hactive hm).elim

end AsyncSchedule

/-- Pointwise comparison is needed only where the input weight is supported. -/
theorem bind_le_bind_on_support (μ : Weight σ) {f q : σ → Weight τ}
    (h : ∀ s ∈ Weight.support μ, f s ≤ q s) : Weight.bind μ f ≤ Weight.bind μ q := by
  intro t
  apply ENNReal.tsum_le_tsum
  intro s
  by_cases hs : μ s = 0
  · simp [hs]
  · exact mul_le_mul_right (h s hs t) (μ s)

/-- Removing rank-decreasing stutters preserves the full terminating projection.
The original fuel decreases on genuine steps; the rank decreases on stutters. -/
theorem pushforward_loopSem (π : σ → τ) (P : σ → Prop)
    (G : σ → Prop) (K : σ → Weight σ) (g : τ → Prop) (k : τ → Weight τ)
    (rank : σ → ℕ)
    (hinv : ∀ s, P s → G s → ∀ t ∈ Weight.support (K s), P t)
    (hdone : ∀ s, P s → ¬ G s → ¬ g (π s))
    (hstep : ∀ s, P s → G s →
      (g (π s) ∧ pushforward π (K s) = k (π s)) ∨
      (pushforward π (K s) = Weight.pure (π s) ∧
        ∀ t ∈ Weight.support (K s), rank t < rank s))
    (s : σ) (hs : P s) :
    pushforward π (loopSem G K s) = loopSem g k (π s) := by
  have upper : ∀ n s, P s →
      pushforward π (loopIter G K n s) ≤ loopSem g k (π s) := by
    intro n
    induction n with
    | zero =>
        intro s _
        rw [loopIter_zero, pushforward_zero]
        exact bot_le
    | succ n ih =>
        intro s hs
        by_cases hG : G s
        · rw [loopIter_succ_pos hG, pushforward_bind]
          calc
            Weight.bind (K s) (fun t => pushforward π (loopIter G K n t))
                ≤ Weight.bind (K s) (fun t => loopSem g k (π t)) :=
              bind_le_bind_on_support _ fun t ht => ih t (hinv s hs hG t ht)
            _ = Weight.bind (pushforward π (K s)) (loopSem g k) :=
              (bind_pushforward π (K s) (loopSem g k)).symm
            _ = loopSem g k (π s) := by
              rcases hstep s hs hG with ⟨hg, hmap⟩ | ⟨hmap, _⟩
              · rw [hmap, ← loopSem_pos hg]
              · rw [hmap, Weight.pure_bind]
        · rw [loopIter_succ_neg hG, pushforward_pure, loopSem_neg (hdone s hs hG)]
  have lower : ∀ n s, P s →
      loopIter g k n (π s) ≤ pushforward π (loopSem G K s) := by
    intro n
    induction n with
    | zero =>
        intro s _
        rw [loopIter_zero]
        exact bot_le
    | succ n ih =>
        have aux : ∀ r s, rank s = r → P s →
            loopIter g k (n + 1) (π s) ≤ pushforward π (loopSem G K s) := by
          intro r
          induction r using Nat.strong_induction_on with
          | h r ihr =>
              intro s hrs hs
              by_cases hG : G s
              · rw [loopSem_pos hG, pushforward_bind]
                rcases hstep s hs hG with ⟨hg, hmap⟩ | ⟨hmap, hdecr⟩
                · rw [loopIter_succ_pos hg]
                  calc
                    Weight.bind (k (π s)) (loopIter g k n)
                        = Weight.bind (pushforward π (K s)) (loopIter g k n) := by rw [hmap]
                    _ = Weight.bind (K s) (fun t => loopIter g k n (π t)) :=
                      bind_pushforward π (K s) (loopIter g k n)
                    _ ≤ Weight.bind (K s) (fun t => pushforward π (loopSem G K t)) :=
                      bind_le_bind_on_support _ fun t ht => ih t (hinv s hs hG t ht)
                · calc
                    loopIter g k (n + 1) (π s)
                        = Weight.bind (Weight.pure (π s)) (loopIter g k (n + 1)) :=
                      (Weight.pure_bind _ _).symm
                    _ = Weight.bind (pushforward π (K s)) (loopIter g k (n + 1)) := by rw [hmap]
                    _ = Weight.bind (K s) (fun t => loopIter g k (n + 1) (π t)) :=
                      bind_pushforward π (K s) (loopIter g k (n + 1))
                    _ ≤ Weight.bind (K s) (fun t => pushforward π (loopSem G K t)) := by
                      apply bind_le_bind_on_support
                      intro t ht
                      exact ihr (rank t) (by simpa only [hrs] using hdecr t ht)
                        t rfl (hinv s hs hG t ht)
              · rw [loopIter_succ_neg (hdone s hs hG), loopSem_neg hG, pushforward_pure]
        exact fun s hs => aux (rank s) s rfl hs
  apply le_antisymm
  · have hlim : pushforward π (loopSem G K s) =
        ⨆ n, pushforward π (loopIter G K n s) :=
      pushforward_iSup π _ (fun _ _ hij => loopIter_monotone G K hij s)
    rw [hlim]
    exact iSup_le fun n => upper n s hs
  · exact iSup_le fun n => lower n s hs

namespace AsyncSchedule

variable {R : α → β → Prop} {g : α → Prop} {h : β → Prop}
  {k : α → Weight α} {l : β → Weight β}

theorem kernel_step_left (S : AsyncSchedule R g h k l) {p : α × β}
    (hp : R p.1 p.2) (hactive : S.mode p ≠ .done) :
    (g p.1 ∧ pushforward Prod.fst (S.kernel p) = k p.1) ∨
    (pushforward Prod.fst (S.kernel p) = Weight.pure p.1 ∧
      ∀ q ∈ Weight.support (S.kernel p), S.rank q < S.rank p) := by
  have hg := S.guards p.1 p.2 hp
  cases hm : S.mode p with
  | left =>
      refine Or.inl ⟨by simpa only [hm] using hg, ?_⟩
      rw [pushforward_fst]
      exact (S.kernel_left hp hm).margL_eq
  | right =>
      refine Or.inr ⟨?_, fun q hq => ((S.kernel_right hp hm).supported q.1 q.2 hq).2⟩
      rw [pushforward_fst]
      exact (S.kernel_right hp hm).margL_eq
  | both =>
      have hguards : g p.1 ∧ h p.2 := by simpa only [hm] using hg
      refine Or.inl ⟨hguards.1, ?_⟩
      rw [pushforward_fst]
      exact (S.kernel_both hp hm).margL_eq
  | done => exact (hactive hm).elim

theorem kernel_step_right (S : AsyncSchedule R g h k l) {p : α × β}
    (hp : R p.1 p.2) (hactive : S.mode p ≠ .done) :
    (h p.2 ∧ pushforward Prod.snd (S.kernel p) = l p.2) ∨
    (pushforward Prod.snd (S.kernel p) = Weight.pure p.2 ∧
      ∀ q ∈ Weight.support (S.kernel p), S.rank q < S.rank p) := by
  have hg := S.guards p.1 p.2 hp
  cases hm : S.mode p with
  | left =>
      refine Or.inr ⟨?_, fun q hq => ((S.kernel_left hp hm).supported q.1 q.2 hq).2⟩
      rw [pushforward_snd]
      exact (S.kernel_left hp hm).margR_eq
  | right =>
      refine Or.inl ⟨by simpa only [hm] using hg, ?_⟩
      rw [pushforward_snd]
      exact (S.kernel_right hp hm).margR_eq
  | both =>
      have hguards : g p.1 ∧ h p.2 := by simpa only [hm] using hg
      refine Or.inl ⟨hguards.2, ?_⟩
      rw [pushforward_snd]
      exact (S.kernel_both hp hm).margR_eq
  | done => exact (hactive hm).elim

/-- The selected scheduler's actual product loop has exactly the original terminal marginals. -/
theorem isCoupling_loop (S : AsyncSchedule R g h k l) {a : α} {b : β} (hab : R a b) :
    IsCoupling (fun x y => R x y ∧ ¬ g x ∧ ¬ h y)
      (loopSem g k a) (loopSem h l b)
      (loopSem (fun p => S.mode p ≠ .done) S.kernel (a, b)) := by
  classical
  let G : α × β → Prop := fun p => S.mode p ≠ .done
  have hinv : ∀ p, R p.1 p.2 → G p →
      ∀ q ∈ Weight.support (S.kernel p), R q.1 q.2 :=
    fun _ hp hactive _ hq => S.kernel_invariant hp hactive hq
  have hdone : ∀ p, R p.1 p.2 → ¬ G p → ¬ g p.1 ∧ ¬ h p.2 := by
    intro p hp hstop
    have hm : S.mode p = .done := not_not.mp hstop
    simpa only [hm] using S.guards p.1 p.2 hp
  refine ⟨?_, ?_, ?_⟩
  · have hproj := pushforward_loopSem Prod.fst (fun p => R p.1 p.2)
      G S.kernel g k S.rank hinv (fun p hp he => (hdone p hp he).1)
      (fun _ hp hactive => S.kernel_step_left hp hactive) (a, b) hab
    simpa only [pushforward_fst] using hproj
  · have hproj := pushforward_loopSem Prod.snd (fun p => R p.1 p.2)
      G S.kernel h l S.rank hinv (fun p hp he => (hdone p hp he).2)
      (fun _ hp hactive => S.kernel_step_right hp hactive) (a, b) hab
    simpa only [pushforward_snd] using hproj
  · intro x y hxy
    have hexit := loopSem_support_invariant G S.kernel (fun p => R p.1 p.2)
      hinv (a, b) hab (x, y) hxy
    exact ⟨hexit.1, hdone (x, y) hexit.1 hexit.2⟩

end AsyncSchedule

/-- Mixed asynchronous loop soundness from local couplings and well-founded stuttering. -/
theorem coupled_loop_async {R : α → β → Prop} {g : α → Prop} {h : β → Prop}
    {k : α → Weight α} {l : β → Weight β} (S : AsyncSchedule R g h k l)
    {a : α} {b : β} (hab : R a b) :
    Coupled (fun x y => R x y ∧ ¬ g x ∧ ¬ h y) (loopSem g k a) (loopSem h l b) :=
  ⟨_, S.isCoupling_loop hab⟩

end RelOL.Prob
