import RelationalOutcomeLogic.Algebra.Alignment
import RelationalOutcomeLogic.Generic.Loops.Synchronous
import RelationalOutcomeLogic.Generic.Loops.Support
import RelationalOutcomeLogic.Algebra.Weighted.Observation

/-!
# Ranked asynchronous loop couplings

A scheduler selects left, right, or joint steps. Unilateral steps decrease a natural
rank on every supported successor; joint steps may reset it. A single chosen joint
kernel defines the product execution. Its projections are proved equal to the two
original loops, including when joint execution diverges. No uniform rank bound or
global termination assumption is required.
-/

universe u v

namespace RelOL.Algebra.Weighted

variable {κ : Type v} [Semiring κ] [CompleteLattice κ]
variable [SummationSemiring.{u} κ] [OmegaSummationSemiring.{u} κ]
variable {α β σ τ : Type u}

open Generic (loopIter loopSem loopIter_monotone)

/-- A mixed alignment whose unilateral phases cannot stutter forever. -/
structure AsyncSchedule (R : α → β → Prop) (g : α → Prop) (h : β → Prop)
    (k : α → Weight κ α) (l : β → Weight κ β) where
  mode : α × β → AsyncMode
  rank : α × β → ℕ
  guards : ∀ a b, R a b → match mode (a, b) with
    | .left => g a
    | .right => h b
    | .both => g a ∧ h b
    | .done => ¬ g a ∧ ¬ h b
  left : ∀ a b, R a b → mode (a, b) = .left →
    Coupled (fun x y => R x y ∧ rank (x, y) < rank (a, b)) (k a) (Weighted.pure b)
  right : ∀ a b, R a b → mode (a, b) = .right →
    Coupled (fun x y => R x y ∧ rank (x, y) < rank (a, b)) (Weighted.pure a) (l b)
  both : ∀ a b, R a b → mode (a, b) = .both → Coupled R (k a) (l b)

namespace AsyncSchedule

variable {R : α → β → Prop} {g : α → Prop} {h : β → Prop}
  {k : α → Weight κ α} {l : β → Weight κ β}

/-- Choose the local joint once; every finite product approximation uses this kernel. -/
noncomputable def kernel (S : AsyncSchedule R g h k l) : α × β → Weight κ (α × β) := by
  classical
  exact fun p => if hp : R p.1 p.2 then
    if hm : S.mode p = .left then (S.left p.1 p.2 hp hm).choose else
    if hm : S.mode p = .right then (S.right p.1 p.2 hp hm).choose else
    if hm : S.mode p = .both then (S.both p.1 p.2 hp hm).choose else 0
    else 0

omit [CompleteLattice κ] [OmegaSummationSemiring κ] in
theorem kernel_left (S : AsyncSchedule R g h k l) {a : α} {b : β}
    (hab : R a b) (hm : S.mode (a, b) = .left) :
    IsCoupling (fun x y => R x y ∧ S.rank (x, y) < S.rank (a, b))
      (k a) (Weighted.pure b) (S.kernel (a, b)) := by
  classical
  dsimp only [kernel]
  rw [dif_pos hab, dif_pos hm]
  exact (S.left a b hab hm).choose_spec

omit [CompleteLattice κ] [OmegaSummationSemiring κ] in
theorem kernel_right (S : AsyncSchedule R g h k l) {a : α} {b : β}
    (hab : R a b) (hm : S.mode (a, b) = .right) :
    IsCoupling (fun x y => R x y ∧ S.rank (x, y) < S.rank (a, b))
      (Weighted.pure a) (l b) (S.kernel (a, b)) := by
  classical
  dsimp only [kernel]
  rw [dif_pos hab, dif_neg (by simp [hm]), dif_pos hm]
  exact (S.right a b hab hm).choose_spec

omit [CompleteLattice κ] [OmegaSummationSemiring κ] in
theorem kernel_both (S : AsyncSchedule R g h k l) {a : α} {b : β}
    (hab : R a b) (hm : S.mode (a, b) = .both) :
    IsCoupling R (k a) (l b) (S.kernel (a, b)) := by
  classical
  dsimp only [kernel]
  rw [dif_pos hab, dif_neg (by simp [hm]), dif_neg (by simp [hm]), dif_pos hm]
  exact (S.both a b hab hm).choose_spec

omit [CompleteLattice κ] [OmegaSummationSemiring κ] in
theorem kernel_invariant (S : AsyncSchedule R g h k l) {p : α × β}
    (hp : R p.1 p.2) (hactive : S.mode p ≠ .done)
    {q : α × β} (hq : q ∈ Weighted.support (S.kernel p)) : R q.1 q.2 := by
  cases hm : S.mode p with
  | left => exact ((S.kernel_left hp hm).supported q.1 q.2 hq).1
  | right => exact ((S.kernel_right hp hm).supported q.1 q.2 hq).1
  | both => exact (S.kernel_both hp hm).supported q.1 q.2 hq
  | done => exact (hactive hm).elim

end AsyncSchedule

/-- Pointwise comparison is needed only where the input weight is supported. -/
theorem bind_le_bind_on_support (μ : Weight κ σ) {f q : σ → Weight κ τ}
    (h : ∀ s ∈ Weighted.support μ, f s ≤ q s) : Weighted.bind μ f ≤ Weighted.bind μ q := by
  intro t
  apply OmegaSummationSemiring.sum_mono
  intro s
  by_cases hs : μ s = 0
  · simp [hs]
  · exact OmegaSummationSemiring.mul_mono le_rfl (h s hs t)

/-- Removing rank-decreasing stutters preserves the full terminating projection.
The original fuel decreases on genuine steps; the rank decreases on stutters. -/
theorem pushforward_loopSem (π : σ → τ) (P : σ → Prop)
    (G : σ → Prop) (K : σ → Weight κ σ) (g : τ → Prop) (k : τ → Weight κ τ)
    (rank : σ → ℕ)
    (hinv : ∀ s, P s → G s → ∀ t ∈ Weighted.support (K s), P t)
    (hdone : ∀ s, P s → ¬ G s → ¬ g (π s))
    (hstep : ∀ s, P s → G s →
      (g (π s) ∧ pushforward π (K s) = k (π s)) ∨
      (pushforward π (K s) = Weighted.pure (π s) ∧
        ∀ t ∈ Weighted.support (K s), rank t < rank s))
    (s : σ) (hs : P s) :
    pushforward π (loopSem G K s) = loopSem g k (π s) := by
  have upper : ∀ n s, P s →
      pushforward π (loopIter G K n s) ≤ loopSem g k (π s) := by
    intro n
    induction n with
    | zero =>
        intro s _
        rw [loopIter_zero, pushforward_zero]
        exact fun t => by rw [Pi.zero_apply, OmegaSummationSemiring.zero_eq_bot]; exact bot_le
    | succ n ih =>
        intro s hs
        by_cases hG : G s
        · rw [loopIter_succ_pos hG, pushforward_bind]
          calc
            Weighted.bind (K s) (fun t => pushforward π (loopIter G K n t))
                ≤ Weighted.bind (K s) (fun t => loopSem g k (π t)) :=
              bind_le_bind_on_support _ fun t ht => ih t (hinv s hs hG t ht)
            _ = Weighted.bind (pushforward π (K s)) (loopSem g k) :=
              (bind_pushforward π (K s) (loopSem g k)).symm
            _ = loopSem g k (π s) := by
              rcases hstep s hs hG with ⟨hg, hmap⟩ | ⟨hmap, _⟩
              · rw [hmap, ← loopSem_pos hg]
              · rw [hmap, Weighted.pure_bind]
        · rw [loopIter_succ_neg hG, pushforward_pure, loopSem_neg (hdone s hs hG)]
  have lower : ∀ n s, P s →
      loopIter g k n (π s) ≤ pushforward π (loopSem G K s) := by
    intro n
    induction n with
    | zero =>
        intro s _
        rw [loopIter_zero]
        exact fun t => by rw [Pi.zero_apply, OmegaSummationSemiring.zero_eq_bot]; exact bot_le
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
                    Weighted.bind (k (π s)) (loopIter g k n)
                        = Weighted.bind (pushforward π (K s)) (loopIter g k n) := by rw [hmap]
                    _ = Weighted.bind (K s) (fun t => loopIter g k n (π t)) :=
                      bind_pushforward π (K s) (loopIter g k n)
                    _ ≤ Weighted.bind (K s) (fun t => pushforward π (loopSem G K t)) :=
                      bind_le_bind_on_support _ fun t ht => ih t (hinv s hs hG t ht)
                · calc
                    loopIter g k (n + 1) (π s)
                        = Weighted.bind (Weighted.pure (π s)) (loopIter g k (n + 1)) :=
                      (Weighted.pure_bind _ _).symm
                    _ = Weighted.bind (pushforward π (K s)) (loopIter g k (n + 1)) := by rw [hmap]
                    _ = Weighted.bind (K s) (fun t => loopIter g k (n + 1) (π t)) :=
                      bind_pushforward π (K s) (loopIter g k (n + 1))
                    _ ≤ Weighted.bind (K s) (fun t => pushforward π (loopSem G K t)) := by
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
  {k : α → Weight κ α} {l : β → Weight κ β}

omit [CompleteLattice κ] [OmegaSummationSemiring κ] in
theorem kernel_step_left (S : AsyncSchedule R g h k l) {p : α × β}
    (hp : R p.1 p.2) (hactive : S.mode p ≠ .done) :
    (g p.1 ∧ pushforward Prod.fst (S.kernel p) = k p.1) ∨
    (pushforward Prod.fst (S.kernel p) = Weighted.pure p.1 ∧
      ∀ q ∈ Weighted.support (S.kernel p), S.rank q < S.rank p) := by
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

omit [CompleteLattice κ] [OmegaSummationSemiring κ] in
theorem kernel_step_right (S : AsyncSchedule R g h k l) {p : α × β}
    (hp : R p.1 p.2) (hactive : S.mode p ≠ .done) :
    (h p.2 ∧ pushforward Prod.snd (S.kernel p) = l p.2) ∨
    (pushforward Prod.snd (S.kernel p) = Weighted.pure p.2 ∧
      ∀ q ∈ Weighted.support (S.kernel p), S.rank q < S.rank p) := by
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
      ∀ q ∈ Weighted.support (S.kernel p), R q.1 q.2 :=
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
    {k : α → Weight κ α} {l : β → Weight κ β} (S : AsyncSchedule R g h k l)
    {a : α} {b : β} (hab : R a b) :
    Coupled (fun x y => R x y ∧ ¬ g x ∧ ¬ h y) (loopSem g k a) (loopSem h l b) :=
  ⟨_, S.isCoupling_loop hab⟩

/-- Reverse a schedule, turning left-only phases into right-only phases. -/
def AsyncSchedule.swap {R : α → β → Prop} {g : α → Prop} {h : β → Prop}
    {k : α → Weight κ α} {l : β → Weight κ β} (S : AsyncSchedule R g h k l) :
    AsyncSchedule (fun b a => R a b) h g l k where
  mode p := (S.mode (p.2, p.1)).swap
  rank p := S.rank (p.2, p.1)
  guards := by
    intro b a hab
    have hs := S.guards a b hab
    cases hm : S.mode (a, b) <;> simp_all [AsyncMode.swap]
  left := by
    intro b a hab hm
    change (S.mode (a, b)).swap = .left at hm
    have hm' : S.mode (a, b) = .right := by
      have hs := congrArg AsyncMode.swap hm
      rw [AsyncMode.swap_swap] at hs
      simpa only [AsyncMode.swap] using hs
    exact (S.right a b hab hm').swap
  right := by
    intro b a hab hm
    change (S.mode (a, b)).swap = .right at hm
    have hm' : S.mode (a, b) = .left := by
      have hs := congrArg AsyncMode.swap hm
      rw [AsyncMode.swap_swap] at hs
      simpa only [AsyncMode.swap] using hs
    exact (S.left a b hab hm').swap
  both := by
    intro b a hab hm
    change (S.mode (a, b)).swap = .both at hm
    have hm' : S.mode (a, b) = .both := by
      have hs := congrArg AsyncMode.swap hm
      rw [AsyncMode.swap_swap] at hs
      simpa only [AsyncMode.swap] using hs
    exact (S.both a b hab hm').swap


end RelOL.Algebra.Weighted

namespace RelOL.Generic

open Algebra

variable {K : Type v} [Semiring K] [CompleteLattice K]
variable [SummationSemiring.{u} K] [OmegaSummationSemiring.{u} K]
variable {α β : Type u}

/-- A ranked mixed schedule proves exact-coupling pRHL for arbitrary ordered scalar instances. -/
theorem prhl_while_async {R : α → β → Prop} {g : α → Prop} {h : β → Prop}
    {k : α → Weighted.Weight K α} {l : β → Weighted.Weight K β}
    (S : Weighted.AsyncSchedule R g h k l) :
    prhl R (loopSem g k) (loopSem h l) (fun a b => R a b ∧ ¬ g a ∧ ¬ h b) :=
  fun _ _ hab => Weighted.coupled_loop_async S hab

/-- The generic outcome judgment inherits the scheduler's proved terminal marginals. -/
theorem quad_couple_while_async {R : α → β → Prop} {g : α → Prop} {h : β → Prop}
    {k : α → Weighted.Weight K α} {l : β → Weighted.Weight K β}
    (S : Weighted.AsyncSchedule R g h k l) :
    quad (couple R) (loopSem g k) (loopSem h l)
      (couple (fun a b => R a b ∧ ¬ g a ∧ ¬ h b)) :=
  prhl_iff_quad.mp (prhl_while_async S)

end RelOL.Generic
