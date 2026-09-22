import RelationalOutcomeLogic.Examples.Probability.Search.Programs
import RelationalOutcomeLogic.Subsumption.PRHL.Asynchronous

/-!
# A full scan coupled to early-exit randomized search

Before the first success the implementations advance together. Afterwards the full
scan consumes its remaining budget while the successful search stays put. This
unilateral phase decreases the remaining budget. Exact output matching and a bound
on consumed trials follow from the mixed asynchronous loop rule.
-/

namespace RelOL.Prob.Search

noncomputable section

/-- Answers agree; early exit leaves at least as much budget, with equality before success. -/
def Related (s t : State) : Prop :=
  s.2 = t.2 ∧ s.1 ≤ t.1 ∧ (s.2 = false → s.1 = t.1)

theorem related_refl (s : State) : Related s s := ⟨rfl, le_rfl, fun _ => rfl⟩

theorem related_miss {s t : State} (h : Related s t) :
    Related (s.1 - 1, s.2) (t.1 - 1, t.2) :=
  ⟨h.1, Nat.sub_le_sub_right h.2.1 1, fun hb => congrArg (fun n => n - 1) (h.2.2 hb)⟩

theorem related_hit {s t : State} (h : Related s t) :
    Related (s.1 - 1, true) (t.1 - 1, true) := by
  refine ⟨rfl, Nat.sub_le_sub_right h.2.1 1, ?_⟩
  simp

/-- Couple the miss branches and hit branches using the same normalized trial. -/
theorem draw_related (T : Trial) {s t : State} (h : Related s t) :
    Coupled Related (draw T s) (draw T t) :=
  ((Coupled.pure (related_miss h)).smul T.miss).add
    ((Coupled.pure (related_hit h)).smul T.hit)

/-- Once success is recorded, further random trials only decrement the remaining budget. -/
theorem draw_seen_true (T : Trial) {s : State} (hs : s.2 = true) :
    draw T s = Weight.pure (s.1 - 1, true) := by
  rw [draw, hs, ← add_smul, T.normalized, one_smul]

/-- The scheduler needs joint and left-only steps; the optimized search never gets ahead. -/
def mode (p : State × State) : AsyncMode :=
  if p.1.1 = 0 then .done else if p.1.2 = true then .left else .both

theorem mode_left_iff (s t : State) :
    mode (s, t) = .left ↔ 0 < s.1 ∧ s.2 = true := by
  unfold mode
  split_ifs with hn hb <;> simp_all [Nat.pos_iff_ne_zero]

theorem mode_ne_right (s t : State) : mode (s, t) ≠ .right := by
  unfold mode
  split_ifs <;> decide

theorem mode_guards {s t : State} (h : Related s t) :
    match mode (s, t) with
    | .left => fullGuard s
    | .right => earlyGuard t
    | .both => fullGuard s ∧ earlyGuard t
    | .done => ¬ fullGuard s ∧ ¬ earlyGuard t := by
  by_cases hn : s.1 = 0
  · simp only [mode, if_pos hn]
    refine ⟨by simp [fullGuard, hn], ?_⟩
    intro ht
    have hsfalse : s.2 = false := h.1.trans ht.2
    have htzero : t.1 = 0 := (h.2.2 hsfalse).symm.trans hn
    exact (Nat.ne_of_gt ht.1) htzero
  · by_cases hb : s.2 = true
    · simp only [mode, if_neg hn, if_pos hb]
      exact Nat.pos_of_ne_zero hn
    · have hsfalse : s.2 = false := by cases hs : s.2 <;> simp_all
      have htfalse : t.2 = false := h.1.symm.trans hsfalse
      have hcount : s.1 = t.1 := h.2.2 hsfalse
      simp only [mode, if_neg hn, if_neg hb]
      exact ⟨Nat.pos_of_ne_zero hn, hcount ▸ Nat.pos_of_ne_zero hn, htfalse⟩

/-- A finite unilateral cleanup follows success; the rank is the full scan's budget. -/
def schedule (T : Trial) :
    AsyncSchedule Related fullGuard earlyGuard (sem (body T)) (sem (body T)) where
  mode := mode
  rank p := p.1.1
  guards := fun _ _ h => mode_guards h
  left := by
    intro s t h hm
    obtain ⟨hn, hb⟩ := (mode_left_iff s t).mp hm
    change Coupled (fun x y => Related x y ∧ x.1 < s.1) (draw T s) (Weight.pure t)
    rw [draw_seen_true T hb]
    apply Coupled.pure
    refine ⟨⟨hb.symm.trans h.1, ?_, ?_⟩, ?_⟩
    · exact (Nat.sub_le _ _).trans h.2.1
    · simp
    · omega
  right := by
    intro s t _ hm
    exact (mode_ne_right s t hm).elim
  both := fun _ _ h _ => draw_related T h

/-- Full-state correctness is obtained from the mixed asynchronous proof rule. -/
theorem full_early_prhl (T : Trial) :
    prhl Related (full T) (early T)
      (fun s t => Related s t ∧ ¬ fullGuard s ∧ ¬ earlyGuard t) :=
  prhl_while_async (schedule T)

/-- The same derivation applies to arbitrary related input weights. -/
theorem full_early_quad (T : Trial) :
    quad (couple Related) (full T) (early T)
      (couple (fun s t => Related s t ∧ ¬ fullGuard s ∧ ¬ earlyGuard t)) :=
  prhl_iff_quad.mp (full_early_prhl T)

/-- The actual product-loop witness is exposed for quantitative outcome splitting. -/
def outputJoint (T : Trial) (s : State) : Weight (State × State) :=
  loopSem (fun p => (schedule T).mode p ≠ .done) (schedule T).kernel (s, s)

theorem outputJoint_isCoupling (T : Trial) (s : State) :
    IsCoupling (fun x y => Related x y ∧ ¬ fullGuard x ∧ ¬ earlyGuard y)
      (sem (full T) s) (sem (early T) s) (outputJoint T s) :=
  (schedule T).isCoupling_loop (related_refl s)

theorem outputs_coupled (T : Trial) (s : State) :
    Coupled (fun x y => Related x y ∧ ¬ fullGuard x ∧ ¬ earlyGuard y)
      (sem (full T) s) (sem (early T) s) :=
  full_early_prhl T s s (related_refl s)

/-- The externally visible answer distributions agree, although final budgets may differ. -/
theorem observed_equal (T : Trial) (s : State) :
    observe (sem (full T) s) = observe (sem (early T) s) := by
  apply coupled_eq_iff.mp
  exact (outputs_coupled T s).bind (fun x => Weight.pure x.2) (fun y => Weight.pure y.2)
    (fun _ _ h => Coupled.pure h.1.1)

/-- Exact marginals transfer the full scan's termination proof to early exit. -/
theorem early_isProbability (T : Trial) (s : State) :
    Weight.IsProbability (sem (early T) s) := by
  change Weight.mass (sem (early T) s) = 1
  rw [← (outputs_coupled T s).mass_eq]
  exact full_isProbability T s

theorem observed_seed_equal (T : Trial) (n : ℕ) :
    observed (full T) (seed n) = observed (early T) (seed n) := by
  simp only [observed_seed]
  exact observed_equal T (n, false)

/-- Every supported trial outcome records exactly one saturating decrement. -/
theorem draw_remaining {T : Trial} {s t : State} (ht : t ∈ Weight.support (draw T s)) :
    t.1 = s.1 - 1 := by
  simp only [draw, Weight.support_add, Set.mem_union, Weight.mem_support_smul_iff,
    Weight.support_pure, Set.mem_singleton_iff] at ht
  rcases ht with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl

/-- Early exit cannot invent budget; its state really records a consumed prefix. -/
theorem early_remaining_le (T : Trial) (s : State) {t : State}
    (ht : t ∈ Weight.support (sem (early T) s)) : t.1 ≤ s.1 := by
  have h := loopSem_support_invariant earlyGuard (draw T) (fun x => x.1 ≤ s.1)
    (fun x hx _ y hy => by rw [draw_remaining hy]; exact (Nat.sub_le _ _).trans hx)
    s le_rfl t ht
  exact h.1

/-- Trials consumed from an initial budget, as recorded by the countdown state. -/
def consumed (initial : ℕ) (s : State) : ℕ := initial - s.1

theorem consumed_bound {s t : State} (h : Related s t) (n : ℕ) :
    consumed n t ≤ consumed n s := by
  unfold consumed
  exact Nat.sub_le_sub_left h.2.1 n

/-- Matching answers can be coupled with no more consumed trials on the early-exit side. -/
theorem cost_coupling (T : Trial) (n : ℕ) (b : Bool) :
    Coupled (fun s t => s.2 = t.2 ∧ consumed n t ≤ consumed n s ∧ consumed n s = n)
      (sem (full T) (n, b)) (sem (early T) (n, b)) := by
  apply (outputs_coupled T (n, b)).mono
  intro s t h
  have hs : s.1 = 0 := Nat.eq_zero_of_not_pos h.2.1
  exact ⟨h.1.1, consumed_bound h.1 n, by simp [consumed, hs]⟩

end

end RelOL.Prob.Search
