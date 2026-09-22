import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Scheduler.EventLoop

/-!
# The uncapped event loop as an increasing limit of finite executions

Successful capped laws are not monotone when work counters are observable:
changing the cap may change the number of speculative launches. We retain only
successful runs that leave at least one proposal unused (`started < cap`). The
cap cannot influence these executions. Their complete result-and-work laws form
an increasing sequence whose supremum is the actual uncapped event loop.
-/

namespace RelOL.Prob.ParallelSampling

universe u
variable {α : Type u}
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Successful outcomes that did not reach the proposal cap. -/
def interiorSuccess (cap : Nat) (r : PoolResult α) : Weight (PoolResult α) :=
  match r.answer with
  | .success _ => if r.started < cap then Weight.pure r else 0
  | .exhausted _ => 0

def interiorCollector (law : Weight (Job α)) (workers window quota cap : Nat) :
    Weight (PoolResult α) :=
  Weight.bind (freshCollector law workers window quota cap) (interiorSuccess cap)

private def observeInterior (cap : Nat) (s : EventState α) : Weight (PoolResult α) :=
  if s.quota = 0 ∧ s.started < cap then Weight.pure s.observe else 0

private theorem interior_observe (cap : Nat) (s : EventState α) :
    interiorSuccess cap s.observe = observeInterior cap s := by
  by_cases hq : s.quota = 0 <;>
    simp [interiorSuccess, EventState.observe, observeInterior, hq]

private def withBudget (cap : Nat) (s : EventState α) : EventState α :=
  { s with budget := cap - s.started }

private theorem withBudget_launch (cap : Nat) (s : EventState α) (j : Job α) :
    (withBudget cap s).launch j = withBudget cap (s.launch j) := by
  simp only [withBudget, EventState.launch, Nat.sub_sub]

private theorem withBudget_tick (cap : Nat) (s : EventState α) :
    (withBudget cap s).tick = withBudget cap s.tick := rfl

private theorem withBudget_commit (cap : Nat) (s : EventState α) :
    (withBudget cap s).commit = withBudget cap s.commit := by
  cases hs : s.slots <;> simp [withBudget, EventState.commit, hs]

private theorem withBudget_action (workers window cap : Nat) (s : EventState α)
    (hc : s.started < cap) :
    eventAction workers window true (withBudget cap s) =
      eventAction workers window false s := by
  have hb : 0 < cap - s.started := Nat.sub_pos_of_lt hc
  simp only [eventAction, withBudget, hb, true_or, or_true]

private theorem eventAction_unlimited_stop_iff (workers window : Nat)
    (hw : 0 < workers) (hwindow : 0 < window) (s : EventState α) :
    eventAction workers window false s = .stop ↔ s.quota = 0 := by
  unfold eventAction
  by_cases hq : s.quota = 0
  · simp [hq]
  · simp only [hq, ↓reduceIte]
    cases hs : s.slots with
    | nil => simp [hw, hwindow]
    | cons head tail =>
        by_cases hr : head.remaining = 0 <;> simp [hr]
        split <;> simp

private theorem eventStep_started (law : Weight (Job α)) (workers window : Nat)
    (limited : Bool) (s t : EventState α)
    (ht : t ∈ Weight.support (eventStep law workers window limited s)) :
    s.started ≤ t.started := by
  cases ha : eventAction workers window limited s with
  | stop =>
      simp only [eventStep, ha, Weight.support_pure, Set.mem_singleton_iff] at ht
      subst t
      exact le_rfl
  | launch =>
      simp only [eventStep, ha, pushforward] at ht
      obtain ⟨j, _, hj⟩ := (Weight.mem_support_bind_iff _ _ _).mp ht
      simp only [Weight.support_pure, Set.mem_singleton_iff] at hj
      subst t
      exact Nat.le_succ _
  | tick =>
      simp only [eventStep, ha, Weight.support_pure, Set.mem_singleton_iff] at ht
      subst t
      exact le_rfl
  | commit =>
      simp only [eventStep, ha, Weight.support_pure, Set.mem_singleton_iff] at ht
      subst t
      cases hs : s.slots <;> simp [EventState.commit, hs]

private theorem interior_after_cap (law : Weight (Job α)) (workers window : Nat)
    (limited : Bool) (cap fuel : Nat) (s : EventState α) (hc : cap ≤ s.started) :
    Weight.bind (loopIter (eventActive workers window limited)
      (eventStep law workers window limited) fuel s) (observeInterior cap) = 0 := by
  rw [← Weight.bind_zero (loopIter (eventActive workers window limited)
    (eventStep law workers window limited) fuel s)]
  apply Weight.bind_congr_on_support
  intro t ht
  have h := (loopIter_support_invariant (eventActive workers window limited)
    (eventStep law workers window limited) (fun t => cap ≤ t.started)
    (fun a ha _ b hb => ha.trans (eventStep_started law workers window limited a b hb))
    fuel s hc t ht).1
  simp [observeInterior, Nat.not_lt.mpr h]

private theorem interior_loopIter (law : Weight (Job α)) (workers window cap fuel : Nat)
    (s : EventState α) :
    Weight.bind (loopIter (eventActive workers window true)
      (eventStep law workers window true) fuel (withBudget cap s)) (observeInterior cap) =
    Weight.bind (loopIter (eventActive workers window false)
      (eventStep law workers window false) fuel s) (observeInterior cap) := by
  induction fuel generalizing s with
  | zero => simp
  | succ fuel ih =>
      by_cases hc : s.started < cap
      · have hb := withBudget_action workers window cap s hc
        cases ha : eventAction workers window false s with
        | stop =>
            simp only [loopIter, eventActive, hb, ha, ne_eq, not_true_eq_false,
              ↓reduceIte, Weight.pure_bind]
            rfl
        | launch =>
            simp only [loopIter, eventActive, hb, ha, ne_eq, reduceCtorEq,
              not_false_eq_true, ↓reduceIte, eventStep, Weight.bind_assoc, bind_pushforward]
            apply congrArg (Weight.bind law)
            funext j
            rw [withBudget_launch]
            exact ih _
        | commit =>
            simp only [loopIter, eventActive, hb, ha, ne_eq, reduceCtorEq,
              not_false_eq_true, ↓reduceIte, eventStep, Weight.pure_bind]
            rw [withBudget_commit]
            exact ih _
        | tick =>
            simp only [loopIter, eventActive, hb, ha, ne_eq, reduceCtorEq,
              not_false_eq_true, ↓reduceIte, eventStep, Weight.pure_bind]
            rw [withBudget_tick]
            exact ih _
      · rw [interior_after_cap law workers window true cap (fuel + 1)
          (withBudget cap s) (Nat.le_of_not_gt hc),
          interior_after_cap law workers window false cap (fuel + 1) s
            (Nat.le_of_not_gt hc)]

private theorem interior_loopSem (law : Weight (Job α)) (workers window cap : Nat)
    (s : EventState α) :
    Weight.bind (eventRun law workers window true (withBudget cap s)) (observeInterior cap) =
    Weight.bind (eventRun law workers window false s) (observeInterior cap) := by
  simp only [eventRun, loopSem]
  rw [Weight.bind_iSup_left _ (fun i j hij => loopIter_monotone _ _ hij _),
    Weight.bind_iSup_left _ (fun i j hij => loopIter_monotone _ _ hij _)]
  simp only [interior_loopIter]

/-- Every retained capped execution is exactly an execution of the actual uncapped
loop, including the work and elapsed-time fields. -/
theorem interiorCollector_eq_filtered_uncapped (law : Weight (Job α))
    (workers window quota cap : Nat) :
    interiorCollector law workers window quota cap =
      Weight.bind (uncappedCollector law workers window quota) (interiorSuccess cap) := by
  simp only [interiorCollector, freshCollector, uncappedCollector, bind_pushforward,
    interior_observe]
  have hi : (EventState.initial quota cap : EventState α) =
      withBudget cap (EventState.initial quota 0) := by simp [EventState.initial, withBudget]
  rw [hi, interior_loopSem]

theorem interiorSuccess_monotone : Monotone (interiorSuccess (α := α)) := by
  intro m n hmn r
  cases hr : r.answer with
  | exhausted xs => simp [interiorSuccess, hr]
  | success xs =>
      by_cases hm : r.started < m
      · simp [interiorSuccess, hr, hm, hm.trans_le hmn]
      · simp only [interiorSuccess, hr, if_neg hm]
        exact bot_le

theorem interiorSuccess_le_pure (cap : Nat) (r : PoolResult α) :
    interiorSuccess cap r ≤ Weight.pure r := by
  cases hr : r.answer with
  | exhausted xs => simp only [interiorSuccess, hr]; exact bot_le
  | success xs =>
      simp only [interiorSuccess, hr]
      split
      · exact le_rfl
      · exact bot_le

theorem interiorCollector_le_freshCollector (law : Weight (Job α))
    (workers window quota cap : Nat) :
    interiorCollector law workers window quota cap ≤
      freshCollector law workers window quota cap := by
  have h := Weight.bind_mono_right (freshCollector law workers window quota cap)
    (interiorSuccess_le_pure cap)
  simpa only [interiorCollector, Weight.bind_pure] using h

theorem interiorCollector_le_uncapped (law : Weight (Job α))
    (workers window quota cap : Nat) :
    interiorCollector law workers window quota cap ≤
      uncappedCollector law workers window quota := by
  rw [interiorCollector_eq_filtered_uncapped]
  have h := Weight.bind_mono_right (uncappedCollector law workers window quota)
    (interiorSuccess_le_pure cap)
  simpa only [Weight.bind_pure] using h

theorem interiorCollector_monotone (law : Weight (Job α)) (workers window quota : Nat) :
    Monotone (interiorCollector law workers window quota) := by
  intro m n hmn
  simp only [interiorCollector_eq_filtered_uncapped]
  exact Weight.bind_mono_right _ (interiorSuccess_monotone hmn)

private theorem success_observe_of_exit (workers window : Nat) (hw : 0 < workers)
    (hwindow : 0 < window) (s : EventState α)
    (hs : ¬ eventActive workers window false s) : s.quota = 0 := by
  apply (eventAction_unlimited_stop_iff workers window hw hwindow s).1
  simpa only [eventActive, not_not] using hs

private theorem interiorSuccess_iSup (r : PoolResult α)
    (hr : ∃ xs, r.answer = .success xs) :
    (⨆ cap, interiorSuccess cap r) = Weight.pure r := by
  obtain ⟨xs, hr⟩ := hr
  apply le_antisymm
  · apply iSup_le
    intro cap
    simp only [interiorSuccess, hr]
    split
    · exact le_rfl
    · exact bot_le
  · apply le_iSup_of_le (r.started + 1)
    simp [interiorSuccess, hr]

/-- No acceptance or normalization hypothesis is needed for the limit identity.
Positive capacity and window ensure every uncapped exit is a success. -/
theorem uncappedCollector_eq_iSup_interior (law : Weight (Job α))
    (workers window quota : Nat) (hw : 0 < workers) (hwindow : 0 < window) :
    uncappedCollector law workers window quota =
      ⨆ cap, interiorCollector law workers window quota cap := by
  simp only [interiorCollector_eq_filtered_uncapped]
  rw [← Weight.bind_iSup_right _ _ interiorSuccess_monotone]
  conv_lhs => rw [← Weight.bind_pure (uncappedCollector law workers window quota)]
  apply Weight.bind_congr_on_support
  intro r hr
  have hstate : ∃ s ∈ Weight.support
      (eventRun law workers window false (EventState.initial quota 0)), s.observe = r := by
    obtain ⟨s, hs, ho⟩ := (Weight.mem_support_bind_iff _ _ _).mp hr
    simp only [Weight.support_pure, Set.mem_singleton_iff] at ho
    exact ⟨s, hs, ho.symm⟩
  obtain ⟨s, hs, rfl⟩ := hstate
  have hexit := (loopSem_support_invariant (eventActive workers window false)
    (eventStep law workers window false) (fun _ => True)
    (fun _ _ _ _ _ => trivial) _ trivial s hs).2
  have hq := success_observe_of_exit workers window hw hwindow s hexit
  simpa only [iSup_apply] using
    (interiorSuccess_iSup s.observe ⟨s.values, by simp [EventState.observe, hq]⟩).symm

end
end RelOL.Prob.ParallelSampling
