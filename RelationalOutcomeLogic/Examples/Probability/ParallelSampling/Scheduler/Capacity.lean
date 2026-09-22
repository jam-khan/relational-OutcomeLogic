import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Scheduler.EventLoop

/-!
# Worker capacity and launch-window invariants

The worker bound counts only unfinished jobs; completed results occupy the
launch window until commitment. Both invariants hold for the actual fresh-launch
event loop, with and without a proposal cap.
-/

namespace RelOL.Prob.ParallelSampling

universe u
variable {α : Type u}

@[simp] theorem running_nil : running ([] : List (Slot α)) = 0 := rfl

theorem running_cons (slot : Slot α) (slots : List (Slot α)) :
    running (slot :: slots) = (if 0 < slot.remaining then 1 else 0) + running slots := by
  by_cases h : 0 < slot.remaining <;> simp [running, h, Nat.add_comm]

@[simp] theorem running_launch (slots : List (Slot α)) (j : Job α) :
    running (slots ++ [Slot.fresh j]) = running slots + 1 := by
  simp [running, Slot.fresh]

theorem running_tick_le (slots : List (Slot α)) :
    running (slots.map Slot.tick) ≤ running slots := by
  induction slots with
  | nil => simp
  | cons slot slots ih =>
      simp only [List.map_cons, running_cons, Slot.tick]
      split_ifs <;> omega

/-- The number of simultaneous workers and the number of uncommitted tickets
have separate bounds. Their distinction matters for speculative-work bounds. -/
def CapacityInvariant (workers window : Nat) (s : EventState α) : Prop :=
  running s.slots ≤ workers ∧ s.slots.length ≤ window

theorem eventAction_launch_space (workers window : Nat) (limited : Bool)
    (s : EventState α) (h : eventAction workers window limited s = .launch) :
    running s.slots < workers ∧ s.slots.length < window := by
  unfold eventAction at h
  split at h
  · contradiction
  · split at h
    · split at h
      · simp_all [running]
      · contradiction
    · split at h
      · contradiction
      · split at h
        · simp_all
        · contradiction

theorem CapacityInvariant.launch {workers window : Nat} {s : EventState α}
    (hspace : running s.slots < workers ∧ s.slots.length < window) (j : Job α) :
    CapacityInvariant workers window (s.launch j) := by
  simp only [CapacityInvariant, EventState.launch, running_launch, List.length_append,
    List.length_singleton]
  omega

theorem CapacityInvariant.tick {workers window : Nat} {s : EventState α}
    (h : CapacityInvariant workers window s) : CapacityInvariant workers window s.tick := by
  exact ⟨(running_tick_le _).trans h.1, by simpa [EventState.tick] using h.2⟩

theorem CapacityInvariant.commit {workers window : Nat} {s : EventState α}
    (h : CapacityInvariant workers window s) : CapacityInvariant workers window s.commit := by
  cases hs : s.slots with
  | nil => simpa [EventState.commit, hs] using h
  | cons slot slots =>
      simp only [CapacityInvariant, EventState.commit, hs]
      simp only [CapacityInvariant, hs, running_cons, List.length_cons] at h
      constructor <;> omega

noncomputable section

/-- Each actual event preserves both bounds, including a random launch. -/
theorem eventStep_capacity (law : Weight (Job α)) (workers window : Nat) (limited : Bool)
    (s : EventState α) (hs : CapacityInvariant workers window s) (t : EventState α)
    (ht : t ∈ Weight.support (eventStep law workers window limited s)) :
    CapacityInvariant workers window t := by
  cases ha : eventAction workers window limited s with
  | stop =>
      simp only [eventStep, ha, Weight.support_pure, Set.mem_singleton_iff] at ht
      exact ht ▸ hs
  | launch =>
      simp only [eventStep, ha, pushforward] at ht
      obtain ⟨j, _, ht⟩ := (Weight.mem_support_bind_iff _ _ _).mp ht
      simp only [Weight.support_pure, Set.mem_singleton_iff] at ht
      subst t
      exact CapacityInvariant.launch (eventAction_launch_space workers window limited s ha) j
  | tick =>
      simp only [eventStep, ha, Weight.support_pure, Set.mem_singleton_iff] at ht
      exact ht ▸ hs.tick
  | commit =>
      simp only [eventStep, ha, Weight.support_pure, Set.mem_singleton_iff] at ht
      exact ht ▸ hs.commit

/-- No supported full-loop execution exceeds its worker or ticket capacity. -/
theorem eventRun_capacity (law : Weight (Job α)) (workers window : Nat) (limited : Bool)
    (s : EventState α) (hs : CapacityInvariant workers window s) (t : EventState α)
    (ht : t ∈ Weight.support (eventRun law workers window limited s)) :
    CapacityInvariant workers window t :=
  (loopSem_support_invariant (eventActive workers window limited)
    (eventStep law workers window limited) (CapacityInvariant workers window)
    (fun s hs _ t ht => eventStep_capacity law workers window limited s hs t ht) s hs t ht).1

theorem eventRun_initial_capacity (law : Weight (Job α)) (workers window quota cap : Nat)
    (limited : Bool) (t : EventState α)
    (ht : t ∈ Weight.support
      (eventRun law workers window limited (EventState.initial quota cap))) :
    CapacityInvariant workers window t :=
  eventRun_capacity law workers window limited _
    (by simp [CapacityInvariant, EventState.initial]) t ht

end
end RelOL.Prob.ParallelSampling
