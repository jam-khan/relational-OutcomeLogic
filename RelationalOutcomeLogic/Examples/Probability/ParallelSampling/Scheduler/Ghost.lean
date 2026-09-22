import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Scheduler.EventLoop
import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Scheduler.Rules

/-!
# Forward event-loop and continuation interpreter correspondence

The probabilistic implementation samples only at launch. Its reconstruction
proof introduces a finite ghost suffix. This module shows that executing that
ghost loop is exactly the deterministic event interpreter verified by the
recursion rule, including all work counters and elapsed completion ticks.
The induction uses a finite sampled tape's potential, not a global runtime bound.
-/

namespace RelOL.Prob.ParallelSampling

universe u
variable {α : Type u}

def Result.prefix (xs : List α) : Result α → Result α
  | .success ys => .success (xs ++ ys)
  | .exhausted ys => .exhausted (xs ++ ys)

/-- Interpret a backward continuation result in a forward accumulated state. -/
def EventState.accumulate (s : EventState α) (r : PoolResult α) : PoolResult α :=
  ⟨r.answer.prefix s.values, s.started + r.started, s.committed + r.committed,
    r.discarded, s.elapsed + r.elapsed⟩

@[simp] theorem Result.prefix_nil (r : Result α) : r.prefix [] = r := by
  cases r <;> simp [Result.prefix]

@[simp] theorem accumulate_launch (s : EventState α) (j : Job α) (r : PoolResult α) :
    (s.launch j).accumulate r = s.accumulate r.launch := by
  simp [EventState.accumulate, EventState.launch, PoolResult.launch,
    Nat.add_comm, Nat.add_left_comm]

@[simp] theorem accumulate_tick (s : EventState α) (r : PoolResult α) :
    s.tick.accumulate r = s.accumulate r.tick := by
  simp [EventState.accumulate, EventState.tick, PoolResult.tick,
    Nat.add_comm, Nat.add_left_comm]

theorem accumulate_commit (n : Nat) (slot : Slot α) (slots : List (Slot α))
    (budget : Nat) (values : List α) (started committed elapsed : Nat) (r : PoolResult α) :
    (EventState.commit
      ⟨n + 1, slot :: slots, budget, values, started, committed, elapsed⟩).accumulate r =
      (⟨n + 1, slot :: slots, budget, values, started, committed, elapsed⟩ :
        EventState α).accumulate
        (r.commit slot.job) := by
  cases ha : slot.job.accepted <;> cases hr : r.answer <;>
    simp [EventState.commit, EventState.accumulate, PoolResult.commit, Result.prefix,
      Result.prepend, ha, hr, List.append_assoc, Nat.add_comm, Nat.add_left_comm]

@[simp] theorem accumulate_stop (s : EventState α) :
    s.accumulate (poolStop s.quota s.slots) = s.observe := by
  by_cases h : s.quota = 0 <;>
    simp [EventState.accumulate, poolStop, EventState.observe, Result.prefix, h]

noncomputable section

def ghostObserved (workers window : Nat) (s : EventState α) (jobs : List (Job α)) :
    Weight (PoolResult α) :=
  pushforward (fun p => p.1.observe)
    (loopSem (fun p => eventActive workers window true p.1) (ghostEventStep workers window)
      (s, jobs))

private theorem ghostObserved_stop (workers window : Nat) (s : EventState α)
    (jobs : List (Job α)) (h : eventAction workers window true s = .stop) :
    ghostObserved workers window s jobs = Weight.pure s.observe := by
  unfold ghostObserved
  rw [loopSem_neg (by simp [eventActive, h])]
  exact pushforward_pure _ _

private theorem ghostObserved_launch (workers window : Nat) (s : EventState α)
    (j : Job α) (jobs : List (Job α)) (h : eventAction workers window true s = .launch) :
    ghostObserved workers window s (j :: jobs) =
      ghostObserved workers window (s.launch j) jobs := by
  unfold ghostObserved
  rw [loopSem_pos (by simp [eventActive, h]), ghostEventStep, h]
  simp only [Weight.pure_bind]

private theorem ghostObserved_tick (workers window : Nat) (s : EventState α)
    (jobs : List (Job α)) (h : eventAction workers window true s = .tick) :
    ghostObserved workers window s jobs = ghostObserved workers window s.tick jobs := by
  unfold ghostObserved
  rw [loopSem_pos (by simp [eventActive, h]), ghostEventStep, h]
  simp only [Weight.pure_bind]

private theorem ghostObserved_commit (workers window : Nat) (s : EventState α)
    (jobs : List (Job α)) (h : eventAction workers window true s = .commit) :
    ghostObserved workers window s jobs = ghostObserved workers window s.commit jobs := by
  unfold ghostObserved
  rw [loopSem_pos (by simp [eventActive, h]), ghostEventStep, h]
  simp only [Weight.pure_bind]

/-- Full forward/backward interpreter equality. The budget equals the remaining
ghost suffix length; accumulated values and accounting are arbitrary. -/
theorem ghostObserved_poolFuel (workers window : Nat) (hworkers : 0 < workers)
    (hwindow : 0 < window) (fuel : Nat) (s : EventState α) (jobs : List (Job α))
    (hbudget : s.budget = jobs.length) (hfuel : poolPotential s.slots jobs ≤ fuel) :
    ghostObserved workers window s jobs =
      Weight.pure (s.accumulate (poolFuel workers window fuel s.quota s.slots jobs)) := by
  induction fuel generalizing s jobs with
  | zero =>
      have hempty : s.slots = [] ∧ jobs = [] := by
        cases hs : s.slots with
        | cons slot slots => simp [poolPotential, hs] at hfuel
        | nil =>
            constructor
            · rfl
            · cases jobs with
              | nil => rfl
              | cons j js => simp [poolPotential, hs] at hfuel
      obtain ⟨hs, rfl⟩ := hempty
      have ha : eventAction workers window true s = .stop := by
        simp [eventAction, hs, hbudget]
      rw [ghostObserved_stop workers window s [] ha]
      simp [poolFuel]
  | succ fuel ih =>
      rcases s with ⟨quota, slots, budget, values, started, committed, elapsed⟩
      dsimp only at hbudget hfuel ⊢
      subst budget
      cases quota with
      | zero =>
          rw [ghostObserved_stop workers window _ jobs (by simp [eventAction])]
          simp [poolFuel, poolLayer, EventState.observe, EventState.accumulate,
            poolStop, Result.prefix]
      | succ n =>
          cases slots with
          | nil =>
              cases jobs with
              | nil =>
                  rw [ghostObserved_stop workers window _ [] (by simp [eventAction])]
                  simp [poolFuel, poolLayer, EventState.observe, EventState.accumulate,
                    poolStop, Result.prefix]
              | cons j js =>
                  have ha : eventAction workers window true
                      ⟨n + 1, [], (j :: js).length, values, started, committed, elapsed⟩ =
                          .launch := by
                    simp [eventAction, hworkers, hwindow]
                  rw [ghostObserved_launch workers window _ j js ha]
                  have he := poolPotential_launch ([] : List (Slot α)) j js
                  have hi := ih
                    (EventState.launch
                      ⟨n + 1, [], (j :: js).length, values, started, committed, elapsed⟩ j)
                    js (by simp [EventState.launch]) (by
                      simp only [EventState.launch, List.nil_append]
                      simpa using (by omega : poolPotential ([] ++ [Slot.fresh j]) js ≤ fuel))
                  rw [hi, accumulate_launch]
                  simp [poolFuel, poolLayer, hworkers, hwindow, EventState.launch]
          | cons slot slots =>
              by_cases hs : slot.remaining = 0
              · have ha : eventAction workers window true
                    ⟨n + 1, slot :: slots, jobs.length, values, started, committed, elapsed⟩ =
                      .commit := by
                  simp [eventAction, hs]
                rw [ghostObserved_commit workers window _ jobs ha]
                have he := poolPotential_commit slot slots jobs hs
                have hi := ih
                  (EventState.commit
                    ⟨n + 1, slot :: slots, jobs.length, values, started, committed, elapsed⟩)
                  jobs (by simp [EventState.commit]) (by
                    change poolPotential slots jobs ≤ fuel
                    omega)
                rw [hi]
                simp only [EventState.commit, Nat.add_sub_cancel,
                  poolFuel, poolLayer, hs, ↓reduceIte]
                exact congrArg Weight.pure
                  (accumulate_commit n slot slots jobs.length values started committed elapsed
                    (poolFuel workers window fuel
                      (if slot.job.accepted then n else n + 1) slots jobs))
              · have he := poolPotential_tick_lt slot slots jobs hs
                cases jobs with
                | nil =>
                    have ha : eventAction workers window true
                        ⟨n + 1, slot :: slots, 0, values, started, committed, elapsed⟩ =
                              .tick := by
                      simp [eventAction, hs]
                    simp only [List.length_nil]
                    rw [ghostObserved_tick workers window _ [] ha]
                    have hi := ih
                      (EventState.tick
                        ⟨n + 1, slot :: slots, 0, values, started, committed, elapsed⟩)
                      [] (by rfl) (by
                        change poolPotential ((slot :: slots).map Slot.tick) [] ≤ fuel
                        omega)
                    rw [hi, accumulate_tick]
                    simp [poolFuel, poolLayer, hs, EventState.tick]
                | cons j js =>
                    by_cases hc : running (slot :: slots) < workers ∧ slots.length + 1 < window
                    · have ha : eventAction workers window true
                          ⟨n + 1, slot :: slots, (j :: js).length, values,
                            started, committed, elapsed⟩ =
                          .launch := by
                        simp [eventAction, hs, hc]
                      rw [ghostObserved_launch workers window _ j js ha]
                      have he' := poolPotential_launch (slot :: slots) j js
                      have hi := ih
                        (EventState.launch
                          ⟨n + 1, slot :: slots, (j :: js).length, values,
                            started, committed, elapsed⟩ j)
                        js (by simp [EventState.launch]) (by
                          change poolPotential ((slot :: slots) ++ [Slot.fresh j]) js ≤ fuel
                          omega)
                      rw [hi, accumulate_launch]
                      simp [poolFuel, poolLayer, hs, hc, EventState.launch]
                    · have ha : eventAction workers window true
                          ⟨n + 1, slot :: slots, (j :: js).length, values,
                            started, committed, elapsed⟩ =
                              .tick := by
                        simp [eventAction, hs, hc]
                      rw [ghostObserved_tick workers window _ (j :: js) ha]
                      have hi := ih
                        (EventState.tick
                          ⟨n + 1, slot :: slots, (j :: js).length, values,
                            started, committed, elapsed⟩)
                        (j :: js) (by rfl) (by
                          change poolPotential ((slot :: slots).map Slot.tick) (j :: js) ≤ fuel
                          omega)
                      rw [hi, accumulate_tick]
                      simp [poolFuel, poolLayer, hs, hc, EventState.tick]

/-- The finite ghost loop computes the complete work-accounted worker-pool run. -/
theorem ghostObserved_pool (workers window quota : Nat) (hworkers : 0 < workers)
    (hwindow : 0 < window) (jobs : List (Job α)) :
    ghostObserved workers window (EventState.initial quota jobs.length) jobs =
      Weight.pure (pool workers window quota jobs) := by
  have h := ghostObserved_poolFuel workers window hworkers hwindow (waitingPotential jobs)
    (EventState.initial quota jobs.length) jobs rfl (by simp [EventState.initial, poolPotential])
  simpa [pool, EventState.initial, EventState.accumulate] using h

/-- Extra interpreter fuel cannot change values, work counters, or elapsed ticks.
The public evaluator chooses one sufficient potential; this theorem justifies
eliminating fuel from the algorithm's observable interface. -/
theorem poolFuel_irrelevant (workers window : Nat) (hworkers : 0 < workers)
    (hwindow : 0 < window) (fuel fuel' quota : Nat) (slots : List (Slot α))
    (jobs : List (Job α)) (hfuel : poolPotential slots jobs ≤ fuel)
    (hfuel' : poolPotential slots jobs ≤ fuel') :
    poolFuel workers window fuel quota slots jobs =
      poolFuel workers window fuel' quota slots jobs := by
  let s : EventState α := ⟨quota, slots, jobs.length, [], 0, 0, 0⟩
  have h :=
    (ghostObserved_poolFuel workers window hworkers hwindow fuel s jobs rfl hfuel).symm.trans
    (ghostObserved_poolFuel workers window hworkers hwindow fuel' s jobs rfl hfuel')
  simp only [s, EventState.accumulate, Result.prefix_nil, Nat.zero_add] at h
  classical
  by_contra hne
  have he := congrFun h (poolFuel workers window fuel quota slots jobs)
  simp [Weight.pure, hne] at he

end
end RelOL.Prob.ParallelSampling
