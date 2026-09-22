import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Scheduler.Rules

/-!
# Local scheduler invariants and the complete finite-tape contract

Launch and completion preserve the outstanding tape. Commitment removes exactly
its head, and acceptance decides whether to prepend that value. Thus the proof
tracks a launch prefix; it never assumes that unfinished results remain iid after
observing completion times. The counters satisfy an exact conservation law.
-/

namespace RelOL.Prob.ParallelSampling

universe u
variable {α : Type u}

private theorem potential_zero (slots : List (Slot α)) (jobs : List (Job α))
    (h : poolPotential slots jobs = 0) : slots = [] ∧ jobs = [] := by
  cases slots with
  | cons s ss => simp [poolPotential] at h
  | nil =>
      constructor
      · rfl
      · cases jobs with
        | nil => rfl
        | cons j js => simp [poolPotential] at h

/-- All sufficiently fueled executions have the complete sequential result,
including the partial population and exhaustion flag. The second component
identifies the precise stopping ticket used by the work contract. -/
theorem poolFuel_correct (workers window : Nat) (hworkers : 0 < workers)
    (hwindow : 0 < window) (fuel quota : Nat)
    (slots : List (Slot α)) (jobs : List (Job α))
    (hfuel : poolPotential slots jobs ≤ fuel) :
    (poolFuel workers window fuel quota slots jobs).answer =
        select quota (slots.map Slot.job ++ jobs) ∧
    (poolFuel workers window fuel quota slots jobs).committed =
        used quota (slots.map Slot.job ++ jobs) := by
  have ho := poolFuel_observed workers window hworkers hwindow fuel
    (⟨quota, slots, jobs⟩ : PoolInput α) hfuel
  simp only [poolKernel, pushforward_pure, PoolResult.observe, PoolInput.expected] at ho
  have he : ((poolFuel workers window fuel quota slots jobs).answer,
      (poolFuel workers window fuel quota slots jobs).committed) =
        (select quota (slots.map Slot.job ++ jobs), used quota (slots.map Slot.job ++ jobs)) := by
    classical
    by_contra hne
    have hh := congrFun ho ((poolFuel workers window fuel quota slots jobs).answer,
      (poolFuel workers window fuel quota slots jobs).committed)
    simp [Weight.pure, hne] at hh
  exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩

/-- The public result agrees with sequential ordered selection for every tape,
so arbitrary dependencies between values, acceptance, and durations are allowed. -/
theorem pool_answer (workers window quota : Nat) (hworkers : 0 < workers)
    (hwindow : 0 < window) (jobs : List (Job α)) :
    (pool workers window quota jobs).answer = select quota jobs := by
  simpa [pool, poolPotential] using
    (poolFuel_correct workers window hworkers hwindow (waitingPotential jobs)
      quota [] jobs (by simp [poolPotential])).1

theorem pool_committed (workers window quota : Nat) (hworkers : 0 < workers)
    (hwindow : 0 < window) (jobs : List (Job α)) :
    (pool workers window quota jobs).committed = used quota jobs := by
  simpa [pool, poolPotential] using
    (poolFuel_correct workers window hworkers hwindow (waitingPotential jobs)
      quota [] jobs (by simp [poolPotential])).2

/-- Every launched ticket is either committed or discarded. Completed but
uncommitted slots still count as discarded work at an early successful return. -/
theorem poolFuel_accounting (workers window fuel quota : Nat)
    (slots : List (Slot α)) (jobs : List (Job α)) :
    (poolFuel workers window fuel quota slots jobs).started + slots.length =
      (poolFuel workers window fuel quota slots jobs).committed +
        (poolFuel workers window fuel quota slots jobs).discarded := by
  induction fuel generalizing quota slots jobs with
  | zero => simp [poolFuel, poolStop]
  | succ fuel ih =>
      cases quota with
      | zero => simp [poolFuel, poolLayer, poolStop]
      | succ n =>
          cases slots with
          | nil =>
              cases jobs with
              | nil => simp [poolFuel, poolLayer, poolStop]
              | cons j js =>
                  by_cases hp : 0 < workers ∧ 0 < window
                  · have hi := ih (n + 1) [Slot.fresh j] js
                    simp [poolFuel, poolLayer, hp, PoolResult.launch] at *
                    omega
                  · simp [poolFuel, poolLayer, hp, poolStop]
          | cons s ss =>
              by_cases hs : s.remaining = 0
              · have hi := ih (if s.job.accepted then n else n + 1) ss jobs
                simp [poolFuel, poolLayer, hs, PoolResult.commit]
                omega
              · cases jobs with
                | nil =>
                    have hi := ih (n + 1) ((s :: ss).map Slot.tick) []
                    simpa [poolFuel, poolLayer, hs, PoolResult.tick] using hi
                | cons j js =>
                    by_cases hc : running (s :: ss) < workers ∧ ss.length + 1 < window
                    · have hi := ih (n + 1) ((s :: ss) ++ [Slot.fresh j]) js
                      simp [poolFuel, poolLayer, hs, hc, PoolResult.launch] at *
                      omega
                    · have hi := ih (n + 1) ((s :: ss).map Slot.tick) (j :: js)
                      simpa [poolFuel, poolLayer, hs, hc, PoolResult.tick] using hi

/-- A nonempty request returns only after a commitment (or exhaustion), leaving
strictly fewer than `window` launched tickets outstanding. The extra zero-quota
premise records this strictness when reasoning inside a recursive continuation. -/
theorem poolFuel_discarded_lt (workers window : Nat) (hwindow : 0 < window)
    (fuel quota : Nat) (slots : List (Slot α)) (jobs : List (Job α))
    (hfuel : poolPotential slots jobs ≤ fuel) (hslots : slots.length ≤ window)
    (hzero : quota = 0 → slots.length < window) :
    (poolFuel workers window fuel quota slots jobs).discarded < window := by
  induction fuel generalizing quota slots jobs with
  | zero =>
      obtain ⟨rfl, rfl⟩ := potential_zero slots jobs (Nat.eq_zero_of_le_zero hfuel)
      simpa [poolFuel, poolStop] using hwindow
  | succ fuel ih =>
      cases quota with
      | zero => simpa [poolFuel, poolLayer, poolStop] using hzero rfl
      | succ n =>
          cases slots with
          | nil =>
              cases jobs with
              | nil => simpa [poolFuel, poolLayer, poolStop] using hwindow
              | cons j js =>
                  by_cases hp : 0 < workers ∧ 0 < window
                  · have he := poolPotential_launch ([] : List (Slot α)) j js
                    have hi := ih (n + 1) [Slot.fresh j] js
                      (by simpa using (by omega : poolPotential ([] ++ [Slot.fresh j]) js ≤ fuel))
                      (by simp; omega) (by omega)
                    simpa [poolFuel, poolLayer, hp, PoolResult.launch] using hi
                  · simpa [poolFuel, poolLayer, hp, poolStop] using hwindow
          | cons s ss =>
              simp only [List.length_cons] at hslots
              by_cases hs : s.remaining = 0
              · have he := poolPotential_commit s ss jobs hs
                have hi := ih (if s.job.accepted then n else n + 1) ss jobs
                  (by omega) (by omega) (by omega)
                simpa [poolFuel, poolLayer, hs, PoolResult.commit] using hi
              · have he := poolPotential_tick_lt s ss jobs hs
                cases jobs with
                | nil =>
                    have hi := ih (n + 1) ((s :: ss).map Slot.tick) [] (by omega)
                      (by simpa using hslots) (by omega)
                    simpa [poolFuel, poolLayer, hs, PoolResult.tick] using hi
                | cons j js =>
                    by_cases hc : running (s :: ss) < workers ∧ ss.length + 1 < window
                    · have he' := poolPotential_launch (s :: ss) j js
                      have hi := ih (n + 1) ((s :: ss) ++ [Slot.fresh j]) js
                        (by omega) (by simp; omega) (by omega)
                      simpa [poolFuel, poolLayer, hs, hc, PoolResult.launch] using hi
                    · have hi := ih (n + 1) ((s :: ss).map Slot.tick) (j :: js)
                        (by omega) (by simpa using hslots) (by omega)
                      simpa [poolFuel, poolLayer, hs, hc, PoolResult.tick] using hi

/-- Exact conservation, connected to the reference stopping ticket. -/
theorem pool_started_eq (workers window quota : Nat) (hworkers : 0 < workers)
    (hwindow : 0 < window) (jobs : List (Job α)) :
    (pool workers window quota jobs).started = used quota jobs +
      (pool workers window quota jobs).discarded := by
  have h := poolFuel_accounting workers window (waitingPotential jobs) quota [] jobs
  change (pool workers window quota jobs).started + 0 =
    (pool workers window quota jobs).committed + (pool workers window quota jobs).discarded at h
  simpa only [Nat.add_zero, pool_committed _ _ _ hworkers hwindow] using h

theorem pool_discarded_le (workers window quota : Nat) (hwindow : 0 < window)
    (jobs : List (Job α)) :
    (pool workers window quota jobs).discarded ≤ window - 1 := by
  have h := poolFuel_discarded_lt workers window hwindow (waitingPotential jobs)
    quota [] jobs (by simp [poolPotential]) (by simp) (by simpa using fun _ => hwindow)
  change (pool workers window quota jobs).discarded < window at h
  omega

/-- The sliding launch window, rather than worker count alone, bounds work. -/
theorem pool_started_le (workers window quota : Nat) (hworkers : 0 < workers)
    (hwindow : 0 < window) (jobs : List (Job α)) :
    (pool workers window quota jobs).started ≤ used quota jobs + window - 1 := by
  rw [pool_started_eq workers window quota hworkers hwindow]
  have h := pool_discarded_le workers window quota hwindow jobs
  omega

/-- A finite tape can launch each unlaunched ticket at most once. -/
theorem poolFuel_started_le (workers window fuel quota : Nat)
    (slots : List (Slot α)) (jobs : List (Job α)) :
    (poolFuel workers window fuel quota slots jobs).started ≤ jobs.length := by
  induction fuel generalizing quota slots jobs with
  | zero => simp [poolFuel, poolStop]
  | succ fuel ih =>
      cases quota with
      | zero => simp [poolFuel, poolLayer, poolStop]
      | succ n =>
          cases slots with
          | nil =>
              cases jobs with
              | nil => simp [poolFuel, poolLayer, poolStop]
              | cons j js =>
                  by_cases hp : 0 < workers ∧ 0 < window
                  · simpa [poolFuel, poolLayer, hp, PoolResult.launch] using
                      Nat.add_le_add_right (ih (n + 1) [Slot.fresh j] js) 1
                  · simp [poolFuel, poolLayer, hp, poolStop]
          | cons slot slots =>
              by_cases hs : slot.remaining = 0
              · simpa [poolFuel, poolLayer, hs, PoolResult.commit] using
                  ih (if slot.job.accepted then n else n + 1) slots jobs
              · cases jobs with
                | nil =>
                    simpa [poolFuel, poolLayer, hs, PoolResult.tick] using
                      ih (n + 1) ((slot :: slots).map Slot.tick) []
                | cons j js =>
                    by_cases hc : running (slot :: slots) < workers ∧ slots.length + 1 < window
                    · simpa [poolFuel, poolLayer, hs, hc, PoolResult.launch] using
                        Nat.add_le_add_right
                          (ih (n + 1) ((slot :: slots) ++ [Slot.fresh j]) js) 1
                    · simpa [poolFuel, poolLayer, hs, hc, PoolResult.tick] using
                        ih (n + 1) ((slot :: slots).map Slot.tick) (j :: js)

theorem pool_started_le_length (workers window quota : Nat) (jobs : List (Job α)) :
    (pool workers window quota jobs).started ≤ jobs.length :=
  poolFuel_started_le workers window (waitingPotential jobs) quota [] jobs

end RelOL.Prob.ParallelSampling
