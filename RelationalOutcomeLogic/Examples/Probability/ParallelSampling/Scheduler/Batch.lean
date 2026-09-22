import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Correctness
import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Scheduler.Capacity

/-!
# Collect the batch, then select in launch order

This second concrete policy drains the entire proposal cap through the actual
fresh-launch event engine, then truncates the accepted launch-ordered population.
The drain's quota is `cap + 1`, which cannot be met with `cap` proposals. All
started work is therefore completed and committed before returning. This models
the collect-all/ordered-truncation pattern separately from early cancellation.
Its work is exactly the cap; the sliding-window early-return bound is not claimed.
-/

namespace RelOL.Prob.ParallelSampling

universe u
variable {α : Type u}

def acceptedValues : List (Job α) → List α
  | [] => []
  | j :: js => if j.accepted then j.value :: acceptedValues js else acceptedValues js

def truncatePopulation (quota : Nat) (values : List α) : Result α :=
  if quota ≤ values.length then .success (values.take quota) else .exhausted values

theorem acceptedValues_length (jobs : List (Job α)) :
    (acceptedValues jobs).length ≤ jobs.length := by
  induction jobs with
  | nil => simp [acceptedValues]
  | cons j js ih => cases ha : j.accepted <;> simp [acceptedValues, ha] <;> omega

/-- Launch-ordered selection is exactly truncation of the accepted subsequence. -/
theorem select_eq_truncate (quota : Nat) (jobs : List (Job α)) :
    select quota jobs = truncatePopulation quota (acceptedValues jobs) := by
  induction jobs generalizing quota with
  | nil => cases quota <;> simp [select, truncatePopulation, acceptedValues]
  | cons j js ih =>
      cases quota with
      | zero => simp [select, truncatePopulation]
      | succ n =>
          cases ha : j.accepted with
          | false => simp [select, acceptedValues, ha, ih]
          | true =>
              simp only [select, acceptedValues, ha, ↓reduceIte, ih]
              simp only [truncatePopulation, List.length_cons, Nat.add_le_add_iff_right]
              split <;> simp_all [Result.prepend, List.take_succ_cons]

theorem select_all (quota : Nat) (jobs : List (Job α)) (h : jobs.length < quota) :
    select quota jobs = .exhausted (acceptedValues jobs) := by
  rw [select_eq_truncate, truncatePopulation, if_neg]
  have hlength := acceptedValues_length jobs
  omega

theorem used_all (quota : Nat) (jobs : List (Job α)) (h : jobs.length < quota) :
    used quota jobs = jobs.length := by
  induction jobs generalizing quota with
  | nil => cases quota <;> rfl
  | cons j js ih =>
      cases quota with
      | zero => simp at h
      | succ n =>
          have hn : js.length < n := by simpa using Nat.lt_of_succ_lt_succ h
          have hn' : js.length < n + 1 := by omega
          cases ha : j.accepted <;>
            simp [used, ha, ih n hn, ih (n + 1) hn', Nat.add_comm]

/-- Postprocessing leaves the drain's work and elapsed-time observations intact. -/
def batchFinish (quota : Nat) (r : PoolResult α) : PoolResult α :=
  { r with answer := truncatePopulation quota r.answer.population }

noncomputable section

/-- Jobs are actually sampled at launch, executed, and fully drained before
selection. Capacity controls concurrency, while all cap tickets remain eligible. -/
def batchCollector (law : Weight (Job α)) (workers quota cap : Nat) :
    Weight (PoolResult α) :=
  pushforward (batchFinish quota)
    (freshCollector law workers (cap + 1) (cap + 1) cap)

theorem batchFinish_pool_answer (workers quota cap : Nat) (hworkers : 0 < workers)
    (jobs : List (Job α)) (hjobs : jobs.length = cap) :
    (batchFinish quota (pool workers (cap + 1) (cap + 1) jobs)).answer = select quota jobs := by
  rw [batchFinish, pool_answer _ _ _ hworkers (by omega), select_all _ _ (by omega)]
  exact (select_eq_truncate quota jobs).symm

/-- The batch collector returns the same whole population law as both sequential
rejection sampling and the early-return ordered collector, including exhaustion. -/
theorem batchCollector_answer (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (workers quota cap : Nat) (hworkers : 0 < workers) :
    pushforward PoolResult.answer (batchCollector law workers quota cap) =
      capped law cap quota := by
  rw [batchCollector, freshCollector_eq_scheduledPrefix law hlaw _ _ _ _ hworkers (by omega),
    scheduledPrefix, capped_eq_prefix law hlaw]
  simp only [pushforward, Weight.bind_assoc, Weight.pure_bind]
  apply Weight.bind_congr_on_support
  intro jobs hjobs
  exact congrArg Weight.pure
    (batchFinish_pool_answer workers quota cap hworkers jobs
      (draws_support_length law cap jobs hjobs))

theorem batchCollector_probability (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (workers quota cap : Nat) (hworkers : 0 < workers) :
    Weight.IsProbability (batchCollector law workers quota cap) :=
  (freshCollector_probability law hlaw workers (cap + 1) (cap + 1) cap hworkers (by omega)).bind
    (fun _ => Weight.isProbability_pure _)

/-- A drained batch commits every launched ticket and discards none. -/
theorem batch_pool_accounting (workers cap : Nat) (hworkers : 0 < workers)
    (jobs : List (Job α)) (hjobs : jobs.length = cap) :
    (pool workers (cap + 1) (cap + 1) jobs).started = cap ∧
    (pool workers (cap + 1) (cap + 1) jobs).committed = cap ∧
    (pool workers (cap + 1) (cap + 1) jobs).discarded = 0 := by
  have hc := pool_committed workers (cap + 1) (cap + 1) hworkers (by omega) jobs
  rw [used_all _ _ (by omega), hjobs] at hc
  have hs := pool_started_eq workers (cap + 1) (cap + 1) hworkers (by omega) jobs
  rw [used_all _ _ (by omega), hjobs] at hs
  have hb := pool_started_le_length workers (cap + 1) (cap + 1) jobs
  rw [hjobs] at hb
  exact ⟨by omega, hc, by omega⟩

/-- The second policy has an exact work contract: cap proposals, no cancellation. -/
theorem batchCollector_accounting (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (workers quota cap : Nat) (hworkers : 0 < workers) (r : PoolResult α)
    (hr : r ∈ Weight.support (batchCollector law workers quota cap)) :
    r.started = cap ∧ r.committed = cap ∧ r.discarded = 0 := by
  rw [batchCollector, freshCollector_eq_scheduledPrefix law hlaw _ _ _ _ hworkers (by omega),
    scheduledPrefix] at hr
  obtain ⟨p, hp, hr⟩ := (Weight.mem_support_bind_iff _ _ _).mp hr
  obtain ⟨jobs, hjobs, hp⟩ := (Weight.mem_support_bind_iff _ _ _).mp hp
  simp only [Weight.support_pure, Set.mem_singleton_iff] at hr hp
  subst r
  subst p
  exact batch_pool_accounting workers cap hworkers jobs (draws_support_length law cap jobs hjobs)

/-- Population equality and the batch policy's exact work appear in one relation. -/
def BatchContract (cap : Nat) (r : Result α) (p : PoolResult α) : Prop :=
  r = p.answer ∧ p.started = cap ∧ p.committed = cap ∧ p.discarded = 0

theorem batchCollector_coupled (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (workers quota cap : Nat) (hworkers : 0 < workers) :
    Coupled (BatchContract cap) (capped law cap quota) (batchCollector law workers quota cap) := by
  have hd : Coupled (fun xs ys : List (Job α) => xs = ys ∧ xs.length = cap)
      (draws law cap) (draws law cap) := by
    refine ⟨diag (draws law cap), margL_diag _, margR_diag _, ?_⟩
    intro xs ys hxy
    have he := (isCoupling_diag (draws law cap)).supported xs ys hxy
    refine ⟨he, draws_support_length law cap xs ?_⟩
    simpa [diag, he] using hxy
  have h := hd.pushforward (S := BatchContract cap) (select quota)
    (fun js => batchFinish quota (pool workers (cap + 1) (cap + 1) js)) (by
      intro xs ys hxy
      rcases hxy with ⟨rfl, hlen⟩
      exact ⟨(batchFinish_pool_answer workers quota cap hworkers xs hlen).symm,
        batch_pool_accounting workers cap hworkers xs hlen⟩)
  rw [capped_eq_prefix law hlaw, batchCollector,
    freshCollector_eq_scheduledPrefix law hlaw _ _ _ _ hworkers (by omega), scheduledPrefix]
  simpa only [pushforward, Weight.bind_assoc, Weight.pure_bind] using h

/-- The complete normalized relational outcome contract for draining a batch. -/
theorem batchCollector_contract (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (workers quota cap : Nat) (hworkers : 0 < workers) :
    Coupled (BatchContract cap) (capped law cap quota) (batchCollector law workers quota cap) ∧
      massEq 1 1 (capped law cap quota) (batchCollector law workers quota cap) :=
  ⟨batchCollector_coupled law hlaw workers quota cap hworkers,
    capped_probability law hlaw cap quota,
    batchCollector_probability law hlaw workers quota cap hworkers⟩

end
end RelOL.Prob.ParallelSampling
