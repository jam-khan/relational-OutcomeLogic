import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.UncappedCorrectness
import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Work
import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Adaptive
import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Faults.Duplication
import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Scheduler.Capacity
import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Window.Work
import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Scheduler.Batch
import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.UncappedRecord

/-!
# Parallel scientific sampling: case-study entry point

The actual collector samples joint (value, acceptance, duration) jobs at launch,
executes a finite-capacity worker pool, and commits in launch order. The capped
contract preserves exhausted populations; the uncapped contract includes almost
sure termination, the whole iid accepted-population law, and bounded speculative
work. Completion-order, duplicate-result, and stale-version faults refute the
same population equality consequence. See `docs/parallel-sampling.md` for the
proof derivation, source correspondence, and precise abstraction boundary.
-/

namespace RelOL.Prob.ParallelSampling
open scoped ENNReal
universe u
variable {α : Type u}
noncomputable section

/-- The uncapped application combines distribution, termination, and work. -/
def uncappedSpec (law : Weight (Job α)) (quota window : Nat) :
    RAssn (Nat × List α) (PoolResult α) := fun μ ν =>
  Coupled Eq μ (pushforward PoolResult.record ν) ∧ massEq 1 1 μ ν ∧
  (∀ p ∈ Weight.support ν,
    p.started = p.committed + p.discarded ∧ p.discarded ≤ window - 1) ∧
  Weight.expectation ν (fun p => p.started) ≤ quota / acceptance law + (window - 1 : Nat)

theorem uncapped_outcome_contract (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (ha : 0 < acceptance law) (workers window quota : Nat)
    (hworkers : 0 < workers) (hwindow : 0 < window) :
    uncappedSpec law quota window (countedPopulation law quota)
      (uncappedCollector law workers window quota) :=
  ⟨coupled_eq_iff.mpr (uncappedCollector_record law hlaw ha workers window quota
      hworkers hwindow).symm,
   ⟨countedPopulation_probability law hlaw ha quota,
    uncappedCollector_probability law hlaw ha workers window quota hworkers hwindow⟩,
   uncappedCollector_support_work law hlaw workers window quota hworkers hwindow,
   uncappedCollector_expected_started_le law hlaw ha workers window quota hworkers hwindow⟩

theorem uncapped_outcome_quad (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (ha : 0 < acceptance law) (workers window quota : Nat)
    (hworkers : 0 < workers) (hwindow : 0 < window) :
    quadSem
      (fun μ : Weight Unit => Weight.bind μ (fun _ => countedPopulation law quota))
      (fun ν : Weight Unit => Weight.bind ν (fun _ => uncappedCollector law workers window quota))
      (exactly (Weight.pure ()) (Weight.pure ())) (uncappedSpec law quota window) := by
  rw [quadSem_exactly_iff]
  simpa only [Weight.pure_bind] using
    uncapped_outcome_contract law hlaw ha workers window quota hworkers hwindow

/-- The correct event-driven policy satisfies exactly the population equality
that the completion-order race certificates refute. -/
theorem ordered_race_correct {θ : ℝ≥0∞} (hθ : θ ≤ 1) (P workers window : Nat)
    (hworkers : 0 < workers) (hwindow : 0 < window) :
    pushforward PoolResult.answer (freshCollector (raceJobLaw θ) workers window 1 (P + 1)) =
      referenceRacePopulation θ := by
  rw [freshCollector_answer _ (raceJobLaw_probability hθ) workers window 1 (P + 1)
    hworkers hwindow, capped_eq_prefix _ (raceJobLaw_probability hθ)]
  exact orderedRacePopulation_succ hθ P

/-- A slow early ticket stays first even when a later accepted job finishes sooner. -/
theorem slow_first_ticket :
    pool 2 2 1 [⟨false, true, 4⟩, ⟨true, true, 0⟩] =
      (⟨.success [false], 2, 1, 1, 5⟩ : PoolResult Bool) := by decide

/-- Rejection advances the ticket frontier; exhaustion retains the partial population. -/
theorem rejected_ticket_and_exhaustion :
    (pool 2 3 2 [⟨false, false, 2⟩, ⟨true, true, 0⟩]).answer =
      (Result.exhausted [true]) := by decide

theorem empty_quota_no_work (workers window : Nat) (jobs : List (Job α)) :
    pool workers window 0 jobs = ⟨.success [], 0, 0, 0, 0⟩ := by
  unfold pool
  cases waitingPotential jobs <;> rfl

theorem empty_cap_exhausted (workers window quota : Nat) :
    pool workers window (quota + 1) ([] : List (Job α)) = ⟨.exhausted [], 0, 0, 0, 0⟩ := rfl

end
end RelOL.Prob.ParallelSampling
