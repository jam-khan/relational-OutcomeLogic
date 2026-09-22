import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Scheduler.Ghost
import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Outcomes

/-!
# Correctness of fresh-launch parallel collection

The implementation is the event loop, with draws at launch. Its finite-prefix
representation follows from the distributional loop rule and the finite ghost
interpreter correspondence. The population component of the resulting contract
comes from the scheduler's local continuation contracts and recursion rule.
-/

namespace RelOL.Prob.ParallelSampling

open scoped ENNReal
universe u
variable {α : Type u}
noncomputable section

/-- The actual event-loop implementation and its finite ghost representation
have the same complete law, including proposal accounting and elapsed ticks. -/
theorem freshCollector_eq_scheduledPrefix (law : Weight (Job α))
    (hlaw : Weight.IsProbability law) (workers window quota cap : Nat)
    (hworkers : 0 < workers) (hwindow : 0 < window) :
    freshCollector law workers window quota cap =
      scheduledPrefix law workers window quota cap := by
  rw [freshCollector, event_loop_observed law hlaw,
    eventReconstruction, bind_pushforward, scheduledPrefix, pushforward]
  apply Weight.bind_congr_on_support
  intro jobs hjobs
  have hlength := draws_support_length law cap jobs hjobs
  simpa only [ghostObserved, EventState.initial, hlength] using
    ghostObserved_pool workers window quota hworkers hwindow jobs

/-- One joint pRelOL contract simultaneously relates the complete population,
its stopping ticket, exact proposal accounting, and the speculation bound. -/
theorem freshCollector_contract (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (workers window quota cap : Nat) (hworkers : 0 < workers) (hwindow : 0 < window) :
    populationWorkSpec window (referenceRecord law cap quota)
      (freshCollector law workers window quota cap) := by
  rw [freshCollector_eq_scheduledPrefix law hlaw workers window quota cap hworkers hwindow]
  exact scheduledPrefix_contract law hlaw workers window quota cap hworkers hwindow

/-- Full joint-population law equality, retaining explicit budget exhaustion. -/
theorem freshCollector_answer (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (workers window quota cap : Nat) (hworkers : 0 < workers) (hwindow : 0 < window) :
    pushforward PoolResult.answer (freshCollector law workers window quota cap) =
      capped law cap quota := by
  rw [freshCollector_eq_scheduledPrefix law hlaw workers window quota cap hworkers hwindow]
  exact scheduledPrefix_answer law hlaw workers window quota cap hworkers hwindow

/-- Almost-sure completion of the finite-cap collector needs positive capacities
and finite individual job durations, with no common duration bound. -/
theorem freshCollector_probability (law : Weight (Job α))
    (hlaw : Weight.IsProbability law) (workers window quota cap : Nat)
    (hworkers : 0 < workers) (hwindow : 0 < window) :
    Weight.IsProbability (freshCollector law workers window quota cap) :=
  (freshCollector_contract law hlaw workers window quota cap hworkers hwindow).2.2

theorem freshCollector_split (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (workers window quota cap : Nat) (hworkers : 0 < workers) (hwindow : 0 < window) :
    populationSplit window (referenceRecord law cap quota) (referenceRecord law cap quota)
      (freshCollector law workers window quota cap) := by
  rw [freshCollector_eq_scheduledPrefix law hlaw workers window quota cap hworkers hwindow]
  exact scheduledPrefix_split law workers window quota cap hworkers hwindow

/-- A composable judgment for a generation starting from the unit input. -/
theorem freshCollector_quad (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (workers window quota cap : Nat) (hworkers : 0 < workers) (hwindow : 0 < window) :
    quadSem
      (fun μ : Weight Unit => Weight.bind μ (fun _ => referenceRecord law cap quota))
      (fun ν : Weight Unit => Weight.bind ν (fun _ => freshCollector law workers window quota cap))
      (exactly (Weight.pure ()) (Weight.pure ())) (populationWorkSpec window) := by
  rw [quadSem_exactly_iff]
  simpa only [Weight.pure_bind] using
    freshCollector_contract law hlaw workers window quota cap hworkers hwindow

/-- Quantitative correctness is a consequence of the same coupling, not a
separately assumed work model. -/
theorem freshCollector_expected_started (law : Weight (Job α))
    (hlaw : Weight.IsProbability law) (workers window quota cap : Nat)
    (hworkers : 0 < workers) (hwindow : 0 < window) :
    Weight.expectation (freshCollector law workers window quota cap) (fun p => p.started) ≤
      Weight.expectation (referenceRecord law cap quota) (fun r => r.2) + (window - 1 : Nat) := by
  rw [freshCollector_eq_scheduledPrefix law hlaw workers window quota cap hworkers hwindow]
  exact scheduledPrefix_expected_started law hlaw workers window quota cap hworkers hwindow

end
end RelOL.Prob.ParallelSampling
