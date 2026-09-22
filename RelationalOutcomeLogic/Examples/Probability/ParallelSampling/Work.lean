import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Reference.CappedWork
import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Correctness
import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Scheduler.Limits

/-! # Work bounds for the actual uncapped collector

Strict-interior finite executions retain the exact launched-work counters and
increase to the uncapped execution law. Monotone convergence transports the
uniform cap bound. The worker count and runtime distribution do not enter this
proposal bound; the launch window is essential.
-/

namespace RelOL.Prob.ParallelSampling
open scoped ENNReal
universe u
variable {α : Type u}
noncomputable section

theorem freshCollector_expected_started_le (law : Weight (Job α))
    (hlaw : Weight.IsProbability law) (ha : 0 < acceptance law)
    (workers window quota cap : Nat) (hworkers : 0 < workers) (hwindow : 0 < window) :
    Weight.expectation (freshCollector law workers window quota cap) (fun p => p.started) ≤
      quota / acceptance law + (window - 1 : Nat) := by
  rw [freshCollector_eq_scheduledPrefix law hlaw workers window quota cap hworkers hwindow]
  exact scheduledPrefix_expected_started_le law hlaw ha workers window quota cap hworkers hwindow

/-- Expected launched proposals, including unused speculative work, for the
real continuous worker pool with no proposal cap or loop-fuel hypothesis. -/
theorem uncappedCollector_expected_started_le (law : Weight (Job α))
    (hlaw : Weight.IsProbability law) (ha : 0 < acceptance law)
    (workers window quota : Nat) (hworkers : 0 < workers) (hwindow : 0 < window) :
    Weight.expectation (uncappedCollector law workers window quota) (fun p => p.started) ≤
      quota / acceptance law + (window - 1 : Nat) := by
  rw [uncappedCollector_eq_iSup_interior law workers window quota hworkers hwindow,
    Weight.expectation_iSup _ (interiorCollector_monotone law workers window quota)]
  apply iSup_le
  intro cap
  exact (Weight.expectation_mono_weight
    (interiorCollector_le_freshCollector law workers window quota cap) _).trans
      (freshCollector_expected_started_le law hlaw ha workers window quota cap hworkers hwindow)

theorem freshCollector_support_work (law : Weight (Job α))
    (hlaw : Weight.IsProbability law) (workers window quota cap : Nat)
    (hworkers : 0 < workers) (hwindow : 0 < window)
    (p : PoolResult α) (hp : p ∈ Weight.support (freshCollector law workers window quota cap)) :
    p.started = p.committed + p.discarded ∧ p.discarded ≤ window - 1 := by
  rw [freshCollector_eq_scheduledPrefix law hlaw workers window quota cap hworkers hwindow] at hp
  obtain ⟨js, _, hp⟩ := (Weight.mem_support_bind_iff _ _ _).mp hp
  simp only [Weight.support_pure, Set.mem_singleton_iff] at hp
  subst p
  rw [pool_started_eq _ _ _ hworkers hwindow, pool_committed _ _ _ hworkers hwindow]
  exact ⟨rfl, pool_discarded_le _ _ _ hwindow _⟩

/-- Pathwise accounting survives the limit, independently of acceptance rate. -/
theorem uncappedCollector_support_work (law : Weight (Job α))
    (hlaw : Weight.IsProbability law) (workers window quota : Nat)
    (hworkers : 0 < workers) (hwindow : 0 < window)
    (p : PoolResult α) (hp : p ∈ Weight.support (uncappedCollector law workers window quota)) :
    p.started = p.committed + p.discarded ∧ p.discarded ≤ window - 1 := by
  have hpos : 0 < ⨆ cap, interiorCollector law workers window quota cap p := by
    simpa only [uncappedCollector_eq_iSup_interior law workers window quota hworkers hwindow,
      iSup_apply] using pos_iff_ne_zero.mpr hp
  obtain ⟨cap, hcap⟩ := lt_iSup_iff.mp hpos
  have hf : 0 < freshCollector law workers window quota cap p :=
    hcap.trans_le (interiorCollector_le_freshCollector law workers window quota cap p)
  exact freshCollector_support_work law hlaw workers window quota cap hworkers hwindow p hf.ne'

end
end RelOL.Prob.ParallelSampling
