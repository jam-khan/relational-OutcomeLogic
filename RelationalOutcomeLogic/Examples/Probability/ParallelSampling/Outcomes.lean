import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Reference.Capped
import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Scheduler.Invariants
import RelationalOutcomeLogic.Prob.Coupling.Restriction
import RelationalOutcomeLogic.Prob.Coupling.Expectation

/-!
# Joint population and work contracts

These finite-prefix kernels are the ghost denotations consumed by the fresh-launch
event-loop refinement. The contract relates the complete population result and
the reference stopping ticket to all proposal counters in one coupling. Success
and exhaustion split into actual weighted outcomes with matching masses.
-/

namespace RelOL.Prob.ParallelSampling
open scoped ENNReal
universe u
variable {α : Type u}
noncomputable section

abbrev ReferenceResult (α : Type u) := Result α × Nat

def referenceRecord (law : Weight (Job α)) (cap quota : Nat) : Weight (ReferenceResult α) :=
  pushforward (fun js => (select quota js, used quota js)) (draws law cap)

def scheduledPrefix (law : Weight (Job α)) (workers window quota cap : Nat) :
    Weight (PoolResult α) := pushforward (pool workers window quota) (draws law cap)

/-- Population agreement, the exact stopping ticket, and bounded speculation. -/
def PopulationWork (window : Nat) (r : ReferenceResult α) (p : PoolResult α) : Prop :=
  r.1 = p.answer ∧ r.2 = p.committed ∧
  p.started = r.2 + p.discarded ∧ p.discarded ≤ window - 1

def populationWorkSpec (window : Nat) : RAssn (ReferenceResult α) (PoolResult α) :=
  fun μ ν => Coupled (PopulationWork window) μ ν ∧ massEq 1 1 μ ν

theorem scheduledPrefix_coupled (law : Weight (Job α))
    (workers window quota cap : Nat) (hworkers : 0 < workers) (hwindow : 0 < window) :
    Coupled (PopulationWork window) (referenceRecord law cap quota)
      (scheduledPrefix law workers window quota cap) := by
  apply (coupled_eq_iff.mpr (rfl : draws law cap = draws law cap)).pushforward
  intro js js' h
  subst js'
  have ho := poolFuel_observed workers window hworkers hwindow (waitingPotential js)
    (⟨quota, [], js⟩ : PoolInput α) (by simp [PoolInput.potential, poolPotential])
  simp only [poolKernel, pushforward_pure, PoolInput.expected, List.map_nil,
    List.nil_append, PoolResult.observe] at ho
  have he : ((pool workers window quota js).answer,
      (pool workers window quota js).committed) = (select quota js, used quota js) := by
    classical
    by_contra hne
    have hh := congrFun ho ((pool workers window quota js).answer,
      (pool workers window quota js).committed)
    change Weight.pure ((pool workers window quota js).answer,
        (pool workers window quota js).committed) _ = _ at hh
    simp [Weight.pure, hne] at hh
  exact ⟨(congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm,
    pool_started_eq _ _ _ hworkers hwindow _, pool_discarded_le _ _ _ hwindow _⟩

theorem referenceRecord_probability (law : Weight (Job α))
    (hlaw : Weight.IsProbability law) (cap quota : Nat) :
    Weight.IsProbability (referenceRecord law cap quota) :=
  (draws_probability law hlaw cap).bind (fun _ => Weight.isProbability_pure _)

theorem scheduledPrefix_probability (law : Weight (Job α))
    (hlaw : Weight.IsProbability law) (workers window quota cap : Nat) :
    Weight.IsProbability (scheduledPrefix law workers window quota cap) :=
  (draws_probability law hlaw cap).bind (fun _ => Weight.isProbability_pure _)

theorem scheduledPrefix_contract (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (workers window quota cap : Nat) (hworkers : 0 < workers) (hwindow : 0 < window) :
    populationWorkSpec window (referenceRecord law cap quota)
      (scheduledPrefix law workers window quota cap) :=
  ⟨scheduledPrefix_coupled law workers window quota cap hworkers hwindow,
   referenceRecord_probability law hlaw cap quota,
   scheduledPrefix_probability law hlaw workers window quota cap⟩

theorem referenceRecord_answer (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (cap quota : Nat) : pushforward Prod.fst (referenceRecord law cap quota) =
      capped law cap quota := by
  rw [capped_eq_prefix law hlaw, referenceRecord, pushforward, bind_pushforward]
  rfl

theorem scheduledPrefix_answer (law : Weight (Job α)) (hlaw : Weight.IsProbability law)
    (workers window quota cap : Nat) (hworkers : 0 < workers) (hwindow : 0 < window) :
    pushforward PoolResult.answer (scheduledPrefix law workers window quota cap) =
      capped law cap quota := by
  have h := (scheduledPrefix_coupled law workers window quota cap hworkers hwindow).pushforward
    Prod.fst PoolResult.answer (fun _ _ h => h.1)
  exact (coupled_eq_iff.mp h).symm.trans (referenceRecord_answer law hlaw cap quota)

def Result.succeeded : Result α → Prop
  | .success _ => True
  | .exhausted _ => False

/-- Each side's success/exhaustion piece has its own exact mass, including zero. -/
def populationSplit (window : Nat) (μ : Weight (ReferenceResult α)) :
    RAssn (ReferenceResult α) (PoolResult α) :=
  oplus
    (fun μ₁ ν₁ => couple (fun r p => PopulationWork window r p ∧
        r.1.succeeded ∧ p.answer.succeeded) μ₁ ν₁ ∧
      massEq (Weight.mass (Weight.restrict μ (fun r => r.1.succeeded)))
        (Weight.mass (Weight.restrict μ (fun r => r.1.succeeded))) μ₁ ν₁)
    (fun μ₂ ν₂ => couple (fun r p => PopulationWork window r p ∧
        ¬ r.1.succeeded ∧ ¬ p.answer.succeeded) μ₂ ν₂ ∧
      massEq (Weight.mass (Weight.restrict μ (fun r => ¬ r.1.succeeded)))
        (Weight.mass (Weight.restrict μ (fun r => ¬ r.1.succeeded))) μ₂ ν₂)

theorem scheduledPrefix_split (law : Weight (Job α))
    (workers window quota cap : Nat) (hworkers : 0 < workers) (hwindow : 0 < window) :
    populationSplit window (referenceRecord law cap quota) (referenceRecord law cap quota)
      (scheduledPrefix law workers window quota cap) :=
  (scheduledPrefix_coupled law workers window quota cap hworkers hwindow).split_mass
    (fun r => r.1.succeeded) (fun p => p.answer.succeeded)
    (fun _ _ h => by rw [h.1])

/-- Expected launch work follows from the same coupling as population correctness. -/
theorem scheduledPrefix_expected_started (law : Weight (Job α))
    (hlaw : Weight.IsProbability law) (workers window quota cap : Nat)
    (hworkers : 0 < workers) (hwindow : 0 < window) :
    Weight.expectation (scheduledPrefix law workers window quota cap) (fun p => p.started) ≤
      Weight.expectation (referenceRecord law cap quota) (fun r => r.2) + (window - 1 : Nat) := by
  have h := (scheduledPrefix_coupled law workers window quota cap hworkers hwindow).swap
  have hb := h.expectation_le (fun p => (p.started : ℝ≥0∞))
    (fun r => (r.2 : ℝ≥0∞) + (window - 1 : Nat)) (by
      intro p r h
      rcases h with ⟨_, _, hs, hd⟩
      rw [hs, Nat.cast_add]
      have hd' : (p.discarded : ℝ≥0∞) ≤ (window - 1 : Nat) := by exact_mod_cast hd
      exact add_le_add_right hd' _)
  have hm : Weight.mass (referenceRecord law cap quota) = 1 :=
    referenceRecord_probability law hlaw cap quota
  simpa only [Weight.expectation_add_cost, Weight.expectation_const,
    hm, one_mul] using hb

end
end RelOL.Prob.ParallelSampling
