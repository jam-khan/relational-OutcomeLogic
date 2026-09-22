import RelationalOutcomeLogic.Examples.Probability.SpeculativeDecoding.Correction
import RelationalOutcomeLogic.Examples.Probability.Coins
import RelationalOutcomeLogic.Prob.Refutation.Observation

/-!
# A normalized speculative sampler with a wrong rejection continuation

The mutant executes the same proposal and acceptance test as the correct sampler,
but resamples the target on rejection instead of its residual. Its token output has
the right support and unit mass, yet a finite-event certificate refutes the very same
equality contract proved for the corrected sampler.
-/

namespace RelOL.Prob.Speculative

open scoped ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

variable {α : Type*}

/-- The actual faulty verifier: the rejection branch samples the uncorrected target. -/
def wrongFallbackVerify (p q : Distribution α) (x : α) : Weight (Bool × α) :=
  accept p q x • Weight.pure (true, x) +
    (1 - accept p q x) • pushforward (fun y => (false, y)) p.weight

/-- Draw a proposal, then execute the faulty verifier. -/
def wrongFallbackStep (p q : Distribution α) : Weight (Bool × α) :=
  Weight.bind q.weight (wrongFallbackVerify p q)

theorem wrongFallbackVerify_isProbability (p q : Distribution α) (x : α) :
    Weight.IsProbability (wrongFallbackVerify p q x) := by
  rw [Weight.IsProbability, wrongFallbackVerify, Weight.mass_add, Weight.mass_smul,
    Weight.mass_smul, Weight.mass_pure, mass_pushforward, p.normalized,
    mul_one, mul_one]
  exact add_tsub_cancel_of_le (accept_le_one p q x)

theorem wrongFallbackStep_isProbability (p q : Distribution α) :
    Weight.IsProbability (wrongFallbackStep p q) :=
  q.normalized.bind (wrongFallbackVerify_isProbability p q)

theorem wrongFallbackVerify_apply_true (p q : Distribution α) (x y : α) :
    wrongFallbackVerify p q x (true, y) = if y = x then accept p q x else 0 := by
  classical
  simp [wrongFallbackVerify, pushforward, Weight.bind, Weight.pure, mul_ite]

theorem wrongFallbackVerify_apply_false (p q : Distribution α) (x y : α) :
    wrongFallbackVerify p q x (false, y) = (1 - accept p q x) * p.weight y := by
  classical
  simp [wrongFallbackVerify, pushforward, Weight.bind, Weight.pure, mul_ite]

theorem wrongFallbackStep_apply_true (p q : Distribution α) (x : α) :
    wrongFallbackStep p q (true, x) = overlap p q x := by
  classical
  simp only [wrongFallbackStep, Weight.bind, wrongFallbackVerify_apply_true, mul_ite,
    mul_zero]
  rw [tsum_eq_single x]
  · simpa using proposal_mul_accept p q x
  · intro y hy
    simp [Ne.symm hy]

theorem wrongFallbackStep_apply_false (p q : Distribution α) (x : α) :
    wrongFallbackStep p q (false, x) = rejectionMass p q * p.weight x := by
  simp only [wrongFallbackStep, Weight.bind, wrongFallbackVerify_apply_false,
    ← mul_assoc, proposal_mul_reject]
  rw [ENNReal.tsum_mul_right]
  exact congrArg (fun r => r * p.weight x) (mass_rejectedProposal p q)

/-- The bad continuation adds a scaled copy of the whole target, not the missing mass. -/
theorem wrongFallback_output (p q : Distribution α) :
    pushforward Prod.snd (wrongFallbackStep p q) =
      overlap p q + rejectionMass p q • p.weight := by
  rw [pushforward_snd]
  funext x
  simp only [margR, tsum_bool, wrongFallbackStep_apply_true, wrongFallbackStep_apply_false,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact add_comm _ _

/-- A fair target and an always-true proposal give a concrete finite counterexample. -/
def fairTarget : Distribution Bool := ⟨Examples.fair, Examples.fair_isProbability⟩

def alwaysTrueDraft : Distribution Bool := ⟨Weight.pure true, Weight.isProbability_pure true⟩

@[simp] theorem fairTarget_weight (b : Bool) : fairTarget.weight b = 1 / 2 := by
  cases b <;> norm_num [fairTarget, Examples.fair, Examples.half, Weight.pure]

@[simp] theorem rejectionMass_fair_true : rejectionMass fairTarget alwaysTrueDraft = 1 / 2 := by
  norm_num [rejectionMass, Weight.mass, tsum_bool, residual, overlap, alwaysTrueDraft,
    Weight.pure]

/-- With a point proposal the mutant produces true with probability three quarters. -/
theorem wrongFallback_fair_true_output :
    pushforward Prod.snd (wrongFallbackStep fairTarget alwaysTrueDraft) = Examples.biased := by
  rw [wrongFallback_output, rejectionMass_fair_true]
  funext b
  cases b <;> norm_num [overlap, alwaysTrueDraft, Examples.biased, Weight.pure]
  · apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num
  · apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num

theorem wrongFallback_same_support :
    Weight.support (pushforward Prod.snd (wrongFallbackStep fairTarget alwaysTrueDraft)) =
      Weight.support fairTarget.weight := by
  rw [wrongFallback_fair_true_output]
  exact Examples.same_support.symm

/-- The false-event deficit is computed from the actual faulty sampler. -/
def wrongFallbackDeficit :
    MassDeficitCert Eq fairTarget.weight
      (pushforward Prod.snd (wrongFallbackStep fairTarget alwaysTrueDraft)) where
  left := {false}
  right := {false}
  cover := by
    intro a ha b hab
    simpa only [← hab] using ha
  deficit := by
    rw [wrongFallback_fair_true_output]
    norm_num [Weight.eventMass, Examples.biased, Weight.pure]

/-- Reference and implementations are genuine sampling transformers on unit inputs. -/
def targetSampler (p : Distribution α) (μ : Weight Unit) : Weight α :=
  Weight.bind μ (fun _ => p.weight)

def correctedSampler (p q : Distribution α) (μ : Weight Unit) : Weight α :=
  Weight.bind μ (fun _ => pushforward Prod.snd (step p q))

def wrongFallbackSampler (p q : Distribution α) (μ : Weight Unit) : Weight α :=
  Weight.bind μ (fun _ => pushforward Prod.snd (wrongFallbackStep p q))

theorem corrected_output_contract (p q : Distribution α) :
    quadSem (targetSampler p) (correctedSampler p q)
      (exactly (Weight.pure ()) (Weight.pure ())) (couple Eq) := by
  rintro μ ν ⟨rfl, rfl⟩
  apply coupled_eq_iff.mpr
  simp only [targetSampler, correctedSampler, Weight.pure_bind, step_output]

def wrongFallbackBug :
    BugCert (targetSampler fairTarget) (wrongFallbackSampler fairTarget alwaysTrueDraft) Eq where
  s₀ := ()
  s₀' := ()
  deficit := by
    simpa only [targetSampler, wrongFallbackSampler, Weight.pure_bind] using wrongFallbackDeficit

/-- The faulty implementation refutes precisely the output contract above. -/
theorem wrongFallback_output_contract_refuted :
    ¬ quadSem (targetSampler fairTarget) (wrongFallbackSampler fairTarget alwaysTrueDraft)
      (exactly (Weight.pure ()) (Weight.pure ())) (couple Eq) :=
  wrongFallbackBug.refutes (exactly_self _ _)

end

end RelOL.Prob.Speculative
