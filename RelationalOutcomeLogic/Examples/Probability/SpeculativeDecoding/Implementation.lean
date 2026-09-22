import RelationalOutcomeLogic.Examples.Probability.SpeculativeDecoding.Counterexamples
import RelationalOutcomeLogic.Algebra.ENNReal.Sequencing

/-!
# A bonus-token selection regression

This model isolates the implementation error of sampling the bonus token from the
draft rather than the target after a completely accepted draft block. A block of
width one and a remaining output budget of two suffice to expose the error.
The rejected branch resumes ordinary target decoding, while the accepted branch
uses either the correct target or the faulty draft continuation.

This is a mathematical model of the reported error, not an extraction or a proof
of an external implementation. The source and abstraction boundary are recorded
in the case-study documentation.

The pinned report is Appendix A, Table 3 of
<https://arxiv.org/html/2510.22876v3>. Its DSD entry describes the bonus-token source
error. The report's Appendix C presents a greedy algorithm; this file models the
probabilistic failure class and does not claim verified correspondence with that
greedy implementation or an unpinned source-code revision.
-/

namespace RelOL.Prob.Speculative.Implementation

open scoped ENNReal

variable {α : Type*}

noncomputable section

/-- Ordinary autoregressive generation of two tokens. -/
def reference (p : Distribution α) (next : α → Distribution α) : Weight (α × α) :=
  Weight.bind p.weight (fun x => pushforward (fun y => (x, y)) (next x).weight)

theorem reference_apply (p : Distribution α) (next : α → Distribution α) (x y : α) :
    reference p next (x, y) = p.weight x * (next x).weight y := by
  classical
  simp only [reference, pushforward, Weight.bind, Weight.pure, mul_ite, mul_one,
    mul_zero, Prod.mk.injEq]
  rw [tsum_eq_single x]
  · simp
  · intro a ha
    simp [Ne.symm ha]

/-- Execute the proposal and its verifier, then select the second token source.
Only the accepted branch is changed by `bonusFromDraft`. -/
def program (bonusFromDraft : Bool) (p q : Distribution α)
    (targetNext draftNext : α → Distribution α) : Weight (α × α) :=
  Weight.bind (step p q) (fun v =>
    pushforward (fun y => (v.2, y))
      (if bonusFromDraft && v.1 then (draftNext v.2).weight else (targetNext v.2).weight))

theorem reference_isProbability (p : Distribution α) (next : α → Distribution α) :
    Weight.IsProbability (reference p next) := by
  apply p.normalized.bind
  intro x
  simpa only [Weight.IsProbability, mass_pushforward] using (next x).normalized

theorem program_isProbability (bonusFromDraft : Bool) (p q : Distribution α)
    (targetNext draftNext : α → Distribution α) :
    Weight.IsProbability (program bonusFromDraft p q targetNext draftNext) := by
  apply (step_isProbability p q).bind
  intro v
  change Weight.mass (pushforward _ _) = 1
  rw [mass_pushforward]
  split
  · exact (draftNext v.2).normalized
  · exact (targetNext v.2).normalized

/-- With the target bonus, the complete two-token distribution is exact. -/
theorem correct (p q : Distribution α) (targetNext draftNext : α → Distribution α) :
    program false p q targetNext draftNext = reference p targetNext := by
  simp only [program, Bool.false_and, Bool.false_eq_true, if_false]
  rw [← bind_pushforward Prod.snd (step p q)
    (fun x => pushforward (fun y => (x, y)) (targetNext x).weight), step_output]
  rfl

/-- When every proposal is accepted, the mutant uses the draft for its second token. -/
theorem mutant_of_same_first (p : Distribution α)
    (targetNext draftNext : α → Distribution α) :
    program true p p targetNext draftNext = reference p draftNext := by
  rw [program, step_self, bind_pushforward]
  rfl

theorem reference_second_const (p r : Distribution α) :
    pushforward Prod.snd (reference p (fun _ => r)) = r.weight := by
  simp only [reference, pushforward_bind]
  have h : ∀ x : α, pushforward Prod.snd
      (pushforward (fun y : α => (x, y)) r.weight) = r.weight := by
    intro x
    simp only [pushforward, Weight.bind_assoc, Weight.pure_bind, Weight.bind_pure]
  simp only [h]
  exact Weight.bind_const_of_isProbability p.weight p.normalized r.weight

/-- A full-support draft for the next token, biased towards true. -/
def biasedDraft : Distribution Bool := ⟨Examples.biased, Examples.biased_isProbability⟩

def correctRun : Weight (Bool × Bool) :=
  program false fairTarget fairTarget (fun _ => fairTarget) (fun _ => biasedDraft)

def mutantRun : Weight (Bool × Bool) :=
  program true fairTarget fairTarget (fun _ => fairTarget) (fun _ => biasedDraft)

theorem correctRun_second : pushforward Prod.snd correctRun = fairTarget.weight := by
  rw [correctRun, correct, reference_second_const]

theorem mutantRun_second : pushforward Prod.snd mutantRun = biasedDraft.weight := by
  rw [mutantRun, mutant_of_same_first, reference_second_const]

/-- Both choices of bonus source terminate with unit mass. -/
theorem both_normalized : Weight.IsProbability correctRun ∧ Weight.IsProbability mutantRun :=
  ⟨program_isProbability .., program_isProbability ..⟩

theorem same_observed_support :
    Weight.support (pushforward Prod.snd correctRun) =
      Weight.support (pushforward Prod.snd mutantRun) := by
  rw [correctRun_second, mutantRun_second]
  exact Examples.same_support

/-- Even the complete two-token supports coincide: every Boolean pair remains possible. -/
theorem same_output_support : Weight.support correctRun = Weight.support mutantRun := by
  rw [correctRun, mutantRun, correct, mutant_of_same_first]
  ext xy
  rcases xy with ⟨x, y⟩
  cases x <;> cases y <;>
    norm_num [Weight.mem_support_iff, reference_apply, biasedDraft, Examples.biased, Weight.pure]

/-- Exact masses of the separating observation; the gap is one quarter. -/
theorem false_event_masses :
    Weight.eventMass (pushforward Prod.snd correctRun) {false} = 1 / 2 ∧
      Weight.eventMass (pushforward Prod.snd mutantRun) {false} = 1 / 4 := by
  rw [correctRun_second, mutantRun_second]
  norm_num [Weight.eventMass, biasedDraft, Examples.biased, Weight.pure]

def bonusDeficit : MassDeficitCert Eq
    (pushforward Prod.snd correctRun) (pushforward Prod.snd mutantRun) where
  left := {false}
  right := {false}
  cover := by
    intro a ha b hab
    simpa only [← hab] using ha
  deficit := by
    rw [false_event_masses.1, false_event_masses.2]
    norm_num

/-- The observed deficit rules out equality of the complete two-token outputs. -/
theorem full_output_not_coupled : ¬ Coupled Eq correctRun mutantRun := by
  intro h
  exact bonusDeficit.refutes (h.pushforward Prod.snd Prod.snd (fun _ _ he => congrArg Prod.snd he))

def sampler (w : Weight (Bool × Bool)) (μ : Weight Unit) : Weight (Bool × Bool) :=
  Weight.bind μ (fun _ => w)

def observedSampler (w : Weight (Bool × Bool)) (μ : Weight Unit) : Weight Bool :=
  pushforward Prod.snd (sampler w μ)

def bonusBug : BugCert (observedSampler correctRun) (observedSampler mutantRun) Eq where
  s₀ := ()
  s₀' := ()
  deficit := by simpa only [observedSampler, sampler, Weight.pure_bind] using bonusDeficit

/-- A certificate over the public second-token observation refutes the full
program-output contract. -/
theorem bonus_output_contract_refuted :
    ¬ quadSem (sampler correctRun) (sampler mutantRun)
      (exactly (Weight.pure ()) (Weight.pure ())) (couple Eq) := by
  apply bonusBug.refutes_of_observation (exactly_self _ _)
  intro μ ν h
  exact h.pushforward Prod.snd Prod.snd (fun _ _ he => congrArg Prod.snd he)

end

end RelOL.Prob.Speculative.Implementation
