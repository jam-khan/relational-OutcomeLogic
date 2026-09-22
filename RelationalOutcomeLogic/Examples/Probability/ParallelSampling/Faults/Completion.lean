import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Faults.Race
import RelationalOutcomeLogic.Prob.Refutation.Observation
import Mathlib.Tactic.Finiteness

/-!
# Quantitative certificates for completion-order commitment

Both policies return one accepted value. Ordered commitment retains the law of
the first launched job; racing commits the earliest completed job. The singleton
population certificate refutes the same equality-of-populations postcondition as
collector correctness. These are explicit mutants, not claims about shipped bugs.
-/

namespace RelOL.Prob.ParallelSampling

open scoped ENNReal
noncomputable section

/-- The complete one-person result, including its success tag. -/
def singletonPopulation (b : Bool) : Result Bool := .success [b]

def referenceRacePopulation (θ : ℝ≥0∞) : Weight (Result Bool) :=
  pushforward singletonPopulation (raceCoin θ)

def completionRacePopulation (θ : ℝ≥0∞) (P : Nat) : Weight (Result Bool) :=
  pushforward singletonPopulation (completionRace θ P)

/-- The correct one-person population obtained by ordering the actual timed jobs. -/
def orderedRacePopulation (θ : ℝ≥0∞) (P : Nat) : Weight (Result Bool) :=
  pushforward (select 1) (draws (raceJobLaw θ) P)

theorem orderedRacePopulation_succ {θ : ℝ≥0∞} (hθ : θ ≤ 1) (P : Nat) :
    orderedRacePopulation θ (P + 1) = referenceRacePopulation θ := by
  simp only [orderedRacePopulation, draws, raceJobLaw, pushforward,
    Weight.bind_assoc, Weight.pure_bind, select, raceJob, Result.prepend,
    referenceRacePopulation, singletonPopulation, ↓reduceIte]
  change Weight.bind (raceCoin θ) (fun b =>
    Weight.bind (draws (raceJobLaw θ) P) (fun _ => Weight.pure (singletonPopulation b))) =
    Weight.bind (raceCoin θ) (fun b => Weight.pure (singletonPopulation b))
  simp only [Weight.bind_const_of_isProbability _
    (draws_probability (raceJobLaw θ) (raceJobLaw_probability hθ) P)]

theorem singletonPopulation_weight (μ : Weight Bool) (b : Bool) :
    pushforward singletonPopulation μ (singletonPopulation b) = μ b := by
  cases b <;> simp [pushforward, Weight.bind, Weight.pure, singletonPopulation]

/-- A false output loses mass despite both programs being normalized and having
the same Boolean support. -/
def completionRaceDeficit {θ : ℝ≥0∞} (h₀ : 0 < θ) (h₁ : θ < 1)
    {P : Nat} (hP : 1 < P) :
    MassDeficitCert Eq (raceCoin θ) (completionRace θ P) where
  left := {false}
  right := {false}
  cover := by intro a ha b hab; simpa only [← hab] using ha
  deficit := by
    simpa only [Weight.eventMass, Finset.sum_singleton] using
      completionRace_false_lt h₀ h₁ hP

/-- The same deficit is certified on complete results, rather than just an
informal observation of their values. -/
def completionRacePopulationDeficit {θ : ℝ≥0∞} (h₀ : 0 < θ) (h₁ : θ < 1)
    {P : Nat} (hP : 1 < P) :
    MassDeficitCert Eq (referenceRacePopulation θ) (completionRacePopulation θ P) where
  left := {singletonPopulation false}
  right := {singletonPopulation false}
  cover := by intro a ha b hab; simpa only [← hab] using ha
  deficit := by
    simpa only [Weight.eventMass, Finset.sum_singleton, referenceRacePopulation,
      completionRacePopulation, singletonPopulation_weight] using
      completionRace_false_lt h₀ h₁ hP

/-- Unit-input sampling transformer, shared by the correct and mutant contracts. -/
def populationSampler {α : Type*} (law : Weight α) (μ : Weight Unit) : Weight α :=
  Weight.bind μ (fun _ => law)

def completionRaceBug {θ : ℝ≥0∞} (h₀ : 0 < θ) (h₁ : θ < 1)
    {P : Nat} (hP : 1 < P) :
    BugCert (populationSampler (referenceRacePopulation θ))
      (populationSampler (completionRacePopulation θ P)) Eq where
  s₀ := ()
  s₀' := ()
  deficit := by
    simpa only [populationSampler, Weight.pure_bind] using
      completionRacePopulationDeficit h₀ h₁ hP

theorem completionRace_population_contract_refuted {θ : ℝ≥0∞}
    (h₀ : 0 < θ) (h₁ : θ < 1) {P : Nat} (hP : 1 < P) :
    ¬ quadSem (populationSampler (referenceRacePopulation θ))
      (populationSampler (completionRacePopulation θ P))
      (exactly (Weight.pure ()) (Weight.pure ())) (couple Eq) :=
  (completionRaceBug h₀ h₁ hP).refutes (exactly_self _ _)

/-- The two-job example has probability `3/4`, not `1/2`. -/
theorem fair_two_race : completionRace (1 / 2) 2 true = 3 / 4 := by
  rw [completionRace_true (by norm_num)]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_sub_of_le (pow_le_one₀ bot_le tsub_le_self) ENNReal.one_ne_top]
  rw [ENNReal.toReal_pow, ENNReal.toReal_sub_of_le (by norm_num) ENNReal.one_ne_top]
  norm_num

/-- More workers amplify the distortion: eight fair jobs give `255/256`. -/
theorem fair_eight_race : completionRace (1 / 2) 8 true = 255 / 256 := by
  rw [completionRace_true (by norm_num)]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_sub_of_le (pow_le_one₀ bot_le tsub_le_self) ENNReal.one_ne_top]
  rw [ENNReal.toReal_pow, ENNReal.toReal_sub_of_le (by norm_num) ENNReal.one_ne_top]
  norm_num

def fairTwoRaceBug :
    BugCert (populationSampler (referenceRacePopulation (1 / 2)))
      (populationSampler (completionRacePopulation (1 / 2) 2)) Eq :=
  completionRaceBug (by norm_num) (by norm_num) (by decide)

def fairEightRaceBug :
    BugCert (populationSampler (referenceRacePopulation (1 / 2)))
      (populationSampler (completionRacePopulation (1 / 2) 8)) Eq :=
  completionRaceBug (by norm_num) (by norm_num) (by decide)

end
end RelOL.Prob.ParallelSampling
