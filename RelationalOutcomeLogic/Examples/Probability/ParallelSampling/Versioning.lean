import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Faults.Completion
import RelationalOutcomeLogic.Generic.Distributional
import RelationalOutcomeLogic.Bridges.Probability

/-!
# Version validation for speculative look-ahead

The reconstruction invariant gives an outstanding sample its generating law
conditional on the public version context. Validation inspects only versions,
never the sampled value. Matching kernels permit reuse; a mismatch discards a
normalized sample and executes the current kernel. This local rule composes with
generation contracts. It does not justify reusing a sample whose conditional law
has changed through sample-dependent choice of the context.
-/

namespace RelOL.Prob.ParallelSampling

universe u
variable {ι α : Type u}

noncomputable section

structure VersionContext (ι : Type u) where
  generated : ι
  required : ι

/-- The hidden sample's conditional reconstruction, given the public versions. -/
def versionBuffer (law : ι → Weight α) (c : VersionContext ι) :
    Weight (VersionContext ι × α) :=
  pushforward (fun x => (c, x)) (law c.generated)

/-- Validation is deliberately a function of versions alone. -/
def validateLookahead (law : ι → Weight α) (valid : ι → ι → Bool)
    (s : VersionContext ι × α) : Weight α :=
  if valid s.1.generated s.1.required then Weight.pure s.2 else law s.1.required

theorem validation_square (law : ι → Weight α)
    (hlaw : ∀ v, Weight.IsProbability (law v))
    (valid : ι → ι → Bool)
    (hsound : ∀ old current, valid old current = true → law old = law current)
    (c : VersionContext ι) :
    Weight.bind (versionBuffer law c) (validateLookahead law valid) = law c.required := by
  rw [versionBuffer, bind_pushforward]
  unfold validateLookahead
  cases hv : valid c.generated c.required with
  | false =>
      simp only [hv, Bool.false_eq_true, ↓reduceIte]
      exact Weight.bind_const_of_isProbability _ (hlaw _) _
  | true =>
      simp only [hv, ↓reduceIte, Weight.bind_pure]
      exact hsound _ _ hv

/-- A rule-level contract for consuming one outstanding proposal. The postcondition
is equality of the complete sampled outcomes, under arbitrary input mixtures. -/
theorem validateLookahead_quad (law : ι → Weight α)
    (hlaw : ∀ v, Weight.IsProbability (law v))
    (valid : ι → ι → Bool)
    (hsound : ∀ old current, valid old current = true → law old = law current) :
    Generic.quad (Generic.lifted (versionBuffer law))
      (fun c => law c.required) (validateLookahead law valid)
      (Generic.lifted (Weight.pure : α → Weight α)) := by
  apply Generic.quad_lifted
  intro c
  simpa only [Generic.weight_bind_eq, Weight.bind_pure] using
    validation_square law hlaw valid hsound c

/-- Equality of version identifiers is sufficient when the law is version-indexed. -/
theorem validateEqualVersion_quad [DecidableEq ι] (law : ι → Weight α)
    (hlaw : ∀ v, Weight.IsProbability (law v)) :
    Generic.quad (Generic.lifted (versionBuffer law))
      (fun c => law c.required)
      (validateLookahead law (fun old current => decide (old = current)))
      (Generic.lifted (Weight.pure : α → Weight α)) := by
  apply validateLookahead_quad law hlaw
  intro old current heq
  simp only [decide_eq_true_eq] at heq
  rw [heq]

/-- Public execution samples the speculative candidate before validation. -/
def validatedSample (law : ι → Weight α) (valid : ι → ι → Bool)
    (c : VersionContext ι) : Weight α :=
  Weight.bind (versionBuffer law c) (validateLookahead law valid)

/-- Extract the public equality from the local rule's reconstruction precondition. -/
theorem validatedSample_eq (law : ι → Weight α)
    (hlaw : ∀ v, Weight.IsProbability (law v))
    (valid : ι → ι → Bool)
    (hsound : ∀ old current, valid old current = true → law old = law current)
    (c : VersionContext ι) :
    validatedSample law valid c = law c.required := by
  have h := validateLookahead_quad law hlaw valid hsound
    (Weight.pure c) (versionBuffer law c) (Generic.lifted_pure _ _)
  simpa only [validatedSample, Generic.lifted, Generic.weight_bind_eq, Weight.pure_bind,
    Weight.bind_pure] using h

open scoped ENNReal

/-- A naive stale proposal ignores the required version and returns the old draw. -/
def stalePopulation (old : ℝ≥0∞) : Weight (Result Bool) :=
  pushforward singletonPopulation (raceCoin old)

def stalePopulationDeficit :
    MassDeficitCert Eq (referenceRacePopulation (1 / 2)) (stalePopulation (3 / 4)) where
  left := {singletonPopulation false}
  right := {singletonPopulation false}
  cover := by intro a ha b hab; simpa only [← hab] using ha
  deficit := by
    simp only [Weight.eventMass, Finset.sum_singleton, referenceRacePopulation,
      stalePopulation, singletonPopulation_weight, raceCoin_false]
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_sub_of_le (by
      rw [ENNReal.div_le_iff (by norm_num) (by norm_num)]
      norm_num) ENNReal.one_ne_top,
      ENNReal.toReal_sub_of_le (by norm_num) ENNReal.one_ne_top]
    norm_num

def stalePopulationBug :
    BugCert (populationSampler (referenceRacePopulation (1 / 2)))
      (populationSampler (stalePopulation (3 / 4))) Eq where
  s₀ := ()
  s₀' := ()
  deficit := by
    simpa only [populationSampler, Weight.pure_bind] using stalePopulationDeficit

theorem stale_population_contract_refuted :
    ¬ quadSem (populationSampler (referenceRacePopulation (1 / 2)))
      (populationSampler (stalePopulation (3 / 4)))
      (exactly (Weight.pure ()) (Weight.pure ())) (couple Eq) :=
  stalePopulationBug.refutes (exactly_self _ _)

end
end RelOL.Prob.ParallelSampling
