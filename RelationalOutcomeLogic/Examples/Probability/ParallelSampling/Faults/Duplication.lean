import RelationalOutcomeLogic.Examples.Probability.ParallelSampling.Faults.Completion

/-!
# Duplicate delivery can preserve every marginal and still bias a population

The mutant samples the first value, then independently decides whether to reuse
that ticket as the second result. Otherwise it draws a fresh second ticket.
With fair values and a fair reuse decision both output marginals remain fair,
and all four populations retain positive mass, but the mixed pair loses half
its probability. The complete population contract detects this loss of independence.
-/

namespace RelOL.Prob.ParallelSampling

open scoped ENNReal
noncomputable section

def independentPair (θ : ℝ≥0∞) : Weight (Bool × Bool) :=
  Weight.bind (raceCoin θ) fun a => pushforward (fun b => (a, b)) (raceCoin θ)

def duplicationMutant (θ δ : ℝ≥0∞) : Weight (Bool × Bool) :=
  Weight.bind (raceCoin θ) fun a => Weight.bind (raceCoin δ) fun reuse =>
    if reuse then Weight.pure (a, a) else
      pushforward (fun b => (a, b)) (raceCoin θ)

theorem independentPair_apply (θ : ℝ≥0∞) (a b : Bool) :
    independentPair θ (a, b) = raceCoin θ a * raceCoin θ b := by
  cases a <;> cases b <;> simp [independentPair, pushforward, Weight.bind, Weight.pure]

theorem duplicationMutant_apply (θ δ : ℝ≥0∞) (a b : Bool) :
    duplicationMutant θ δ (a, b) =
      raceCoin θ a * ((1 - δ) * raceCoin θ b + if a = b then δ else 0) := by
  cases a <;> cases b <;> simp [duplicationMutant, pushforward, Weight.bind, Weight.pure, add_comm]

theorem independentPair_probability {θ : ℝ≥0∞} (hθ : θ ≤ 1) :
    Weight.IsProbability (independentPair θ) := by
  apply (raceCoin_isProbability hθ).bind
  intro a
  simpa only [Weight.IsProbability, mass_pushforward] using raceCoin_isProbability hθ

theorem duplicationMutant_probability {θ δ : ℝ≥0∞} (hθ : θ ≤ 1) (hδ : δ ≤ 1) :
    Weight.IsProbability (duplicationMutant θ δ) := by
  apply (raceCoin_isProbability hθ).bind
  intro a
  apply (raceCoin_isProbability hδ).bind
  intro reuse
  cases reuse with
  | false =>
      simpa only [Bool.false_eq_true, ↓reduceIte, Weight.IsProbability, mass_pushforward]
        using raceCoin_isProbability hθ
  | true => exact Weight.isProbability_pure _

theorem independentPair_fst {θ : ℝ≥0∞} (hθ : θ ≤ 1) :
    pushforward Prod.fst (independentPair θ) = raceCoin θ := by
  simp only [independentPair, pushforward, Weight.bind_assoc,
    Weight.pure_bind]
  simp only [Weight.bind_const_of_isProbability _ (raceCoin_isProbability hθ),
    Weight.bind_pure]

theorem independentPair_snd {θ : ℝ≥0∞} (hθ : θ ≤ 1) :
    pushforward Prod.snd (independentPair θ) = raceCoin θ := by
  simp only [independentPair, pushforward, Weight.bind_assoc,
    Weight.pure_bind, Weight.bind_pure,
    Weight.bind_const_of_isProbability _ (raceCoin_isProbability hθ)]

theorem duplicationMutant_fst {θ δ : ℝ≥0∞} (hθ : θ ≤ 1) (hδ : δ ≤ 1) :
    pushforward Prod.fst (duplicationMutant θ δ) = raceCoin θ := by
  rw [duplicationMutant, pushforward_bind]
  have hinner (a : Bool) :
      pushforward Prod.fst (Weight.bind (raceCoin δ) fun reuse =>
        if reuse then Weight.pure (a, a) else
          pushforward (fun b => (a, b)) (raceCoin θ)) = Weight.pure a := by
    rw [pushforward_bind]
    have hb (reuse : Bool) : pushforward Prod.fst
        (if reuse then Weight.pure (a, a) else
          pushforward (fun b => (a, b)) (raceCoin θ)) = Weight.pure a := by
      cases reuse with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, pushforward, Weight.bind_assoc,
            Weight.pure_bind]
          exact Weight.bind_const_of_isProbability _ (raceCoin_isProbability hθ) _
      | true => simp
    simp only [hb, Weight.bind_const_of_isProbability _ (raceCoin_isProbability hδ)]
  simp only [hinner, Weight.bind_pure]

theorem duplicationMutant_snd {θ δ : ℝ≥0∞} (hθ : θ ≤ 1) (hδ : δ ≤ 1) :
    pushforward Prod.snd (duplicationMutant θ δ) = raceCoin θ := by
  rw [duplicationMutant, Weight.bind_comm, pushforward_bind]
  have hinner (reuse : Bool) :
      pushforward Prod.snd (Weight.bind (raceCoin θ) fun a =>
        if reuse then Weight.pure (a, a) else
          pushforward (fun b => (a, b)) (raceCoin θ)) = raceCoin θ := by
    cases reuse with
    | false => exact independentPair_snd hθ
    | true => simp [pushforward, Weight.bind_assoc, Weight.pure_bind, Weight.bind_pure]
  simp only [hinner, Weight.bind_const_of_isProbability _ (raceCoin_isProbability hδ)]

/-- A complete two-person population, retaining order. -/
def pairPopulation (p : Bool × Bool) : Result Bool := .success [p.1, p.2]

theorem pairPopulation_weight (μ : Weight (Bool × Bool)) (a b : Bool) :
    pushforward pairPopulation μ (pairPopulation (a, b)) = μ (a, b) := by
  cases a <;> cases b <;>
    simp [pushforward, Weight.bind, Fintype.sum_prod_type, Weight.pure, pairPopulation]

def duplicatePopulationDeficit :
    MassDeficitCert Eq (pushforward pairPopulation (independentPair (1 / 2)))
      (pushforward pairPopulation (duplicationMutant (1 / 2) (1 / 2))) where
  left := {pairPopulation (false, true)}
  right := {pairPopulation (false, true)}
  cover := by intro a ha b hab; simpa only [← hab] using ha
  deficit := by
    simp only [Weight.eventMass, Finset.sum_singleton, pairPopulation_weight,
      independentPair_apply, duplicationMutant_apply, raceCoin_false, raceCoin_true]
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
    norm_num

def duplicatePopulationBug :
    BugCert (populationSampler (pushforward pairPopulation (independentPair (1 / 2))))
      (populationSampler (pushforward pairPopulation
        (duplicationMutant (1 / 2) (1 / 2)))) Eq where
  s₀ := ()
  s₀' := ()
  deficit := by
    simpa only [populationSampler, Weight.pure_bind] using duplicatePopulationDeficit

theorem duplicate_population_contract_refuted :
    ¬ quadSem (populationSampler (pushforward pairPopulation (independentPair (1 / 2))))
      (populationSampler (pushforward pairPopulation
        (duplicationMutant (1 / 2) (1 / 2))))
      (exactly (Weight.pure ()) (Weight.pure ())) (couple Eq) :=
  duplicatePopulationBug.refutes (exactly_self _ _)

theorem fair_duplication_same_support :
    Weight.support (duplicationMutant (1 / 2) (1 / 2)) =
      Weight.support (independentPair (1 / 2)) := by
  ext ⟨a, b⟩
  cases a <;> cases b <;>
    norm_num [Weight.support, duplicationMutant_apply, independentPair_apply]

end
end RelOL.Prob.ParallelSampling
