import RelationalOutcomeLogic.Prob.Refutation.Observation
import RelationalOutcomeLogic.Examples.Probability.Search.OutcomeContract
import RelationalOutcomeLogic.Examples.Probability.Search.Cost
import RelationalOutcomeLogic.Examples.Probability.Search.CachedRandomness

/-!
# Public entry point for the randomized-search case

This import exposes the commands, asynchronous correctness, quantitative outcome
contract, trial savings, and cached-randomness certificate. The final theorem below
uses the observed certificate to refute the same full-state contract established
by `search_outcome_quad`, with the cached command substituted for early exit.
-/

namespace RelOL.Prob.Search

noncomputable section

/-- The cached implementation fails the quantitative contract proved for early exit. -/
theorem cached_outcome_spec_refuted (T : Trial) (hzero : 0 < T.miss) (hone : T.miss < 1)
    {n : ℕ} (hn : 1 < n) :
    ¬ quad (exactly (seed n) (seed n)) (full T) (cached T) (resultSpec T n) := by
  have href : ¬ quadSem (semLift (cached T)) (semLift (full T))
      (exactly (seed n) (seed n)) (fun μ ν => resultSpec T n ν μ) :=
    (cached_bug T hzero hone hn).refutes_of_observation
      (F := semLift (cached T)) (G := semLift (full T))
      (f := Prod.snd) (g := Prod.snd)
      (exactly_self _ _)
      (fun _ _ h => coupled_eq_iff.mpr (resultSpec_observed_eq T n h).symm)
  intro h
  apply href
  rintro μ ν ⟨rfl, rfl⟩
  exact h _ _ (exactly_self _ _)

end

end RelOL.Prob.Search
