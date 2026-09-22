import RelationalOutcomeLogic.Examples.Probability.SpeculativeDecoding.OutcomeContracts
import RelationalOutcomeLogic.Examples.Probability.SpeculativeDecoding.Fuel
import RelationalOutcomeLogic.Examples.Probability.SpeculativeDecoding.RoundClipping
import RelationalOutcomeLogic.Examples.Probability.SpeculativeDecoding.Security
import RelationalOutcomeLogic.Examples.Probability.SpeculativeDecoding.Implementation

/-!
# Speculative decoding: correctness, work, privacy, and refutation

This is the case-study entry point. Read `Correction`, `Programs`, `StepContract`,
`Refinement`, `DecoderRules`, and `Buffered` for the correctness derivation, then
`Costs`, `OutcomeContracts`, and `Fuel` for accounting and sufficient-fuel independence.
`RoundLaw`, `RoundExpectation`, and `RoundClipping` give the conditional survival
law, exact expectations, and remaining-budget boundaries. `Counterexamples` and
`Implementation` give normalized, equal-support quantitative failures.
`Security` distinguishes token privacy from streaming-packet privacy and proves
the explicitly modeled buffered-release mitigation. The companion guide is
`docs/speculative-decoding.md`.

All statements concern exact discrete kernels and finite generation budgets.
Target calls are abstract batched verification rounds. Neither external model
code, floating-point sampling, cache management, nor physical timing is verified.
-/

namespace RelOL.Prob.Speculative

open scoped ENNReal

noncomputable section

/-- The wrong rejection continuation violates the very same quantitative split
proved by `step_outcome_quad`, even though its output support and mass agree. -/
theorem wrongFallback_outcome_contract_refuted :
    ¬ quadSem
      (fun μ : Weight Unit => Weight.bind μ (fun _ => fairTarget.weight))
      (fun μ : Weight Unit => Weight.bind μ
        (fun _ => wrongFallbackStep fairTarget alwaysTrueDraft))
      (exactly (Weight.pure ()) (Weight.pure ()))
      (stepSpec fairTarget alwaysTrueDraft) := by
  intro h
  have hs := h (Weight.pure ()) (Weight.pure ()) (exactly_self _ _)
  simp only [Weight.pure_bind] at hs
  exact wrongFallbackDeficit.refutes
    (coupled_eq_iff.mpr (stepSpec_observed_eq _ _ hs))

/-- A concrete adaptive policy; it depends only on the emitted prefix and budget. -/
def adaptiveWidth (h : List Bool) (remaining : ℕ) : ℕ :=
  min (if h.getLast? = some true then 3 else 1) remaining

/-- A checked client of the complete contract with an imperfect draft and a
nonconstant policy, parameterized by arbitrary public prompt and output length. -/
theorem adaptive_example (n : ℕ) (h : List Bool) :
    quadSem (fun μ => Weight.bind μ (autoregressive (fun _ => fairTarget) n))
      (fun μ => Weight.bind μ
        (run (fun _ => fairTarget) (fun _ => alwaysTrueDraft) adaptiveWidth n))
      (exactly (Weight.pure h) (Weight.pure h)) (resultSpec n h) :=
  decoder_outcome_quad _ _ _ n h

/-- An imperfect constant draft has conditional acceptance probability one half
at every accepted history, giving the geometric law for every block width. -/
theorem imperfect_round_expected_emitted (K : ℕ) (h : List Bool) :
    Weight.expectation
      (RoundLaw.round (fun _ => fairTarget) (fun _ => alwaysTrueDraft) K h)
      (fun out => (out.2.emitted : ℝ≥0∞)) =
      (1 - (1 / 2 : ℝ≥0∞) ^ (K + 1)) / (1 - (1 / 2 : ℝ≥0∞)) := by
  apply RoundLaw.expected_emitted_geometric
  · intro i _ h' _
    norm_num [acceptanceMass, Weight.mass, tsum_bool, overlap, alwaysTrueDraft, Weight.pure]
  · norm_num

/-- A perfect draft reaches the maximum possible round emission, including zero
remaining budget and a final round with no room for its bonus token. -/
theorem perfect_round_expected_emitted_clipped {α : Type*} (p : Model α)
    (K n : ℕ) (h : List α) :
    Weight.expectation (RoundLaw.roundWithBudget p p K n h)
      (fun out => (out.2.emitted : ℝ≥0∞)) = (min (K + 1) n : ℕ) := by
  apply RoundLaw.expected_emitted_clipped_rate_one
  intro i _ h' _
  exact acceptanceMass_self (p h')

/-- An empty output budget performs no speculative work, irrespective of policy. -/
theorem zero_budget {α : Type*} (p q : Model α) (width : List α → ℕ → ℕ)
    (h : List α) : run p q width 0 h = Weight.pure ⟨h, []⟩ := rfl

end
end RelOL.Prob.Speculative
