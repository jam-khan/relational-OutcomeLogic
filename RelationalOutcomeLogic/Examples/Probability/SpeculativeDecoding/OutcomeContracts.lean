import RelationalOutcomeLogic.Examples.Probability.SpeculativeDecoding.Costs
import RelationalOutcomeLogic.Examples.Probability.SpeculativeDecoding.StepContract

/-!
# Complete-run relational outcome contracts for speculative decoding

The complete-run contract combines target-distributed payloads with normalization
and accounting of the actual eager-buffer trace. Decoder correctness consumes the
rule-derived local split in `StepContract`; this module assembles its final
observable and accounting consequences into one pRelOL postcondition.
-/

namespace RelOL.Prob.Speculative

variable {α : Type*}

noncomputable section

/-- Output agreement, completion, and exact trace accounting in one postcondition. -/
def resultSpec (n : ℕ) (h : List α) : RAssn (List α) (Run α) :=
  fun μ ν => couple (fun tokens result => tokens = result.tokens) μ ν ∧
    massEq 1 1 μ ν ∧
    ∀ result ∈ Weight.support ν,
      result.tokens.length = h.length + n ∧ Accounted n result

theorem run_outcome_contract (p q : Model α) (width : List α → ℕ → ℕ)
    (n : ℕ) (h : List α) :
    resultSpec n h (autoregressive p n h) (run p q width n h) := by
  refine ⟨?_, ⟨autoregressive_isProbability p n h,
    run_isProbability p q width n h⟩, ?_⟩
  · rw [← run_output p q width n h]
    have hc := (coupled_eq_iff.mpr (rfl : run p q width n h = run p q width n h)).pushforward
      (S := fun tokens result => tokens = result.tokens)
      Run.tokens id (fun a b hab => congrArg Run.tokens hab)
    simpa only [couple, pushforward, id_eq, Weight.bind_pure] using hc
  · intro result hr
    exact ⟨decode_length p q width n n le_rfl h result hr,
      decode_accounted p q width n n le_rfl h result hr⟩

/-- The complete buffered program satisfies the same pRelOL judgment used by
the rest of the development, instantiated with its denotational kernels. -/
theorem decoder_outcome_quad (p q : Model α) (width : List α → ℕ → ℕ)
    (n : ℕ) (h : List α) :
    quadSem (fun μ => Weight.bind μ (autoregressive p n))
      (fun μ => Weight.bind μ (run p q width n))
      (exactly (Weight.pure h) (Weight.pure h)) (resultSpec n h) := by
  rintro μ ν ⟨rfl, rfl⟩
  simpa only [Weight.pure_bind] using run_outcome_contract p q width n h

end
end RelOL.Prob.Speculative
