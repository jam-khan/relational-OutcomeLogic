import RelationalOutcomeLogic.Examples.Probability.SpeculativeDecoding.DecoderRules

/-!
# Complete buffered decoder: normalization, length, and public run API

The distributional buffer invariant is proved in `Refinement`; local relational
rules derive verifier and decoder correctness in `DecoderRules`. This module
collects their consequences for complete, sufficiently fueled executions.
-/

namespace RelOL.Prob.Speculative

variable {α : Type*}

noncomputable section

@[simp] theorem decode_zero_budget (p q : Model α) (width : List α → ℕ → ℕ)
    (r : ℕ) (h : List α) : decode p q width r 0 h = Weight.pure ⟨h, []⟩ := by
  cases r <;> rfl

/-- The observable equality also establishes almost-sure completion of each
finite run: no mass is lost in rejection, suffix disposal, or round recursion. -/
theorem decode_isProbability (p q : Model α) (width : List α → ℕ → ℕ)
    (r n : ℕ) (hn : n ≤ r) (h : List α) :
    Weight.IsProbability (decode p q width r n h) := by
  have hm := congrArg Weight.mass (decode_output p q width r n hn h)
  rw [mass_pushforward, autoregressive_isProbability p n h] at hm
  exact hm

theorem autoregressive_length (p : Model α) (n : ℕ) (h out : List α)
    (hout : out ∈ Weight.support (autoregressive p n h)) :
    out.length = h.length + n := by
  induction n generalizing h with
  | zero =>
    have : out = h := by simpa only [autoregressive, Weight.support_pure,
      Set.mem_singleton_iff] using hout
    simp [this]
  | succ n ih =>
    obtain ⟨x, _, hx⟩ := (Weight.mem_support_bind_iff _ _ _).mp hout
    have := ih (h ++ [x]) hx
    simp only [List.length_append, List.length_singleton] at this
    omega

/-- The instrumented decoder emits exactly the budgeted number of new tokens. -/
theorem decode_length (p q : Model α) (width : List α → ℕ → ℕ)
    (r n : ℕ) (hn : n ≤ r) (h : List α) (result : Run α)
    (hr : result ∈ Weight.support (decode p q width r n h)) :
    result.tokens.length = h.length + n := by
  apply autoregressive_length p n h
  rw [← decode_output p q width r n hn h]
  exact (Weight.mem_support_bind_iff _ _ _).mpr
    ⟨result, hr, by simp only [Weight.support_pure, Set.mem_singleton_iff]⟩

theorem run_output (p q : Model α) (width : List α → ℕ → ℕ) (n : ℕ) (h : List α) :
    pushforward Run.tokens (run p q width n h) = autoregressive p n h :=
  decode_output p q width n n le_rfl h

theorem run_isProbability (p q : Model α) (width : List α → ℕ → ℕ)
    (n : ℕ) (h : List α) : Weight.IsProbability (run p q width n h) :=
  decode_isProbability p q width n n le_rfl h

end
end RelOL.Prob.Speculative
