import RelationalOutcomeLogic.Examples.Probability.SpeculativeDecoding.Buffered

/-!
# Sufficient round fuel does not change a decoding run

Each nonempty verifier round consults its continuation with a strictly smaller
token budget. Consequently all round-fuel bounds covering the requested token
budget give the same distribution of complete `Run` values, including accounting
traces. Fuel is a device for structural recursion, not an observable parameter
once the sufficient-fuel condition is met. No unbounded-loop semantics is used.
-/

namespace RelOL.Prob.Speculative

variable {α β : Type*}

noncomputable section

/-- The verifier only consults continuation budgets at most `n.pred`: a
nonempty round has emitted a token before it starts another round. -/
theorem verifyBuffer_congr (p q : Model α)
    (resume resume' : ℕ → List α → RoundTrace → Weight β)
    (n : ℕ)
    (hresume : ∀ m ≤ n.pred, ∀ h trace, resume m h trace = resume' m h trace)
    (h buffer : List α) (drafted accepted : ℕ) :
    verifyBuffer p q resume n h buffer drafted accepted =
      verifyBuffer p q resume' n h buffer drafted accepted := by
  induction n generalizing h buffer accepted with
  | zero => exact hresume 0 le_rfl h _
  | succ n ih =>
    cases buffer with
    | nil =>
      simp only [verifyBuffer]
      apply congrArg (Weight.bind (p h).weight)
      funext y
      exact hresume n (by simp) _ _
    | cons x xs =>
      simp only [verifyBuffer]
      apply congrArg (Weight.bind (verify (p h) (q h) x))
      funext v
      cases hv : v.1 with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact hresume n (by simp) _ _
      | true =>
        simp only [↓reduceIte]
        exact ih (fun m hm => hresume m (by
          simpa only [Nat.pred_succ] using hm.trans (Nat.pred_le n))) _ xs _

/-- Sufficient round fuel is irrelevant to the complete run distribution,
including every round's work counters and rejection/bonus flags. -/
theorem decode_fuel_irrelevant (p q : Model α) (width : List α → ℕ → ℕ)
    (n r s : ℕ) (hr : n ≤ r) (hs : n ≤ s) (h : List α) :
    decode p q width r n h = decode p q width s n h := by
  induction r generalizing n s h with
  | zero =>
    have : n = 0 := Nat.eq_zero_of_le_zero hr
    subst n
    simp only [decode_zero_budget]
  | succ r ih =>
    cases n with
    | zero => simp only [decode_zero_budget]
    | succ n =>
      cases s with
      | zero => omega
      | succ s =>
        rw [decode, decode]
        apply congrArg (Weight.bind (draftBlock q h (width h (n + 1))))
        funext buffer
        apply verifyBuffer_congr
        intro m hm h' trace
        simp only [Nat.pred_succ] at hm
        exact congrArg (pushforward (Run.prepend trace))
          (ih m s (by omega) (by omega) h')

/-- The canonical run is the complete distribution computed by every
sufficient-fuel decoder, not merely an equal token projection. -/
theorem decode_eq_run (p q : Model α) (width : List α → ℕ → ℕ)
    (r n : ℕ) (hn : n ≤ r) (h : List α) :
    decode p q width r n h = run p q width n h :=
  decode_fuel_irrelevant p q width n r n hn le_rfl h

end
end RelOL.Prob.Speculative
