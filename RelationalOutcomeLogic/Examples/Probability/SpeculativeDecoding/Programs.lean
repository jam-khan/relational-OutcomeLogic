import RelationalOutcomeLogic.Examples.Probability.SpeculativeDecoding.Correction
import RelationalOutcomeLogic.Algebra.ENNReal.Sequencing

/-!
# Buffered speculative decoding programs

`decode` samples an entire autoregressive draft block before inspecting any
acceptance result. Rejection discards its unconsumed suffix. Complete acceptance
is followed by a target-model bonus token, unless the output budget is exhausted.
The result retains round counters independently of its token projection.

The width policy sees only the already emitted history and remaining budget.
`roundsBudget` makes the program structurally recursive; the correctness theorem
in `Buffered` shows that `outputBudget` rounds always suffice, including width zero.
These kernels are denotational programs, using the same `Weight.bind` as `Cmd`.
-/

namespace RelOL.Prob.Speculative

variable {α : Type*}

/-- A next-token model conditioned on the emitted or proposed history. -/
abbrev Model (α : Type*) := List α → Distribution α

/-- One verification round, including work on subsequently discarded proposals. -/
structure RoundTrace where
  drafted : ℕ
  accepted : ℕ
  corrected : Bool
  bonus : Bool
  deriving DecidableEq, Repr

/-- Observable token payload and internal accounting are kept separate. -/
structure Run (α : Type*) where
  tokens : List α
  rounds : List RoundTrace

namespace RoundTrace

/-- Tokens emitted by this round; correction and bonus are mutually exclusive. -/
def emitted (r : RoundTrace) : ℕ :=
  r.accepted + (if r.corrected then 1 else 0) + (if r.bonus then 1 else 0)

end RoundTrace

namespace Run

def prepend (r : RoundTrace) (run : Run α) : Run α :=
  { tokens := run.tokens, rounds := r :: run.rounds }

def targetCalls (run : Run α) : ℕ := run.rounds.length

def draftTokens (run : Run α) : ℕ := (run.rounds.map RoundTrace.drafted).sum

def acceptedTokens (run : Run α) : ℕ := (run.rounds.map RoundTrace.accepted).sum

def emittedTokens (run : Run α) : ℕ := (run.rounds.map RoundTrace.emitted).sum

end Run

noncomputable section

/-- Ordinary autoregressive decoding, retaining the supplied history. -/
def autoregressive (p : Model α) : ℕ → List α → Weight (List α)
  | 0, h => Weight.pure h
  | n + 1, h => Weight.bind (p h).weight (fun x => autoregressive p n (h ++ [x]))

/-- Sample a complete draft block, conditioning each proposal on earlier proposals. -/
def draftBlock (q : Model α) : List α → ℕ → Weight (List α)
  | _, 0 => Weight.pure []
  | h, k + 1 => Weight.bind (q h).weight (fun x =>
      pushforward (List.cons x) (draftBlock q (h ++ [x]) k))

/-- Verify a pre-sampled buffer. `resume` starts the next round and records the
finished round. Its history contains emitted tokens only, never discarded drafts. -/
def verifyBuffer {β : Type*} (p q : Model α)
    (resume : ℕ → List α → RoundTrace → Weight β) :
    ℕ → List α → List α → ℕ → ℕ → Weight β
  | 0, h, _, drafted, accepted =>
      resume 0 h ⟨drafted, accepted, false, false⟩
  | n + 1, h, [], drafted, accepted =>
      Weight.bind (p h).weight (fun y =>
        resume n (h ++ [y]) ⟨drafted, accepted, false, true⟩)
  | n + 1, h, x :: xs, drafted, accepted =>
      Weight.bind (verify (p h) (q h) x) (fun v =>
        if v.1 then
          verifyBuffer p q resume n (h ++ [x]) xs drafted (accepted + 1)
        else resume n (h ++ [v.2]) ⟨drafted, accepted, true, false⟩)

/-- A delayed-sampling specification. Unlike `verifyBuffer`, this samples the
next proposal only when it is needed. Equality holds after averaging the actual
buffer distribution; it is deliberately not asserted for individual buffers. -/
def delayed {β : Type*} (p q : Model α)
    (resume : ℕ → List α → RoundTrace → Weight β) :
    ℕ → List α → ℕ → ℕ → ℕ → Weight β
  | 0, h, _, drafted, accepted =>
      resume 0 h ⟨drafted, accepted, false, false⟩
  | n + 1, h, 0, drafted, accepted =>
      Weight.bind (p h).weight (fun y =>
        resume n (h ++ [y]) ⟨drafted, accepted, false, true⟩)
  | n + 1, h, k + 1, drafted, accepted =>
      Weight.bind (step (p h) (q h)) (fun v =>
        if v.1 then
          delayed p q resume n (h ++ [v.2]) k drafted (accepted + 1)
        else resume n (h ++ [v.2]) ⟨drafted, accepted, true, false⟩)

/-- The actual buffered decoder, including round-level operation counters.
Widths may vary with public history and remaining budget. Widths larger than
the budget are allowed but cause unnecessary draft work. -/
def decode (p q : Model α) (width : List α → ℕ → ℕ) :
    ℕ → ℕ → List α → Weight (Run α)
  | 0, _, h => Weight.pure ⟨h, []⟩
  | _ + 1, 0, h => Weight.pure ⟨h, []⟩
  | r + 1, n + 1, h =>
      let k := width h (n + 1)
      Weight.bind (draftBlock q h k) (fun buffer =>
        verifyBuffer p q (fun m h' trace =>
          pushforward (Run.prepend trace) (decode p q width r m h'))
          (n + 1) h buffer k 0)

/-- Fixed-width decoding with proposals clipped to the remaining output budget. -/
def fixedWidth (k : ℕ) : List α → ℕ → ℕ := fun _ n => min k n

/-- A complete run uses at most one round per requested token. -/
def run (p q : Model α) (width : List α → ℕ → ℕ)
    (n : ℕ) (h : List α) : Weight (Run α) := decode p q width n n h

end
end RelOL.Prob.Speculative
