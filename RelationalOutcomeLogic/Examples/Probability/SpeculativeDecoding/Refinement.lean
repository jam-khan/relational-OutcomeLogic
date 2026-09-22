import RelationalOutcomeLogic.Examples.Probability.SpeculativeDecoding.Programs
import RelationalOutcomeLogic.Generic.Distributional
import RelationalOutcomeLogic.Generic.Loops.Bounded
import RelationalOutcomeLogic.Bridges.Probability

/-!
# Verifying a random buffer with distributional invariant rules

The invariant reconstructs a pending buffer from the draft model at its current
history. `BufferRefinement.local_square` verifies one transition; its proof uses
the elementary sampling laws. Sequencing, dispatch, and bounded recursion then
derive the complete verifier judgment for arbitrary input mixtures. The final
`buffered_eq_delayed` equality is a consequence of that derivation.
-/

namespace RelOL.Prob.Speculative

universe u
variable {α β : Type u}

noncomputable section

theorem autoregressive_isProbability (p : Model α) (n : ℕ) (h : List α) :
    Weight.IsProbability (autoregressive p n h) := by
  induction n generalizing h with
  | zero => exact Weight.isProbability_pure _
  | succ n ih => exact (p h).normalized.bind (fun x => ih (h ++ [x]))

theorem draftBlock_isProbability (q : Model α) (h : List α) (k : ℕ) :
    Weight.IsProbability (draftBlock q h k) := by
  induction k generalizing h with
  | zero => exact Weight.isProbability_pure _
  | succ k ih =>
    apply (q h).normalized.bind
    intro x
    simpa only [Weight.IsProbability, mass_pushforward] using ih (h ++ [x])

namespace BufferRefinement

/-- Abstract verifier state records the law of the pending proposals. -/
structure Pending (α : Type*) where
  history : List α
  pending : ℕ
  drafted : ℕ
  accepted : ℕ

/-- Concrete verifier state holds proposals that have already been sampled. -/
structure Buffered (α : Type*) where
  history : List α
  buffer : List α
  drafted : ℕ
  accepted : ℕ

/-- Conditional reconstruction of hidden random state. -/
def expansion (q : Model α) (s : Pending α) : Weight (Buffered α) :=
  pushforward (fun buffer => ⟨s.history, buffer, s.drafted, s.accepted⟩)
    (draftBlock q s.history s.pending)

/-- One delayed transition, returning either a pending state or a completed result. -/
def abstractStep (p q : Model α) (resume : ℕ → List α → RoundTrace → Weight β)
    (n : ℕ) (s : Pending α) : Weight (Sum (Pending α) β) :=
  match s.pending with
  | 0 => Weight.bind (p s.history).weight (fun y =>
      pushforward Sum.inr
        (resume n (s.history ++ [y]) ⟨s.drafted, s.accepted, false, true⟩))
  | k + 1 => Weight.bind (step (p s.history) (q s.history)) (fun v =>
      if v.1 then Weight.pure (.inl ⟨s.history ++ [v.2], k, s.drafted, s.accepted + 1⟩)
      else pushforward Sum.inr
        (resume n (s.history ++ [v.2]) ⟨s.drafted, s.accepted, true, false⟩))

/-- One eager transition consumes the stored head and preserves the stored suffix. -/
def concreteStep (p q : Model α) (resume : ℕ → List α → RoundTrace → Weight β)
    (n : ℕ) (s : Buffered α) : Weight (Sum (Buffered α) β) :=
  match s.buffer with
  | [] => Weight.bind (p s.history).weight (fun y =>
      pushforward Sum.inr
        (resume n (s.history ++ [y]) ⟨s.drafted, s.accepted, false, true⟩))
  | x :: xs => Weight.bind (verify (p s.history) (q s.history) x) (fun v =>
      if v.1 then Weight.pure (.inl ⟨s.history ++ [x], xs, s.drafted, s.accepted + 1⟩)
      else pushforward Sum.inr
        (resume n (s.history ++ [v.2]) ⟨s.drafted, s.accepted, true, false⟩))

private theorem return_reconstruct (q : Model α) (μ : Weight β) :
    Weight.bind (pushforward (Sum.inr : β → Sum (Pending α) β) μ)
      (Generic.extendReconstruction (expansion q)) =
      pushforward (Sum.inr : β → Sum (Buffered α) β) μ := by
  simp only [bind_pushforward, Generic.extendReconstruction]
  rfl

/-- The only buffer-specific commuting-square obligation: one transition keeps
the conditional suffix law after acceptance and discards it after rejection. -/
theorem local_square (p q : Model α)
    (resume : ℕ → List α → RoundTrace → Weight β) (n : ℕ) (s : Pending α) :
    Weight.bind (expansion q s) (concreteStep p q resume n) =
      Weight.bind (abstractStep p q resume n s)
        (Generic.extendReconstruction (expansion q)) := by
  rcases s with ⟨h, k, drafted, accepted⟩
  cases k with
  | zero =>
    simp only [expansion, draftBlock, pushforward_pure, Weight.pure_bind,
      concreteStep, abstractStep, Weight.bind_assoc, return_reconstruct]
  | succ k =>
    simp only [expansion, bind_pushforward, draftBlock, Weight.bind_assoc,
      concreteStep, abstractStep, step]
    apply congrArg (Weight.bind (q h).weight)
    funext x
    rw [Weight.bind_comm]
    apply Weight.bind_congr_on_support
    intro v hv
    rcases v with ⟨b, y⟩
    cases b with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, return_reconstruct]
      exact Weight.bind_const_of_isProbability _ (draftBlock_isProbability q (h ++ [x]) k) _
    | true =>
      have hy := verify_accepts_same (p h) (q h) x y hv
      subst y
      simp only [↓reduceIte, Weight.pure_bind, Generic.extendReconstruction,
        Generic.weight_bind_eq, Generic.weight_pure_eq, expansion, bind_pushforward]

/-- The local square is lifted to a judgment on arbitrary weighted histories. -/
theorem step_quad (p q : Model α)
    (resume : ℕ → List α → RoundTrace → Weight β) (n : ℕ) :
    Generic.quad (Generic.lifted (expansion q))
      (abstractStep p q resume n) (concreteStep p q resume n)
      (Generic.lifted (Generic.extendReconstruction (expansion q))) :=
  Generic.quad_lifted (local_square p q resume n)

def abstractLayer (p q : Model α) (resume : ℕ → List α → RoundTrace → Weight β)
    (n : ℕ) (k : Pending α → Weight β) (s : Pending α) : Weight β :=
  Weight.bind (abstractStep p q resume n s) (Generic.dispatch k)

def concreteLayer (p q : Model α) (resume : ℕ → List α → RoundTrace → Weight β)
    (n : ℕ) (k : Buffered α → Weight β) (s : Buffered α) : Weight β :=
  Weight.bind (concreteStep p q resume n s) (Generic.dispatch k)

/-- Sequencing a verified transition with a verified continuation establishes
the recursive layer. Its premise is a continuation specification, not the result
of executing the completed verifier. -/
theorem layer_quad (p q : Model α)
    (resume : ℕ → List α → RoundTrace → Weight β) (n : ℕ)
    (k : Pending α → Weight β) (l : Buffered α → Weight β)
    (hkl : Generic.quad (Generic.lifted (expansion q)) k l
      (Generic.lifted (Weight.pure : β → Weight β))) :
    Generic.quad (Generic.lifted (expansion q))
      (abstractLayer p q resume n k) (concreteLayer p q resume n l)
      (Generic.lifted (Weight.pure : β → Weight β)) :=
  Generic.quad_seq (step_quad p q resume n) (Generic.quad_lifted_dispatch hkl)

def abstractRun (p q : Model α) (resume : ℕ → List α → RoundTrace → Weight β)
    (n : ℕ) (s : Pending α) : Weight β :=
  delayed p q resume n s.history s.pending s.drafted s.accepted

def concreteRun (p q : Model α) (resume : ℕ → List α → RoundTrace → Weight β)
    (n : ℕ) (s : Buffered α) : Weight β :=
  verifyBuffer p q resume n s.history s.buffer s.drafted s.accepted

theorem abstractRun_unfold (p q : Model α)
    (resume : ℕ → List α → RoundTrace → Weight β) (n : ℕ) :
    abstractRun p q resume (n + 1) = abstractLayer p q resume n (abstractRun p q resume n) := by
  funext s
  rcases s with ⟨h, k, drafted, accepted⟩
  cases k with
  | zero =>
    simp [abstractRun, abstractLayer, abstractStep, delayed, Weight.bind_assoc,
      bind_pushforward, Generic.dispatch]
  | succ k =>
    simp only [abstractRun, abstractLayer, abstractStep, delayed, Weight.bind_assoc]
    apply congrArg (Weight.bind (step (p h) (q h)))
    funext v
    cases v.1 <;>
      simp [Weight.pure_bind, bind_pushforward, Generic.dispatch, abstractRun]

theorem concreteRun_unfold (p q : Model α)
    (resume : ℕ → List α → RoundTrace → Weight β) (n : ℕ) :
    concreteRun p q resume (n + 1) = concreteLayer p q resume n (concreteRun p q resume n) := by
  funext s
  rcases s with ⟨h, buffer, drafted, accepted⟩
  cases buffer with
  | nil =>
    simp [concreteRun, concreteLayer, concreteStep, verifyBuffer, Weight.bind_assoc,
      bind_pushforward, Generic.dispatch]
  | cons x xs =>
    simp only [concreteRun, concreteLayer, concreteStep, verifyBuffer, Weight.bind_assoc]
    apply congrArg (Weight.bind (verify (p h) (q h) x))
    funext v
    cases v.1 <;>
      simp [Weight.pure_bind, bind_pushforward, Generic.dispatch, concreteRun]

/-- Full verifier correctness is derived by the reusable bounded-recursion rule.
The input assertion retains the conditional buffer law for arbitrary mixtures. -/
theorem verifier_quad (p q : Model α)
    (resume : ℕ → List α → RoundTrace → Weight β) (n : ℕ) :
    Generic.quad (Generic.lifted (expansion q))
      (abstractRun p q resume n) (concreteRun p q resume n)
      (Generic.lifted (Weight.pure : β → Weight β)) := by
  apply Generic.quad_recursion (fun _ => Generic.lifted (expansion q))
    (Generic.lifted Weight.pure) (abstractRun p q resume) (concreteRun p q resume)
    (abstractLayer p q resume) (concreteLayer p q resume)
    (abstractRun_unfold p q resume) (concreteRun_unfold p q resume) ?_ ?_ n
  · apply Generic.quad_lifted
    intro s
    simp only [Generic.weight_bind_eq, expansion, bind_pushforward, abstractRun,
      concreteRun, delayed, verifyBuffer, Weight.bind_pure]
    exact Weight.bind_const_of_isProbability _
      (draftBlock_isProbability q s.history s.pending) _
  · exact layer_quad p q resume

end BufferRefinement

/-- The full-trace buffer equality follows from the distributional invariant
judgment. Local arithmetic occurs in `BufferRefinement.local_square`; recursion
and continuation composition are applications of the reusable logic rules. -/
theorem buffered_eq_delayed (p q : Model α)
    (resume : ℕ → List α → RoundTrace → Weight β)
    (n : ℕ) (h : List α) (k drafted accepted : ℕ) :
    Weight.bind (draftBlock q h k)
      (fun buffer => verifyBuffer p q resume n h buffer drafted accepted) =
      delayed p q resume n h k drafted accepted := by
  have hj := BufferRefinement.verifier_quad p q resume n
    (Weight.pure ⟨h, k, drafted, accepted⟩)
    (BufferRefinement.expansion q ⟨h, k, drafted, accepted⟩)
    (Generic.lifted_pure _ _)
  simpa only [Generic.lifted, Generic.weight_bind_eq, Weight.pure_bind,
    Weight.bind_pure, BufferRefinement.expansion, bind_pushforward,
    BufferRefinement.abstractRun, BufferRefinement.concreteRun] using hj

end
end RelOL.Prob.Speculative
