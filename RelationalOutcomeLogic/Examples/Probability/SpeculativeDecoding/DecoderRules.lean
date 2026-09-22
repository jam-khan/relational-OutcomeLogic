import RelationalOutcomeLogic.Examples.Probability.SpeculativeDecoding.Refinement
import RelationalOutcomeLogic.Examples.Probability.SpeculativeDecoding.StepContract
import RelationalOutcomeLogic.Generic.Loops.Bounded
import RelationalOutcomeLogic.Bridges.Probability

/-!
# Deriving bounded decoder correctness from local relational rules

The delayed verifier and complete decoder are derived by the indexed-family
bounded-recursion rule. Each layer is proved for arbitrary continuations that
satisfy the previous contracts. Sampling and observation use relational
sequencing; no correctness theorem for a completed decoder is a premise.
-/

namespace RelOL.Prob.Speculative

universe u
variable {α β γ δ σ : Type u}

noncomputable section

/-- Agreement after forgetting a concrete program's internal observations. -/
def observedBy (observe : β → γ) : Generic.RAssn Weight γ β :=
  fun μ ν => pushforward observe ν = μ

/-- Local continuation rule: matching observations before sequencing remain
matched when each concrete continuation refines its corresponding abstract one. -/
theorem quad_observed_continuation (project : δ → α) (observe : β → γ)
    (k : α → Weight γ) (l : δ → Weight β)
    (h : ∀ v, pushforward observe (l v) = k (project v)) :
    Generic.quad (observedBy project) k l (observedBy observe) := by
  intro μ ν hμν
  change pushforward observe (Weight.bind ν l) = Weight.bind μ k
  rw [pushforward_bind]
  simp_rw [h]
  rw [← bind_pushforward project ν k, show pushforward project ν = μ from hμν]

/-- Sequencing a sampler's local observation contract with a continuation
contract. The proof explicitly uses the common relational sequencing rule. -/
theorem quad_observed_sequence (s : σ) (μ : Weight α) (ν : Weight δ)
    (project : δ → α) (observe : β → γ)
    (hsample : pushforward project ν = μ)
    (k : α → Weight γ) (l : δ → Weight β)
    (hcontinue : ∀ v, pushforward observe (l v) = k (project v)) :
    Generic.quad (Generic.exactly (Weight.pure s) (Weight.pure s))
      (fun _ => Weight.bind μ k) (fun _ => Weight.bind ν l) (observedBy observe) := by
  have hs : Generic.quad (Generic.exactly (Weight.pure s) (Weight.pure s))
      (fun _ : σ => μ) (fun _ : σ => ν) (observedBy project) := by
    rintro _ _ ⟨rfl, rfl⟩
    simpa only [Generic.weight_bind_eq, Weight.pure_bind, observedBy] using hsample
  exact Generic.quad_seq hs (quad_observed_continuation project observe k l hcontinue)

private theorem observed_sequence (s : σ) (μ : Weight α) (ν : Weight δ)
    (project : δ → α) (observe : β → γ)
    (hsample : pushforward project ν = μ)
    (k : α → Weight γ) (l : δ → Weight β)
    (hcontinue : ∀ v, pushforward observe (l v) = k (project v)) :
    pushforward observe (Weight.bind ν l) = Weight.bind μ k := by
  have hh := quad_observed_sequence s μ ν project observe hsample k l hcontinue
    (Weight.pure s) (Weight.pure s) ⟨rfl, rfl⟩
  simpa only [Generic.weight_bind_eq, Weight.pure_bind, observedBy] using hh

/-- The ghost parameters needed to retain each pending continuation's contract. -/
abbrev DelayIndex (α : Type u) := BufferRefinement.Pending α

def delayInput (N n : ℕ) (s : DelayIndex α) : Generic.RAssn Weight (DelayIndex α) (DelayIndex α) :=
  fun μ ν => n ≤ N ∧ Generic.exactly (Weight.pure s) (Weight.pure s) μ ν

def delayPost (p : Model α) (observe : β → List α) (n : ℕ) (s : DelayIndex α) :
    Generic.RAssn Weight (List α) β :=
  fun μ ν => μ = autoregressive p n s.history ∧ observedBy observe μ ν

def targetDelayLayer (p : Model α) (_ : ℕ) (k : DelayIndex α → Weight (List α))
    (s : DelayIndex α) : Weight (List α) :=
  Weight.bind (p s.history).weight (fun x => k { s with history := s.history ++ [x] })

def verifierLayer (p q : Model α) (resume : ℕ → List α → RoundTrace → Weight β)
    (n : ℕ) (l : DelayIndex α → Weight β) (s : DelayIndex α) : Weight β :=
  match s.pending with
  | 0 => Weight.bind (p s.history).weight (fun y =>
      resume n (s.history ++ [y]) ⟨s.drafted, s.accepted, false, true⟩)
  | k + 1 => Weight.bind (step (p s.history) (q s.history)) (fun v =>
      if v.1 then l ⟨s.history ++ [v.2], k, s.drafted, s.accepted + 1⟩
      else resume n (s.history ++ [v.2]) ⟨s.drafted, s.accepted, true, false⟩)

/-- Rule-derived family for the delayed verifier. The reference postcondition
records each budget/history benchmark, allowing acceptance and resumed rounds
to consume the appropriate continuation contract. -/
theorem delayed_quad_family (p q : Model α)
    (resume : ℕ → List α → RoundTrace → Weight β) (observe : β → List α)
    (N : ℕ)
    (hresume : ∀ m ≤ N.pred, ∀ h trace,
      pushforward observe (resume m h trace) = autoregressive p m h)
    (n : ℕ) (s : DelayIndex α) :
    Generic.quad (delayInput N n s)
      (fun s => autoregressive p n s.history)
      (fun s => delayed p q resume n s.history s.pending s.drafted s.accepted)
      (delayPost p observe n s) := by
  apply Generic.quad_recursion_family (P := delayInput N) (Q := delayPost p observe)
    (F := fun n s => autoregressive p n s.history)
    (G := fun n s => delayed p q resume n s.history s.pending s.drafted s.accepted)
    (layerF := targetDelayLayer p) (layerG := verifierLayer p q resume)
  · intro n
    rfl
  · intro n
    funext s
    rcases s with ⟨h, k, d, a⟩
    cases k <;> rfl
  · intro s μ ν hpre
    obtain ⟨_, rfl, rfl⟩ := hpre
    change Weight.bind (Weight.pure s) _ = autoregressive p 0 s.history ∧
      pushforward observe (Weight.bind (Weight.pure s) _) = Weight.bind (Weight.pure s) _
    constructor
    · exact Weight.pure_bind _ _
    · simpa only [Weight.pure_bind, delayed] using hresume 0 (Nat.zero_le _) s.history _
  · intro n k l hkl s μ ν hpre
    obtain ⟨hN, rfl, rfl⟩ := hpre
    have hn : n ≤ N := by omega
    have hnp : n ≤ N.pred := Nat.le_pred_of_lt (by omega)
    have hlocal (t : DelayIndex α) :
        k t = autoregressive p n t.history ∧ pushforward observe (l t) = k t := by
      have hh := hkl t (Weight.pure t) (Weight.pure t) ⟨hn, rfl, rfl⟩
      simpa only [Generic.weight_bind_eq, Weight.pure_bind, delayPost, observedBy] using hh
    change Weight.bind (Weight.pure s) _ = autoregressive p (n + 1) s.history ∧
      pushforward observe (Weight.bind (Weight.pure s) _) = Weight.bind (Weight.pure s) _
    simp only [Weight.pure_bind]
    constructor
    · unfold targetDelayLayer
      rw [autoregressive]
      apply congrArg (Weight.bind (p s.history).weight)
      funext x
      exact (hlocal _).1
    · rcases s with ⟨h, pending, drafted, accepted⟩
      cases pending with
      | zero =>
        apply observed_sequence (⟨h, 0, drafted, accepted⟩ : DelayIndex α)
          (p h).weight (p h).weight id observe
          (by simp only [pushforward, id_eq, Weight.bind_pure])
        intro y
        exact (hresume n hnp _ _).trans
          (hlocal ⟨h ++ [y], 0, drafted, accepted⟩).1.symm
      | succ pending =>
        apply observed_sequence (⟨h, pending + 1, drafted, accepted⟩ : DelayIndex α)
          (p h).weight (step (p h) (q h)) Prod.snd observe
          (stepSpec_observed_eq _ _ (step_outcome_contract _ _)).symm
        intro v
        cases hb : v.1 with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact (hresume n hnp _ _).trans
            (hlocal ⟨h ++ [v.2], pending + 1, drafted, accepted⟩).1.symm
        | true =>
          simp only [↓reduceIte]
          exact (hlocal ⟨h ++ [v.2], pending, drafted, accepted + 1⟩).2.trans
            ((hlocal ⟨h ++ [v.2], pending, drafted, accepted + 1⟩).1.trans
              (hlocal ⟨h ++ [v.2], pending + 1, drafted, accepted⟩).1.symm)

/-- The observable statement extracted from the rule-derived verifier family. -/
theorem delayed_output (p q : Model α)
    (resume : ℕ → List α → RoundTrace → Weight β) (observe : β → List α)
    (n : ℕ)
    (hresume : ∀ m ≤ n.pred, ∀ h trace,
      pushforward observe (resume m h trace) = autoregressive p m h)
    (h : List α) (k drafted accepted : ℕ) :
    pushforward observe (delayed p q resume n h k drafted accepted) =
      autoregressive p n h := by
  let s : DelayIndex α := ⟨h, k, drafted, accepted⟩
  have hh := delayed_quad_family p q resume observe n hresume n s
    (Weight.pure s) (Weight.pure s) ⟨le_rfl, rfl, rfl⟩
  simpa only [Generic.weight_bind_eq, Weight.pure_bind, delayPost, observedBy] using hh.2

/-- Token projection erases a prepended round without changing the payload. -/
theorem pushforward_tokens_prepend (trace : RoundTrace) (μ : Weight (Run α)) :
    pushforward Run.tokens (pushforward (Run.prepend trace) μ) =
      pushforward Run.tokens μ := by
  simp only [pushforward, Weight.bind_assoc, Weight.pure_bind, Run.prepend]

/-- A continuation's remaining output budget and already emitted history. -/
structure DecoderIndex (α : Type u) where
  remaining : ℕ
  history : List α

def decoderInput (r : ℕ) (s : DecoderIndex α) :
    Generic.RAssn Weight (DecoderIndex α) (DecoderIndex α) :=
  fun μ ν => s.remaining ≤ r ∧ Generic.exactly (Weight.pure s) (Weight.pure s) μ ν

def decoderPost (p : Model α) (_ : ℕ) (s : DecoderIndex α) :
    Generic.RAssn Weight (List α) (Run α) :=
  fun μ ν => μ = autoregressive p s.remaining s.history ∧ observedBy Run.tokens μ ν

def targetDecoderLayer (p : Model α) (_ : ℕ)
    (k : DecoderIndex α → Weight (List α)) (s : DecoderIndex α) : Weight (List α) :=
  match s.remaining with
  | 0 => Weight.pure s.history
  | n + 1 => Weight.bind (p s.history).weight (fun x => k ⟨n, s.history ++ [x]⟩)

def bufferedDecoderLayer (p q : Model α) (width : List α → ℕ → ℕ) (_ : ℕ)
    (l : DecoderIndex α → Weight (Run α)) (s : DecoderIndex α) : Weight (Run α) :=
  match s.remaining with
  | 0 => Weight.pure ⟨s.history, []⟩
  | n + 1 =>
      let k := width s.history (n + 1)
      Weight.bind (draftBlock q s.history k) (fun buffer =>
        verifyBuffer p q (fun m h' trace => pushforward (Run.prepend trace) (l ⟨m, h'⟩))
          (n + 1) s.history buffer k 0)

/-- Indexed recursive derivation for the complete decoder. The reference kernel
uses its own one-token layers; the optimized kernel uses one entire buffered
round. The continuation family relates all remaining budgets covered by fuel. -/
theorem decoder_quad_family (p q : Model α) (width : List α → ℕ → ℕ)
    (r : ℕ) (s : DecoderIndex α) :
    Generic.quad (decoderInput r s)
      (fun s => autoregressive p (min r s.remaining) s.history)
      (fun s => decode p q width r s.remaining s.history) (decoderPost p r s) := by
  apply Generic.quad_recursion_family (P := decoderInput) (Q := decoderPost p)
    (F := fun r s => autoregressive p (min r s.remaining) s.history)
    (G := fun r s => decode p q width r s.remaining s.history)
    (layerF := targetDecoderLayer p) (layerG := bufferedDecoderLayer p q width)
  · intro r
    funext s
    rcases s with ⟨n, h⟩
    cases n with
    | zero => simp only [Nat.min_zero, autoregressive, targetDecoderLayer]
    | succ n => simp only [Nat.succ_min_succ, autoregressive, targetDecoderLayer]
  · intro r
    funext s
    rcases s with ⟨n, h⟩
    cases n <;> rfl
  · intro s μ ν hpre
    obtain ⟨hzero, rfl, rfl⟩ := hpre
    have hz : s.remaining = 0 := Nat.eq_zero_of_le_zero hzero
    change Weight.bind (Weight.pure s) _ = autoregressive p s.remaining s.history ∧
      pushforward Run.tokens (Weight.bind (Weight.pure s) _) = Weight.bind (Weight.pure s) _
    simp only [Weight.pure_bind, hz, Nat.min_zero, autoregressive, decode, pushforward_pure]
    constructor <;> trivial
  · intro r k l hkl s μ ν hpre
    obtain ⟨hr, rfl, rfl⟩ := hpre
    have hlocal (t : DecoderIndex α) (ht : t.remaining ≤ r) :
        k t = autoregressive p t.remaining t.history ∧
          pushforward Run.tokens (l t) = k t := by
      have hh := hkl t (Weight.pure t) (Weight.pure t) ⟨ht, rfl, rfl⟩
      simpa only [Generic.weight_bind_eq, Weight.pure_bind, decoderPost, observedBy] using hh
    change Weight.bind (Weight.pure s) _ = autoregressive p s.remaining s.history ∧
      pushforward Run.tokens (Weight.bind (Weight.pure s) _) = Weight.bind (Weight.pure s) _
    simp only [Weight.pure_bind]
    rcases s with ⟨n, h⟩
    cases n with
    | zero =>
      simp only [targetDecoderLayer, bufferedDecoderLayer, autoregressive, pushforward_pure]
      constructor <;> trivial
    | succ n =>
      have hn : n ≤ r := by simpa using hr
      have hleft : targetDecoderLayer p r k ⟨n + 1, h⟩ = autoregressive p (n + 1) h := by
        unfold targetDecoderLayer
        rw [autoregressive]
        apply congrArg (Weight.bind (p h).weight)
        funext x
        exact (hlocal ⟨n, h ++ [x]⟩ hn).1
      refine ⟨hleft, ?_⟩
      rw [hleft]
      change pushforward Run.tokens
        (Weight.bind (draftBlock q h (width h (n + 1))) (fun buffer =>
          verifyBuffer p q (fun m h' trace => pushforward (Run.prepend trace) (l ⟨m, h'⟩))
            (n + 1) h buffer (width h (n + 1)) 0)) = _
      rw [buffered_eq_delayed]
      apply delayed_output
      intro m hm h' trace
      rw [pushforward_tokens_prepend]
      have hm' : m ≤ r := by simp only [Nat.pred_succ] at hm; omega
      exact (hlocal ⟨m, h'⟩ hm').2.trans (hlocal ⟨m, h'⟩ hm').1

/-- Output equality is extracted from the complete indexed derivation. -/
theorem decode_output (p q : Model α) (width : List α → ℕ → ℕ)
    (r n : ℕ) (hn : n ≤ r) (h : List α) :
    pushforward Run.tokens (decode p q width r n h) = autoregressive p n h := by
  let s : DecoderIndex α := ⟨n, h⟩
  have hh := decoder_quad_family p q width r s
    (Weight.pure s) (Weight.pure s) ⟨hn, rfl, rfl⟩
  have he := hh.2.trans hh.1
  simpa only [Generic.weight_bind_eq, Weight.pure_bind, observedBy] using he

end
end RelOL.Prob.Speculative
