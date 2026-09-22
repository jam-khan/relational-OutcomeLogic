import RelationalOutcomeLogic.Examples.Probability.SpeculativeDecoding.Buffered
import RelationalOutcomeLogic.Algebra.ENNReal.Expectation

/-!
# Exact operation accounting for buffered decoding

Counters refer to abstract batched target-verification rounds and draft-token
evaluations. They are not measurements of latency. These support theorems apply
to the actual pre-sampled decoder and charge proposals even when later discarded.
-/

namespace RelOL.Prob.Speculative

variable {α β : Type*}

noncomputable section

theorem draftBlock_length (q : Model α) (h buffer : List α) (k : ℕ)
    (hb : buffer ∈ Weight.support (draftBlock q h k)) : buffer.length = k := by
  induction k generalizing h buffer with
  | zero =>
    have : buffer = [] := by simpa only [draftBlock, Weight.support_pure,
      Set.mem_singleton_iff] using hb
    simp [this]
  | succ k ih =>
    obtain ⟨x, _, hx⟩ := (Weight.mem_support_bind_iff _ _ _).mp hb
    obtain ⟨xs, hxs, hcons⟩ := (Weight.mem_support_bind_iff _ _ _).mp hx
    have : buffer = x :: xs := by simpa only [Weight.support_pure,
      Set.mem_singleton_iff] using hcons
    subst buffer
    simp only [List.length_cons, ih (h ++ [x]) xs hxs]

/-- The precise obligations at the boundary between verification rounds. -/
structure RoundExit (n : ℕ) (h buffer : List α) (drafted accepted : ℕ)
    (m : ℕ) (h' : List α) (trace : RoundTrace) : Prop where
  remaining_le : m ≤ n
  history_length : h'.length + m = h.length + n
  emitted : trace.emitted + m = accepted + n
  drafted_eq : trace.drafted = drafted
  accepted_le : trace.accepted ≤ accepted + buffer.length
  progress : 0 < n → m < n
  exclusive : (trace.corrected && trace.bonus) = false

/-- Every execution of a verifier leaves through a continuation satisfying the
same budget and trace accounting invariant, irrespective of acceptance choices. -/
theorem verifyBuffer_support (p q : Model α)
    (resume : ℕ → List α → RoundTrace → Weight β)
    (n : ℕ) (h buffer : List α) (drafted accepted : ℕ) (result : β)
    (hr : result ∈ Weight.support
      (verifyBuffer p q resume n h buffer drafted accepted)) :
    ∃ m h' trace, RoundExit n h buffer drafted accepted m h' trace ∧
      result ∈ Weight.support (resume m h' trace) := by
  induction n generalizing h buffer accepted with
  | zero =>
    refine ⟨0, h, ⟨drafted, accepted, false, false⟩, ?_, hr⟩
    constructor <;> simp [RoundTrace.emitted]
  | succ n ih =>
    cases buffer with
    | nil =>
      obtain ⟨y, _, hy⟩ := (Weight.mem_support_bind_iff _ _ _).mp hr
      refine ⟨n, h ++ [y], ⟨drafted, accepted, false, true⟩, ?_, hy⟩
      constructor <;> simp [RoundTrace.emitted] <;> omega
    | cons x xs =>
      obtain ⟨v, _, hv⟩ := (Weight.mem_support_bind_iff _ _ _).mp hr
      cases hb : v.1 with
      | false =>
        simp only [hb, Bool.false_eq_true, ↓reduceIte] at hv
        refine ⟨n, h ++ [v.2], ⟨drafted, accepted, true, false⟩, ?_, hv⟩
        constructor <;> simp [RoundTrace.emitted] <;> omega
      | true =>
        simp only [hb, ↓reduceIte] at hv
        obtain ⟨m, h', trace, he, hr'⟩ := ih (h ++ [x]) xs (accepted + 1) hv
        refine ⟨m, h', trace, ?_, hr'⟩
        have hh := he.history_length
        have hm := he.remaining_le
        have hem := he.emitted
        have ha := he.accepted_le
        simp only [List.length_append, List.length_singleton] at hh
        constructor
        · omega
        · omega
        · omega
        · exact he.drafted_eq
        · simp only [List.length_cons]; omega
        · omega
        · exact he.exclusive

/-- Accounting invariant for a completed decoder execution. -/
structure Accounted (n : ℕ) (result : Run α) : Prop where
  emitted : result.emittedTokens = n
  rounds_le : result.targetCalls ≤ n
  traces : ∀ trace ∈ result.rounds,
    trace.accepted ≤ trace.drafted ∧ 0 < trace.emitted ∧
      (trace.corrected && trace.bonus) = false

/-- Each round makes progress, every emitted token is charged exactly once,
and discarded proposals remain charged to their original round. -/
theorem decode_accounted (p q : Model α) (width : List α → ℕ → ℕ)
    (r n : ℕ) (hn : n ≤ r) (h : List α) (result : Run α)
    (hr : result ∈ Weight.support (decode p q width r n h)) : Accounted n result := by
  induction r generalizing n h result with
  | zero =>
    have : n = 0 := Nat.eq_zero_of_le_zero hn
    subst n
    have : result = ⟨h, []⟩ := by simpa only [decode, Weight.support_pure,
      Set.mem_singleton_iff] using hr
    subst result
    constructor <;> simp [Run.emittedTokens, Run.targetCalls]
  | succ r ih =>
    cases n with
    | zero =>
      have : result = ⟨h, []⟩ := by simpa only [decode, Weight.support_pure,
        Set.mem_singleton_iff] using hr
      subst result
      constructor <;> simp [Run.emittedTokens, Run.targetCalls]
    | succ n =>
      obtain ⟨buffer, hb, hv⟩ := (Weight.mem_support_bind_iff _ _ _).mp hr
      obtain ⟨m, h', trace, he, hr'⟩ := verifyBuffer_support p q _
        (n + 1) h buffer (width h (n + 1)) 0 result hv
      obtain ⟨tail, htail, hresult⟩ := (Weight.mem_support_bind_iff _ _ _).mp hr'
      have hresult : result = Run.prepend trace tail := by
        simpa only [Weight.support_pure, Set.mem_singleton_iff] using hresult
      subst result
      have hm : m < n + 1 := he.progress (by omega)
      have hc := ih m (by omega) h' tail htail
      have hb := draftBlock_length q h buffer (width h (n + 1)) hb
      have hem := he.emitted
      have ha := he.accepted_le
      have hd := he.drafted_eq
      constructor
      · simp only [Run.emittedTokens, Run.prepend, List.map_cons, List.sum_cons]
        change trace.emitted + tail.emittedTokens = n + 1
        rw [hc.emitted]
        omega
      · simp only [Run.targetCalls, Run.prepend, List.length_cons]
        have ht := hc.rounds_le
        change tail.rounds.length ≤ m at ht
        omega
      · intro t ht
        simp only [Run.prepend, List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact ⟨by omega, by omega, he.exclusive⟩
        · exact hc.traces t ht

/-- A uniform adaptive-width bound applies to every charged round, including a
round whose proposed suffix is later discarded or clipped by the token budget. -/
theorem decode_trace_bound (p q : Model α) (width : List α → ℕ → ℕ)
    (K : ℕ) (hwidth : ∀ h n, width h n ≤ K)
    (r n : ℕ) (h : List α) (result : Run α)
    (hr : result ∈ Weight.support (decode p q width r n h)) :
    ∀ trace ∈ result.rounds, trace.drafted ≤ K := by
  induction r generalizing n h result with
  | zero =>
    have : result = ⟨h, []⟩ := by simpa only [decode, Weight.support_pure,
      Set.mem_singleton_iff] using hr
    subst result
    simp
  | succ r ih =>
    cases n with
    | zero =>
      have : result = ⟨h, []⟩ := by simpa only [decode, Weight.support_pure,
        Set.mem_singleton_iff] using hr
      subst result
      simp
    | succ n =>
      obtain ⟨buffer, _, hv⟩ := (Weight.mem_support_bind_iff _ _ _).mp hr
      obtain ⟨m, h', trace, he, hr'⟩ := verifyBuffer_support p q _
        (n + 1) h buffer (width h (n + 1)) 0 result hv
      obtain ⟨tail, htail, hresult⟩ := (Weight.mem_support_bind_iff _ _ _).mp hr'
      have hresult : result = Run.prepend trace tail := by
        simpa only [Weight.support_pure, Set.mem_singleton_iff] using hresult
      subst result
      intro t ht
      simp only [Run.prepend, List.mem_cons] at ht
      rcases ht with rfl | ht
      · rw [he.drafted_eq]
        exact hwidth _ _
      · exact ih m h' tail htail t ht

private theorem sum_drafted_le (traces : List RoundTrace) (K : ℕ)
    (hb : ∀ t ∈ traces, t.drafted ≤ K) :
    (traces.map RoundTrace.drafted).sum ≤ K * traces.length := by
  induction traces with
  | nil => simp
  | cons t ts ih =>
    have ht := hb t (by simp)
    have hs := ih (fun t hm => hb t (by simp [hm]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ]
    omega

/-- Pathwise bound on all draft evaluations, including discarded work. -/
theorem decode_draft_bound (p q : Model α) (width : List α → ℕ → ℕ)
    (K : ℕ) (hwidth : ∀ h n, width h n ≤ K)
    (r n : ℕ) (hn : n ≤ r) (h : List α) (result : Run α)
    (hr : result ∈ Weight.support (decode p q width r n h)) :
    result.draftTokens ≤ K * n := by
  have hb := sum_drafted_le result.rounds K
    (decode_trace_bound p q width K hwidth r n h result hr)
  exact hb.trans (Nat.mul_le_mul_left K (decode_accounted p q width r n hn h result hr).rounds_le)

/-- Fixed-width drafting is a specialization of the adaptive accounting theorem. -/
theorem fixed_draft_bound (p q : Model α) (K n : ℕ) (h : List α) (result : Run α)
    (hr : result ∈ Weight.support (run p q (fixedWidth K) n h)) :
    result.draftTokens ≤ K * n :=
  decode_draft_bound p q (fixedWidth K) K (fun _ _ => Nat.min_le_left _ _)
    n n le_rfl h result hr

open scoped ENNReal

/-- Expected abstract target-verification rounds are at most the token budget. -/
theorem expected_targetCalls_le (p q : Model α) (width : List α → ℕ → ℕ)
    (n : ℕ) (h : List α) :
    Weight.expectation (run p q width n h) (fun r => (r.targetCalls : ℝ≥0∞)) ≤ n := by
  apply Weight.expectation_le_of_bound (run_isProbability p q width n h)
  intro result hr
  exact_mod_cast (decode_accounted p q width n n le_rfl h result hr).rounds_le

/-- Expected work includes every sampled draft token, even rejected suffixes. -/
theorem expected_draftTokens_le (p q : Model α) (width : List α → ℕ → ℕ)
    (K : ℕ) (hwidth : ∀ h n, width h n ≤ K) (n : ℕ) (h : List α) :
    Weight.expectation (run p q width n h) (fun r => (r.draftTokens : ℝ≥0∞)) ≤
      (K * n : ℕ) := by
  apply Weight.expectation_le_of_bound (run_isProbability p q width n h)
  intro result hr
  exact_mod_cast decode_draft_bound p q width K hwidth n n le_rfl h result hr

/-- A perfect draft consumes each proposal, then obtains one bonus token.
The accumulated acceptance count is reflected in the final round boundary. -/
theorem delayed_perfect (p : Model α)
    (resume : ℕ → List α → RoundTrace → Weight β)
    (k : ℕ) (h : List α) (drafted accepted : ℕ) :
    delayed p p resume (k + 1) h k drafted accepted =
      Weight.bind (autoregressive p (k + 1) h)
        (fun out => resume 0 out ⟨drafted, accepted + k, false, true⟩) := by
  induction k generalizing h accepted with
  | zero =>
    simp only [delayed, autoregressive, Weight.bind_assoc, Weight.pure_bind,
      Nat.add_zero]
  | succ k ih =>
    simp only [delayed, step_self, bind_pushforward, ↓reduceIte]
    rw [autoregressive, Weight.bind_assoc]
    apply congrArg (Weight.bind (p h).weight)
    funext x
    simpa only [Nat.add_assoc, Nat.add_comm 1 k] using ih (h ++ [x]) (accepted + 1)

/-- An arbitrary perfect width-`k` draft emits `k+1` exact target tokens in one
batched target-verification call, with exactly `k` draft evaluations. -/
theorem perfect_single_round (p : Model α) (k : ℕ) (h : List α) :
    run p p (fixedWidth k) (k + 1) h =
      pushforward (fun out => (⟨out, [⟨k, k, false, true⟩]⟩ : Run α))
        (autoregressive p (k + 1) h) := by
  have hwidth : fixedWidth k h (k + 1) = k := Nat.min_eq_left (by omega)
  simp only [run, decode, hwidth]
  rw [buffered_eq_delayed, delayed_perfect]
  simp only [decode_zero_budget, pushforward_pure, Run.prepend, Nat.zero_add]
  rfl

/-- Exact expected cost of the perfect-draft batching witness. -/
theorem expected_perfect_single_round_calls (p : Model α) (k : ℕ) (h : List α) :
    Weight.expectation (run p p (fixedWidth k) (k + 1) h)
      (fun result => (result.targetCalls : ℝ≥0∞)) = 1 := by
  rw [perfect_single_round, pushforward, Weight.expectation_bind]
  simp only [Weight.expectation_pure, Run.targetCalls, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.cast_one]
  rw [Weight.expectation_const, autoregressive_isProbability, one_mul]

/-- With a perfect draft, one proposal plus its target bonus emits two tokens in
one target-verification round. This equality retains the exact output law and
the entire accounting trace, not just an upper bound on its expectation. -/
theorem perfect_two_token_run (p : Model α) (h : List α) :
    run p p (fixedWidth 1) 2 h =
      pushforward (fun out => (⟨out, [⟨1, 1, false, true⟩]⟩ : Run α))
        (autoregressive p 2 h) := perfect_single_round p 1 h

/-- A concrete strict saving: two exact target-distributed tokens cost one
abstract target-verification call with a perfect width-one draft. -/
theorem expected_perfect_two_token_calls (p : Model α) (h : List α) :
    Weight.expectation (run p p (fixedWidth 1) 2 h)
      (fun result => (result.targetCalls : ℝ≥0∞)) = 1 :=
  expected_perfect_single_round_calls p 1 h

/-- A completed one-token run has exactly one target-verification round. -/
theorem Accounted.one_target_call {result : Run α} (ha : Accounted 1 result) :
    result.targetCalls = 1 := by
  cases hrounds : result.rounds with
  | nil =>
    have he := ha.emitted
    simp [Run.emittedTokens, hrounds] at he
  | cons trace tail =>
    have hb := ha.rounds_le
    simp only [Run.targetCalls, hrounds, List.length_cons] at hb ⊢
    omega

private theorem calls_prepend_one (trace : RoundTrace) (μ : Weight (Run α))
    (hμ : Weight.IsProbability μ) (ha : ∀ result ∈ Weight.support μ, Accounted 1 result) :
    pushforward Run.targetCalls (pushforward (Run.prepend trace) μ) = Weight.pure 2 := by
  change Weight.bind (pushforward (Run.prepend trace) μ)
    (fun result => Weight.pure result.targetCalls) = _
  rw [bind_pushforward]
  change Weight.bind μ (fun result => Weight.pure (result.targetCalls + 1)) = _
  trans Weight.bind μ (fun _ => Weight.pure 2)
  · apply Weight.bind_congr_on_support
    intro result hr
    rw [(ha result hr).one_target_call]
  · exact Weight.bind_const_of_isProbability μ hμ _

/-- The complete two-token run costs one call on first acceptance and two on
first rejection, independently of how its remaining token is produced. -/
theorem two_token_targetCalls (p q : Model α) (h : List α) :
    pushforward Run.targetCalls (run p q (fixedWidth 1) 2 h) =
      pushforward (fun v : Bool × α => if v.1 then 1 else 2) (step (p h) (q h)) := by
  rw [run, decode]
  simp only [fixedWidth, Nat.min_eq_left (by omega : 1 ≤ 2)]
  rw [buffered_eq_delayed]
  simp only [delayed]
  rw [pushforward_bind]
  change Weight.bind (step (p h) (q h)) _ = Weight.bind (step (p h) (q h)) _
  congr 1
  funext v
  rcases v with ⟨b, x⟩
  cases b
  · simp only [Bool.false_eq_true, if_false]
    rw [calls_prepend_one _ _ (decode_isProbability p q _ 1 1 le_rfl _)
      (fun result hr => decode_accounted p q _ 1 1 le_rfl _ result hr)]
  · simp only [if_true]
    rw [pushforward_bind]
    simp only [decode, pushforward_pure, Run.targetCalls, Run.prepend,
      List.length_cons, List.length_nil, Nat.zero_add]
    exact Weight.bind_const_of_isProbability _ (p _).normalized _

/-- Exact expected target-call cost for arbitrary, potentially imperfect drafts.
The saving over two autoregressive calls is their accepted overlap mass. -/
theorem expected_two_token_calls (p q : Model α) (h : List α) :
    Weight.expectation (run p q (fixedWidth 1) 2 h)
      (fun result => (result.targetCalls : ℝ≥0∞)) =
        1 + rejectionMass (p h) (q h) := by
  have ho := congrArg (fun μ : Weight ℕ =>
    Weight.expectation μ (fun n => (n : ℝ≥0∞))) (two_token_targetCalls p q h)
  simp only [pushforward, Weight.expectation_bind, Weight.expectation_pure] at ho
  rw [ho]
  unfold Weight.expectation
  rw [ENNReal.tsum_prod']
  simp only [tsum_bool, Bool.false_eq_true, ↓reduceIte, Nat.cast_ofNat,
    Nat.cast_one, step_apply_true, step_apply_false, mul_one, ENNReal.tsum_mul_right]
  change rejectionMass (p h) (q h) * 2 + acceptanceMass (p h) (q h) = _
  calc
    _ = (acceptanceMass (p h) (q h) + rejectionMass (p h) (q h)) +
        rejectionMass (p h) (q h) := by ring
    _ = _ := by rw [acceptance_add_rejection]

end
end RelOL.Prob.Speculative
