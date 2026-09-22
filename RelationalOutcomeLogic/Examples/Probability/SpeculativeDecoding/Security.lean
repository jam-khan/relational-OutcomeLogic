import RelationalOutcomeLogic.Examples.Probability.SpeculativeDecoding.Counterexamples
import RelationalOutcomeLogic.Examples.Probability.SpeculativeDecoding.Buffered

/-!
# Preserved token distributions and leaking speculation observations

For an arbitrary target and any two draft models, unequal acceptance masses
produce different first-round token-count observations in the complete decoder,
while its full token distribution is unchanged. Strict gaps give quantitative
refutation certificates and failed pRelOL privacy judgments. The Boolean example
instantiates this general result. Full buffering then restores joint payload and
packet-count/size privacy for the stated observer; release times are excluded.
-/

namespace RelOL.Prob.Speculative

open scoped ENNReal

noncomputable section

variable {α : Type*}

theorem step_flag_true (p q : Distribution α) :
    pushforward Prod.fst (step p q) true = acceptanceMass p q := by
  simp only [pushforward_fst, margL, step_apply_true, acceptanceMass, Weight.mass]

theorem step_flag_false (p q : Distribution α) :
    pushforward Prod.fst (step p q) false = rejectionMass p q := by
  simp only [pushforward_fst, margL, step_apply_false, rejectionMass, Weight.mass]

/-- A one-proposal round emits two tokens on acceptance (including its bonus),
and one corrected token on rejection, when at least two output slots remain. -/
def oneDraftPacketSize (accepted : Bool) : ℕ := if accepted then 2 else 1


/-- Token count of the first streamed verification round; zero only for an empty trace. -/
def firstRoundSize (result : Run α) : ℕ :=
  match result.rounds with
  | [] => 0
  | trace :: _ => trace.emitted

theorem firstRoundSize_prepend (trace : RoundTrace) (μ : Weight (Run α))
    (hμ : Weight.IsProbability μ) :
    pushforward firstRoundSize (pushforward (Run.prepend trace) μ) =
      Weight.pure trace.emitted := by
  change Weight.bind (pushforward (Run.prepend trace) μ)
    (fun result => Weight.pure (firstRoundSize result)) = _
  rw [bind_pushforward]
  change Weight.bind μ (fun _ => Weight.pure trace.emitted) = _
  exact Weight.bind_const_of_isProbability μ hμ _

/-- The packet observation is obtained from the actual complete buffered decoder,
including its bonus draw or its second round after rejection. -/
theorem two_token_firstRoundSize (p q : Model α) (h : List α) :
    pushforward firstRoundSize (run p q (fixedWidth 1) 2 h) =
      pushforward (fun v : Bool × α => oneDraftPacketSize v.1) (step (p h) (q h)) := by
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
    rw [firstRoundSize_prepend _ _ (decode_isProbability p q _ 1 1 le_rfl _)]
    rfl
  · simp only [if_true]
    rw [pushforward_bind]
    simp only [decode, pushforward_pure, firstRoundSize, Run.prepend,
      RoundTrace.emitted, Bool.false_eq_true, if_false, if_true, Nat.add_zero]
    exact Weight.bind_const_of_isProbability _ (p _).normalized _

/-- The acceptance mass is exactly the probability that the actual complete
two-token run emits two tokens in its first streamed round. -/
theorem two_token_firstRoundSize_mass (p q : Model α) (h : List α) :
    Weight.eventMass (pushforward firstRoundSize (run p q (fixedWidth 1) 2 h)) {2} =
      acceptanceMass (p h) (q h) := by
  classical
  rw [two_token_firstRoundSize, Weight.eventMass_singleton]
  simp only [pushforward, Weight.bind, Weight.pure]
  rw [ENNReal.tsum_prod']
  simp [oneDraftPacketSize, step_apply_true, acceptanceMass, Weight.mass]

/-- Any strict gap between draft acceptance masses yields a quantitative
certificate against the complete decoders' first-round observations. -/
def acceptanceGapPacketLeak (p q₀ q₁ : Model α) (h : List α)
    (hgap : acceptanceMass (p h) (q₁ h) < acceptanceMass (p h) (q₀ h)) :
    MassDeficitCert Eq (pushforward firstRoundSize (run p q₀ (fixedWidth 1) 2 h))
      (pushforward firstRoundSize (run p q₁ (fixedWidth 1) 2 h)) where
  left := {2}
  right := {2}
  cover := by
    intro a ha b hab
    simpa only [← hab] using ha
  deficit := by
    rw [two_token_firstRoundSize_mass, two_token_firstRoundSize_mass]
    exact hgap

theorem acceptance_gap_refutes_packet_privacy (p q₀ q₁ : Model α) (h : List α)
    (hgap : acceptanceMass (p h) (q₁ h) < acceptanceMass (p h) (q₀ h)) :
    ¬ Coupled Eq (pushforward firstRoundSize (run p q₀ (fixedWidth 1) 2 h))
      (pushforward firstRoundSize (run p q₁ (fixedWidth 1) 2 h)) :=
  (acceptanceGapPacketLeak p q₀ q₁ h hgap).refutes

/-- Either orientation of a nonzero acceptance gap refutes observational equality. -/
theorem unequal_acceptance_refutes_packet_privacy (p q₀ q₁ : Model α) (h : List α)
    (hne : acceptanceMass (p h) (q₀ h) ≠ acceptanceMass (p h) (q₁ h)) :
    ¬ Coupled Eq (pushforward firstRoundSize (run p q₀ (fixedWidth 1) 2 h))
      (pushforward firstRoundSize (run p q₁ (fixedWidth 1) 2 h)) := by
  intro hc
  have he := congrArg (fun μ : Weight ℕ => Weight.eventMass μ {2})
    (coupled_eq_iff.mp hc)
  rw [two_token_firstRoundSize_mass, two_token_firstRoundSize_mass] at he
  exact hne he

/-- Arbitrary draft models and adaptive width policies preserve the same complete
token distribution; this holds even when their round observations differ. -/
theorem run_payload_private (p q₀ q₁ : Model α)
    (width₀ width₁ : List α → ℕ → ℕ) (n : ℕ) (h : List α) :
    Coupled Eq (pushforward Run.tokens (run p q₀ width₀ n h))
      (pushforward Run.tokens (run p q₁ width₁ n h)) := by
  apply coupled_eq_iff.mpr
  rw [run_output, run_output]

def twoTokenSampler (p q : Model α) (h : List α) (μ : Weight Unit) : Weight (Run α) :=
  Weight.bind μ (fun _ => run p q (fixedWidth 1) 2 h)

/-- A generic acceptance-gap witness attached to executions from explicit inputs. -/
def acceptanceGapPacketBug (p q₀ q₁ : Model α) (h : List α)
    (hgap : acceptanceMass (p h) (q₁ h) < acceptanceMass (p h) (q₀ h)) :
    BugCert (fun μ => pushforward firstRoundSize (twoTokenSampler p q₀ h μ))
      (fun μ => pushforward firstRoundSize (twoTokenSampler p q₁ h μ)) Eq where
  s₀ := ()
  s₀' := ()
  deficit := by
    simpa only [twoTokenSampler, Weight.pure_bind] using
      acceptanceGapPacketLeak p q₀ q₁ h hgap

theorem acceptance_gap_contract_refuted (p q₀ q₁ : Model α) (h : List α)
    (hgap : acceptanceMass (p h) (q₁ h) < acceptanceMass (p h) (q₀ h)) :
    ¬ quadSem (twoTokenSampler p q₀ h) (twoTokenSampler p q₁ h)
      (exactly (Weight.pure ()) (Weight.pure ()))
      (fun μ ν => Coupled Eq (pushforward firstRoundSize μ)
        (pushforward firstRoundSize ν)) :=
  (acceptanceGapPacketBug p q₀ q₁ h hgap).refutes_of_observation
    (exactly_self _ _) (fun _ _ h => h)

/-- A secret chooses a perfect or always-true proposal; the public target stays fair. -/
def secretDraft (secret : Bool) : Distribution Bool :=
  if secret then alwaysTrueDraft else fairTarget

def secretStep (secret : Bool) : Weight (Bool × Bool) :=
  step fairTarget (secretDraft secret)

/-- Every secret gives the same emitted-token law. -/
theorem secretStep_output (secret : Bool) :
    pushforward Prod.snd (secretStep secret) = fairTarget.weight :=
  step_output _ _

theorem secretStep_payload_private (s t : Bool) :
    Coupled Eq (pushforward Prod.snd (secretStep s))
      (pushforward Prod.snd (secretStep t)) := by
  apply coupled_eq_iff.mpr
  rw [secretStep_output, secretStep_output]

theorem secretStep_flag_false_secret :
    pushforward Prod.fst (secretStep false) = Weight.pure true := by
  funext b
  cases b <;>
    simp only [secretStep, secretDraft, Bool.false_eq_true, if_false,
      step_flag_false, step_flag_true] <;>
    norm_num [acceptanceMass, rejectionMass, Weight.mass, tsum_bool, residual, overlap,
      Weight.pure]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

theorem secretStep_flag_true_secret :
    pushforward Prod.fst (secretStep true) = fairTarget.weight := by
  funext b
  cases b <;>
    simp only [secretStep, secretDraft, if_true, step_flag_false, step_flag_true,
      rejectionMass_fair_true] <;>
    norm_num [acceptanceMass, Weight.mass, tsum_bool, overlap, alwaysTrueDraft, Weight.pure]

/-- Acceptance has mass one with a perfect draft and one half with the point draft. -/
def acceptanceLeak :
    MassDeficitCert Eq (pushforward Prod.fst (secretStep false))
      (pushforward Prod.fst (secretStep true)) where
  left := {true}
  right := {true}
  cover := by
    intro a ha b hab
    simpa only [← hab] using ha
  deficit := by
    rw [secretStep_flag_false_secret, secretStep_flag_true_secret]
    norm_num [Weight.eventMass, Weight.pure]

theorem secretStep_flag_not_private :
    ¬ Coupled Eq (pushforward Prod.fst (secretStep false))
      (pushforward Prod.fst (secretStep true)) :=
  acceptanceLeak.refutes


def oneDraftPacketObservation (secret : Bool) : Weight ℕ :=
  pushforward oneDraftPacketSize (pushforward Prod.fst (secretStep secret))

/-- The same deficit remains visible after replacing the flag by the round's token count. -/
def packetSizeLeak :
    MassDeficitCert Eq (oneDraftPacketObservation false) (oneDraftPacketObservation true) where
  left := {2}
  right := {2}
  cover := by
    intro a ha b hab
    simpa only [← hab] using ha
  deficit := by
    simp only [oneDraftPacketObservation, secretStep_flag_false_secret,
      secretStep_flag_true_secret, Weight.eventMass, Finset.sum_singleton]
    norm_num [pushforward, Weight.bind, tsum_bool, Weight.pure, oneDraftPacketSize]

def secretSampler (secret : Bool) (μ : Weight Unit) : Weight (Bool × Bool) :=
  Weight.bind μ (fun _ => secretStep secret)

/-- The observer failure is attached to executions from explicit initial inputs. -/
def acceptanceLeakBug :
    BugCert (fun μ => pushforward Prod.fst (secretSampler false μ))
      (fun μ => pushforward Prod.fst (secretSampler true μ)) Eq where
  s₀ := ()
  s₀' := ()
  deficit := by
    simpa only [secretSampler, Weight.pure_bind] using acceptanceLeak

theorem acceptance_privacy_contract_refuted :
    ¬ quadSem (secretSampler false) (secretSampler true)
      (exactly (Weight.pure ()) (Weight.pure ()))
      (fun μ ν => Coupled Eq (pushforward Prod.fst μ) (pushforward Prod.fst ν)) := by
  exact acceptanceLeakBug.refutes_of_observation (exactly_self _ _)
    (fun _ _ h => h)

/-- Two complete decoders differing only in a secret draft choice. -/
def secretRun (secret : Bool) : Weight (Run Bool) :=
  run (fun _ => fairTarget) (fun _ => secretDraft secret) (fixedWidth 1) 2 []

theorem secretRun_firstRoundSize (secret : Bool) :
    pushforward firstRoundSize (secretRun secret) = oneDraftPacketObservation secret := by
  rw [secretRun, two_token_firstRoundSize]
  simp only [oneDraftPacketObservation, secretStep, pushforward, Weight.bind_assoc,
    Weight.pure_bind]

/-- The concrete Boolean example instantiates the arbitrary-model gap theorem. -/
theorem secretDraft_acceptance_gap :
    acceptanceMass fairTarget (secretDraft true) <
      acceptanceMass fairTarget (secretDraft false) := by
  simp only [secretDraft, Bool.false_eq_true, if_false, if_true, acceptanceMass_self]
  norm_num [acceptanceMass, Weight.mass, tsum_bool, overlap, alwaysTrueDraft, Weight.pure]

/-- The full-run observer deficit is an instance of the general acceptance-gap certificate. -/
def fullRunPacketLeak :
    MassDeficitCert Eq (pushforward firstRoundSize (secretRun false))
      (pushforward firstRoundSize (secretRun true)) :=
  acceptanceGapPacketLeak (fun _ => fairTarget) (fun _ => secretDraft false)
    (fun _ => secretDraft true) [] secretDraft_acceptance_gap

theorem secretRun_packet_not_private :
    ¬ Coupled Eq (pushforward firstRoundSize (secretRun false))
      (pushforward firstRoundSize (secretRun true)) := fullRunPacketLeak.refutes

theorem secretRun_payload_private :
    Coupled Eq (pushforward Run.tokens (secretRun false))
      (pushforward Run.tokens (secretRun true)) := by
  exact run_payload_private (fun _ => fairTarget) (fun _ => secretDraft false)
    (fun _ => secretDraft true) (fixedWidth 1) (fixedWidth 1) 2 []

def secretRunSampler (secret : Bool) (μ : Weight Unit) : Weight (Run Bool) :=
  Weight.bind μ (fun _ => secretRun secret)

def fullRunPacketLeakBug :
    BugCert (fun μ => pushforward firstRoundSize (secretRunSampler false μ))
      (fun μ => pushforward firstRoundSize (secretRunSampler true μ)) Eq where
  s₀ := ()
  s₀' := ()
  deficit := by
    simpa only [secretRunSampler, Weight.pure_bind] using fullRunPacketLeak

/-- The actual complete-run privacy judgment is refuted from valid unit inputs. -/
theorem fullRun_packet_contract_refuted :
    ¬ quadSem (secretRunSampler false) (secretRunSampler true)
      (exactly (Weight.pure ()) (Weight.pure ()))
      (fun μ ν => Coupled Eq (pushforward firstRoundSize μ)
        (pushforward firstRoundSize ν)) :=
  fullRunPacketLeakBug.refutes_of_observation (exactly_self _ _) (fun _ _ h => h)

theorem fullRun_payload_contract :
    quadSem (secretRunSampler false) (secretRunSampler true)
      (exactly (Weight.pure ()) (Weight.pure ()))
      (fun μ ν => Coupled Eq (pushforward Run.tokens μ) (pushforward Run.tokens ν)) := by
  rintro μ ν ⟨rfl, rfl⟩
  simpa only [secretRunSampler, Weight.pure_bind] using secretRun_payload_private

/-- Buffer the complete payload and send one packet whose size is its actual token
count. This packet model records sizes and counts, but deliberately not release times. -/
def bufferedPacket (result : Run α) : List α × List ℕ :=
  (result.tokens, [result.tokens.length])

def bufferedRelease (μ : Weight (Run α)) : Weight (List α × List ℕ) :=
  pushforward bufferedPacket μ

/-- Buffering retains exactly the same token payload, for arbitrary input weights. -/
theorem bufferedRelease_payload (μ : Weight (Run α)) :
    pushforward Prod.fst (bufferedRelease μ) = pushforward Run.tokens μ := by
  simp only [bufferedRelease, pushforward, Weight.bind_assoc,
    Weight.pure_bind]
  rfl

/-- Actual packet sizes become a fixed observation because the complete run has
a fixed public output budget. Neither timing nor intermediate packets are exposed. -/
theorem bufferedRelease_packet_observation (p q : Model α)
    (width : List α → ℕ → ℕ) (n : ℕ) (h : List α) :
    pushforward Prod.snd (bufferedRelease (run p q width n h)) =
      Weight.pure [h.length + n] := by
  change Weight.bind (pushforward bufferedPacket (run p q width n h))
    (fun packet => Weight.pure packet.2) = _
  rw [bind_pushforward]
  have hc : Weight.bind (run p q width n h)
      (fun result => Weight.pure (bufferedPacket result).2) =
      Weight.bind (run p q width n h) (fun _ => Weight.pure [h.length + n]) := by
    apply Weight.bind_congr_on_support
    intro result hr
    dsimp [bufferedPacket]
    rw [decode_length p q width n n le_rfl h result hr]
  rw [hc]
  exact Weight.bind_const_of_isProbability _ (run_isProbability p q width n h) _

theorem bufferedRelease_correct (p q : Model α) (width : List α → ℕ → ℕ)
    (n : ℕ) (h : List α) :
    pushforward Prod.fst (bufferedRelease (run p q width n h)) =
      autoregressive p n h := by
  rw [bufferedRelease_payload, run_output]

/-- The whole released packet, including its payload and size, is determined by
ordinary autoregressive decoding. This also excludes hidden payload/size correlations. -/
theorem bufferedRelease_law (p q : Model α) (width : List α → ℕ → ℕ)
    (n : ℕ) (h : List α) :
    bufferedRelease (run p q width n h) =
      pushforward (fun out : List α => (out, [out.length])) (autoregressive p n h) := by
  rw [← run_output p q width n h]
  simp only [bufferedRelease, pushforward, Weight.bind_assoc, Weight.pure_bind]
  rfl

theorem bufferedRelease_private (p : Model α) (q₀ q₁ : Model α)
    (width₀ width₁ : List α → ℕ → ℕ) (n : ℕ) (h : List α) :
    Coupled Eq (bufferedRelease (run p q₀ width₀ n h))
      (bufferedRelease (run p q₁ width₁ n h)) := by
  apply coupled_eq_iff.mpr
  rw [bufferedRelease_law, bufferedRelease_law]

/-- For a fixed public history and budget, different secret draft models and
width policies have identical packet-size/count observations after full buffering. -/
theorem bufferedRelease_packet_private (p : Model α) (q₀ q₁ : Model α)
    (width₀ width₁ : List α → ℕ → ℕ) (n : ℕ) (h : List α) :
    Coupled Eq
      (pushforward Prod.snd (bufferedRelease (run p q₀ width₀ n h)))
      (pushforward Prod.snd (bufferedRelease (run p q₁ width₁ n h))) := by
  apply coupled_eq_iff.mpr
  rw [bufferedRelease_packet_observation, bufferedRelease_packet_observation]

end

end RelOL.Prob.Speculative
